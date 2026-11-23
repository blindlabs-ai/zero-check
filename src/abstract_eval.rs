use std::collections::{BTreeMap, BTreeSet};

pub type NodeId = usize;
pub type IrOp = Op<NodeId>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArchProfile { X86_64Avx2, Aarch64Neon }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegBudget { pub max_gprs: usize, pub max_vecs: usize, pub simd_bits: usize, pub lanes_i64: usize }
impl ArchProfile {
    #[must_use] pub const fn budget(self) -> RegBudget {
        match self {
            Self::X86_64Avx2 => RegBudget { max_gprs: 14, max_vecs: 16, simd_bits: 256, lanes_i64: 4 },
            Self::Aarch64Neon => RegBudget { max_gprs: 28, max_vecs: 32, simd_bits: 128, lanes_i64: 2 },
        }
    }
    #[must_use] pub const fn name(self) -> &'static str { match self { Self::X86_64Avx2 => "x86_64-avx2", Self::Aarch64Neon => "aarch64-neon" } }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CmpKind { Eq, Ne, Lt, Le, Gt, Ge }
impl CmpKind {
    #[must_use] pub const fn negate(self) -> Self { [Self::Ne, Self::Eq, Self::Ge, Self::Gt, Self::Le, Self::Lt][(self as usize) % 6] }
    #[must_use] pub const fn flip(self) -> Self { match self { Self::Lt => Self::Gt, Self::Gt => Self::Lt, Self::Le => Self::Ge, Self::Ge => Self::Le, x => x } }
    #[must_use] pub const fn eval(self, a: i64, b: i64) -> bool {
        match self { Self::Eq => a == b, Self::Ne => a != b, Self::Lt => a < b, Self::Le => a <= b, Self::Gt => a > b, Self::Ge => a >= b }
    }
}

/// Generation-tagged ASan-class shadow-epoch allocation state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocState { pub len: usize, pub alive: bool, pub init_mask: u64, pub generation: u32, pub all_init: bool }
impl AllocState {
    #[must_use] pub const fn full_mask(len: usize) -> u64 { if len >= 64 { u64::MAX } else if len == 0 { 0 } else { (1u64 << len) - 1 } }
    #[must_use] pub const fn from_buf(buf: &BufSpec) -> Self {
        Self { len: buf.len, alive: true, init_mask: if buf.pre_init { Self::full_mask(buf.len) } else { 0 }, generation: 1, all_init: buf.pre_init }
    }
    #[must_use] pub const fn is_slot_init(self, idx: usize) -> bool { if self.all_init { true } else if idx < 64 { ((self.init_mask >> idx) & 1) != 0 } else { false } }
    pub fn mark_init(&mut self, idx: usize) { if idx < 64 { self.init_mask |= 1u64 << idx; } }
    pub fn alloc(&mut self, len: usize) -> u32 {
        self.len = len; self.alive = true; self.init_mask = 0; self.all_init = false;
        self.generation = self.generation.wrapping_add(1); self.generation
    }
    pub fn free(&mut self) -> Result<u32, u32> {
        if !self.alive { return Err(self.generation); }
        self.alive = false; self.init_mask = 0; self.all_init = false;
        self.generation = self.generation.wrapping_add(1); Ok(self.generation)
    }
}

crate::define_errors!(pub VerifyError {
    InvalidBuffer(b: u8) => ("invalid buffer {b}"),
    InvalidParam(p: u8) => ("invalid param {p}"),
    InvalidNode(n: NodeId) => ("invalid node {n}"),
    WriteToReadOnly { buf: u8 } => ("write to read-only buffer {buf}"),
    NoAliasViolation { buf_a: u8, buf_b: u8, region: u16 } => ("noalias overlap: bufs {buf_a},{buf_b} in region {region}"),
    UseAfterFree { node: NodeId, buf: u8, generation: u32 } => ("node {node}: use-after-free on buf {buf} (gen {generation})"),
    DoubleFree { node: NodeId, buf: u8, generation: u32 } => ("node {node}: double-free on buf {buf} (gen {generation})"),
    UninitializedRead { node: NodeId, buf: u8, idx_lo: i64, idx_hi: i64 } => ("node {node}: uninitialized read on buf {buf} idx [{idx_lo},{idx_hi}]"),
    OutOfBounds { node: NodeId, idx_lo: i64, idx_hi: i64, limit: usize } => ("node {node}: idx [{idx_lo},{idx_hi}] outside 0..{limit}"),
    IntOverflow { node: NodeId } => ("node {node}: signed i64 overflow"),
    ShiftOverflow { node: NodeId, lo: i64, hi: i64 } => ("node {node}: shift [{lo},{hi}] outside 0..64"),
    DivByZero { node: NodeId } => ("node {node}: div/rem by zero or i64::MIN / -1"),
    RegisterSpill { profile: ArchProfile, peak_gprs: usize, max_gprs: usize, peak_vecs: usize, max_vecs: usize } => ("register spill on {}: gprs {peak_gprs}/{max_gprs}, vecs {peak_vecs}/{max_vecs}", profile.name()),
    CounterexampleFound { node: NodeId, fault: u8, inputs: Vec<i64> } => ("counterexample node {node} fault 0x{fault:02x}: {inputs:?}"),
    LintViolations { count: usize } => ("static Rust linter found {count} error(s)"),
    Ntf1Violation(msg: String) => ("ntf1 violation: {msg}"),
    Io(msg: String) => ("io error: {msg}"),
});

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Domain { pub lo: i64, pub hi: i64, pub modulus: i64, pub rem: i64 }

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.saturating_abs(); b = b.saturating_abs();
    while b != 0 { let t = a % b; a = b; b = t; }
    if a == 0 { 1 } else { a }
}
fn gcd_i64(a: i64, b: i64) -> i64 { let g = gcd_i128(i128::from(a), i128::from(b)); if g > i128::from(i64::MAX) { 1 } else { g as i64 } }

impl Domain {
    #[must_use] pub const fn top() -> Self { Self { lo: i64::MIN, hi: i64::MAX, modulus: 1, rem: 0 } }
    #[must_use] pub const fn range(lo: i64, hi: i64) -> Self { if lo <= hi { Self { lo, hi, modulus: 1, rem: 0 } } else { Self::top() } }
    #[must_use] pub const fn exact(v: i64) -> Self { Self { lo: v, hi: v, modulus: 1, rem: 0 } }
    #[must_use] pub fn congruent(lo: i64, hi: i64, modulus: i64, rem: i64) -> Self {
        if lo > hi { return Self::top(); } else if lo == hi { return Self::exact(lo); }
        let m = if modulus > 1 { modulus } else { 1 };
        let d = Self { lo, hi, modulus: m, rem: rem.rem_euclid(m) }; d.tighten().unwrap_or(d)
    }
    #[must_use] pub const fn is_const(self) -> Option<i64> {
        if self.lo != self.hi || self.modulus < 1 || self.rem < 0 || self.rem >= self.modulus { return None; }
        if self.modulus == 1 { return Some(self.lo); }
        let r = self.lo % self.modulus;
        if (if r < 0 { r + self.modulus } else { r }) == self.rem { Some(self.lo) } else { None }
    }
    #[must_use] pub const fn is_nonneg(self) -> bool { self.lo >= 0 }
    #[must_use] pub fn contains(self, v: i64) -> bool { v >= self.lo && v <= self.hi && (self.modulus <= 1 || v.rem_euclid(self.modulus) == self.rem) }
    #[must_use] pub fn width_u128(self) -> u128 { (i128::from(self.hi) - i128::from(self.lo)) as u128 }
    #[must_use] pub fn tighten(self) -> Option<Self> {
        if self.lo > self.hi || self.modulus < 1 || self.rem < 0 || self.rem >= self.modulus { return None; }
        if self.modulus == 1 { return Some(self); }
        let (m, r, lo128, hi128) = (i128::from(self.modulus), i128::from(self.rem), i128::from(self.lo), i128::from(self.hi));
        let (nlo, nhi) = (lo128 + (r - lo128.rem_euclid(m)).rem_euclid(m), hi128 - (hi128.rem_euclid(m) - r).rem_euclid(m));
        if nlo > nhi || nlo < i128::from(i64::MIN) || nhi > i128::from(i64::MAX) { None }
        else if nlo == nhi { Some(Self::exact(nlo as i64)) }
        else { Some(Self { lo: nlo as i64, hi: nhi as i64, modulus: self.modulus, rem: self.rem }) }
    }
    #[must_use] pub fn split_mid(self) -> Option<(Self, Self)> {
        let d = self.tighten()?; if d.lo >= d.hi { return None; }
        let mid = d.lo.wrapping_add(((i128::from(d.hi) - i128::from(d.lo)) / 2) as i64);
        Some((Self { hi: mid, ..d }.tighten()?, Self { lo: mid.wrapping_add(1), ..d }.tighten()?))
    }
    #[must_use] pub fn split_mod2(self) -> Option<(Self, Self)> {
        let d = self.tighten()?; if d.lo >= d.hi || d.modulus > i64::MAX / 4 { return None; }
        let m2 = d.modulus * 2;
        Some((Self { modulus: m2, rem: d.rem, ..d }.tighten()?, Self { modulus: m2, rem: d.rem + d.modulus, ..d }.tighten()?))
    }
    #[must_use] pub fn rem_mod(self, d: i64) -> Option<i64> {
        if d <= 0 { None } else if let Some(c) = self.is_const() { Some(c.rem_euclid(d)) }
        else if self.modulus > 1 && self.modulus % d == 0 { Some(self.rem.rem_euclid(d)) } else { None }
    }
    #[must_use] pub fn try_meet(self, other: Self) -> Option<Self> {
        let (lo, hi) = (self.lo.max(other.lo), self.hi.min(other.hi));
        if lo > hi || (self.modulus > 1 && other.modulus > 1 && self.modulus == other.modulus && self.rem != other.rem) { return None; }
        let (modulus, rem) = if other.modulus > self.modulus { (other.modulus, other.rem) } else { (self.modulus, self.rem) };
        Self { lo, hi, modulus, rem }.tighten()
    }
    #[must_use] pub fn meet(self, other: Self) -> Self { self.try_meet(other).unwrap_or(self) }
    #[must_use] pub fn join(self, other: Self) -> Self {
        if self == other { return self; }
        let (lo, hi) = (self.lo.min(other.lo), self.hi.max(other.hi));
        if lo == hi { return Self::exact(lo); }
        let (m1, r1) = self.is_const().map_or((i128::from(self.modulus), i128::from(self.rem)), |c| (0, i128::from(c)));
        let (m2, r2) = other.is_const().map_or((i128::from(other.modulus), i128::from(other.rem)), |c| (0, i128::from(c)));
        let g1 = if m1 == 0 { m2 } else if m2 == 0 { m1 } else { gcd_i128(m1, m2) };
        let diff = (r1 - r2).abs();
        let g = if g1 == 0 { diff } else if diff == 0 { g1 } else { gcd_i128(g1, diff) };
        let m = if g > 1 && g <= i128::from(i64::MAX / 2) { g as i64 } else { 1 };
        Self::congruent(lo, hi, m, r1.rem_euclid(i128::from(m)) as i64)
    }
    fn from_i128(lo: i128, hi: i128, modulus: i64, rem: i64) -> (Self, bool) {
        if lo >= i128::from(i64::MIN) && hi <= i128::from(i64::MAX) && lo <= hi { (Self::congruent(lo as i64, hi as i64, modulus, rem), false) } else { (Self::top(), true) }
    }
    #[must_use] pub fn eval_add_sub(self, rhs: Self, is_sub: bool) -> (Self, bool) {
        let (g, ra, rb) = match (self.is_const(), rhs.is_const()) {
            (Some(a), Some(b)) => (1i64, i128::from(a), i128::from(b)),
            (None, Some(b)) => (self.modulus, i128::from(self.rem), i128::from(b)),
            (Some(a), None) => (rhs.modulus, i128::from(a), i128::from(rhs.rem)),
            (None, None) => (gcd_i64(self.modulus, rhs.modulus), i128::from(self.rem), i128::from(rhs.rem)),
        };
        let (g128, (a0, a1, b0, b1)) = (i128::from(g), (i128::from(self.lo), i128::from(self.hi), i128::from(rhs.lo), i128::from(rhs.hi)));
        if is_sub { Self::from_i128(a0 - b1, a1 - b0, g, (ra - rb).rem_euclid(g128) as i64) }
        else { Self::from_i128(a0 + b0, a1 + b1, g, (ra + rb).rem_euclid(g128) as i64) }
    }
    #[must_use] pub fn eval_square(self) -> (Self, bool) {
        let (a0, a1) = (i128::from(self.lo), i128::from(self.hi));
        let (p0, p1) = (a0 * a0, a1 * a1);
        let lo = if self.lo <= 0 && self.hi >= 0 {
            if self.contains(0) { 0 } else { let pos = i128::from(self.rem); let neg = pos - i128::from(self.modulus); (pos * pos).min(neg * neg) }
        } else { p0.min(p1) };
        let (m, r) = if self.modulus > 1 {
            let (m128, r128) = (i128::from(self.modulus), i128::from(self.rem));
            let lifted = m128.saturating_mul(gcd_i128(m128 + 2 * r128, 2 * m128));
            let mm = if lifted <= i128::from(i64::MAX / 2) { lifted } else { m128 };
            (mm as i64, (r128 * r128).rem_euclid(mm) as i64)
        } else { (1, 0) };
        Self::from_i128(lo, p0.max(p1), m, r)
    }
    #[must_use] pub fn eval_mul(self, rhs: Self) -> (Self, bool) {
        if self.is_const() == Some(0) || rhs.is_const() == Some(0) { return (Self::exact(0), false); }
        let (a0, a1, b0, b1) = (i128::from(self.lo), i128::from(self.hi), i128::from(rhs.lo), i128::from(rhs.hi));
        let p = [a0 * b0, a0 * b1, a1 * b0, a1 * b1];
        let (lo, hi, cap) = (p.into_iter().min().unwrap_or(i128::from(i64::MIN)), p.into_iter().max().unwrap_or(i128::from(i64::MAX)), i128::from(i64::MAX / 2));
        let scale = |dm: i64, dr: i64, c: i64| {
            let mm = i128::from(dm).saturating_mul(i128::from(c).abs());
            if mm > 1 && mm <= cap { (mm as i64, (i128::from(dr) * i128::from(c)).rem_euclid(mm) as i64) } else { (1, 0) }
        };
        let (m, rem) = if let Some(c) = rhs.is_const() { scale(self.modulus, self.rem, c) }
        else if let Some(c) = self.is_const() { scale(rhs.modulus, rhs.rem, c) }
        else {
            let (ma, ra, mb, rb) = (i128::from(self.modulus), i128::from(self.rem), i128::from(rhs.modulus), i128::from(rhs.rem));
            let mm = gcd_i128(gcd_i128(ma.saturating_mul(mb), ma.saturating_mul(rb)), mb.saturating_mul(ra));
            if mm > 1 && mm <= cap { (mm as i64, (ra * rb).rem_euclid(mm) as i64) } else { (1, 0) }
        };
        Self::from_i128(lo, hi, m, rem)
    }
    #[must_use] pub fn eval_div_rem(self, rhs_raw: Self, is_rem: bool) -> (Self, bool) {
        let Some(rhs) = rhs_raw.tighten() else { return (Self::top(), true); };
        if rhs.contains(0) || (self.lo == i64::MIN && rhs.contains(-1)) { return (Self::top(), true); }
        if let (Some(a), Some(b)) = (self.is_const(), rhs.is_const()) { return (Self::exact(if is_rem { a % b } else { a / b }), false); }
        if !is_rem {
            let (mut lo, mut hi) = (i64::MAX, i64::MIN);
            for d in [rhs.lo, rhs.hi, rhs.rem, rhs.rem - rhs.modulus] {
                if d != 0 && d >= rhs.lo && d <= rhs.hi { for a in [self.lo, self.hi] { lo = lo.min(a / d); hi = hi.max(a / d); } }
            }
            return (Self::range(lo, hi), false);
        }
        if let Some(d) = rhs.is_const().filter(|&d| d > 0) {
            if !self.is_nonneg() { return (Self::range(-(d - 1), d - 1), false); }
            if self.hi < d { return (self, false); }
            let g = gcd_i64(self.modulus, d);
            return if g > 1 { let r0 = self.rem.rem_euclid(g); (Self::congruent(r0, r0 + ((d - 1 - r0) / g) * g, g, r0), false) } else { (Self::range(0, d - 1), false) };
        }
        let lim = (i128::from(rhs.lo).abs().max(i128::from(rhs.hi).abs()) - 1).min(i128::from(i64::MAX)) as i64;
        (Self::range(if self.is_nonneg() { 0 } else { -lim }, lim), false)
    }
    #[must_use] pub fn eval_shl(self, s: u8) -> (Self, bool) {
        if s >= 64 { (Self::top(), true) } else if s == 63 { (Self::top(), false) }
        else { (Self::from_i128(i128::from(self.lo) << s, i128::from(self.hi) << s, if s > 0 && s < 62 { 1i64 << s } else { 1 }, 0).0, false) }
    }
    #[must_use] pub fn eval_shr(self, s: u8) -> (Self, bool) { if s >= 64 { (Self::top(), true) } else { (Self::range(self.lo >> s, self.hi >> s), false) } }
    #[must_use] pub fn eval_bit(self, rhs: Self, kind: u8) -> Self {
        if let (Some(a), Some(b)) = (self.is_const(), rhs.is_const()) { return Self::exact(match kind { 0 => a & b, 1 => a | b, _ => a ^ b }); }
        if kind == 0 { return match (self.is_nonneg(), rhs.is_nonneg()) { (true, true) => Self::range(0, self.hi.min(rhs.hi)), (false, true) => Self::range(0, rhs.hi), (true, false) => Self::range(0, self.hi), _ => Self::top() }; }
        if self.is_nonneg() && rhs.is_nonneg() {
            let mv = self.hi.max(rhs.hi) as u64;
            return Self::range(0, if mv == 0 { 0 } else { ((1u64 << (64 - mv.leading_zeros()).min(63)) - 1) as i64 });
        }
        Self::top()
    }
    #[must_use] pub fn eval_cmp(self, kind: CmpKind, rhs: Self) -> Self {
        if let (Some(a), Some(b)) = (self.is_const(), rhs.is_const()) { return Self::exact(i64::from(kind.eval(a, b))); }
        match kind {
            CmpKind::Eq => self.try_meet(rhs).is_none().then_some(0),
            CmpKind::Ne => self.try_meet(rhs).is_none().then_some(1),
            CmpKind::Lt => if self.hi < rhs.lo { Some(1) } else if self.lo >= rhs.hi { Some(0) } else { None },
            CmpKind::Le => if self.hi <= rhs.lo { Some(1) } else if self.lo > rhs.hi { Some(0) } else { None },
            CmpKind::Gt => if self.lo > rhs.hi { Some(1) } else if self.hi <= rhs.lo { Some(0) } else { None },
            CmpKind::Ge => if self.lo >= rhs.hi { Some(1) } else if self.hi < rhs.lo { Some(0) } else { None },
        }.map_or(Self::range(0, 1), Self::exact)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BufSpec {
    pub id: u8, pub name: String, pub len: usize, pub mutable: bool,
    pub region: u16, pub offset: usize, pub elem_domain: Domain, pub pre_init: bool,
}

crate::define_ops!(
    @0 pure Param(u8), @0 pure Const(i64), @0s eff Alloc { buf: u8, len: usize }, @0 eff Free(u8),
    @1s eff CheckGen { buf: u8, expected: Id }, @1s eff Load { buf: u8, idx: Id },
    @2s eff Store { buf: u8, idx: Id, val: Id }, @1s pure BoundsCheck { idx: Id, limit: usize },
    @2 pure Add(Id, Id), @2 pure Sub(Id, Id), @2 pure Mul(Id, Id),
    @2 pure WrapAdd(Id, Id), @2 pure WrapSub(Id, Id), @2 pure WrapMul(Id, Id),
    @2 pure Div(Id, Id), @2 pure Rem(Id, Id), @1t pure Shl(Id, u8), @1t pure Shr(Id, u8),
    @2 pure ShlVar(Id, Id), @2 pure ShrVar(Id, Id), @2 pure BitAnd(Id, Id), @2 pure BitOr(Id, Id), @2 pure BitXor(Id, Id),
    @2k pure Cmp(CmpKind, Id, Id), @3s pure Select { cond: Id, t_val: Id, f_val: Id },
);

impl<Id: Copy> Op<Id> {
    pub fn eval_dom(self, dom: impl Fn(Id) -> Domain, pdom: impl Fn(u8) -> Domain, bdom: impl Fn(u8) -> Domain) -> Domain {
        match self {
            Self::Param(p) => pdom(p), Self::Const(c) => Domain::exact(c),
            Self::Alloc { .. } => Domain::range(1, i64::MAX), Self::Free(_) => Domain::exact(0),
            Self::CheckGen { expected, .. } => dom(expected), Self::Load { buf, .. } => bdom(buf), Self::Store { val, .. } => dom(val),
            Self::BoundsCheck { idx, limit } => if limit > 0 { dom(idx).meet(Domain::range(0, i64::try_from(limit - 1).unwrap_or(i64::MAX))) } else { Domain::top() },
            Self::Add(a, b) | Self::WrapAdd(a, b) => dom(a).eval_add_sub(dom(b), false).0,
            Self::Sub(a, b) | Self::WrapSub(a, b) => dom(a).eval_add_sub(dom(b), true).0,
            Self::Mul(a, b) | Self::WrapMul(a, b) => dom(a).eval_mul(dom(b)).0,
            Self::Div(a, b) => dom(a).eval_div_rem(dom(b), false).0, Self::Rem(a, b) => dom(a).eval_div_rem(dom(b), true).0,
            Self::Shl(a, s) => dom(a).eval_shl(s).0, Self::Shr(a, s) => dom(a).eval_shr(s).0,
            Self::ShlVar(a, b) => dom(b).is_const().filter(|&s| (0..64).contains(&s)).map_or(Domain::top(), |s| dom(a).eval_shl(s as u8).0),
            Self::ShrVar(a, b) => dom(b).is_const().filter(|&s| (0..64).contains(&s)).map_or(Domain::top(), |s| dom(a).eval_shr(s as u8).0),
            Self::BitAnd(a, b) => dom(a).eval_bit(dom(b), 0), Self::BitOr(a, b) => dom(a).eval_bit(dom(b), 1), Self::BitXor(a, b) => dom(a).eval_bit(dom(b), 2),
            Self::Cmp(k, a, b) => dom(a).eval_cmp(k, dom(b)),
            Self::Select { cond, t_val, f_val } => {
                let cd = dom(cond);
                if cd.is_const() == Some(0) { dom(f_val) } else if !cd.contains(0) { dom(t_val) } else { dom(t_val).join(dom(f_val)) }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub name: String, pub bufs: Vec<BufSpec>, pub param_domains: Vec<Domain>,
    pub nodes: Vec<IrOp>, pub node_guards: Vec<Option<(NodeId, bool)>>, pub outputs: Vec<NodeId>, pub simd_lanes: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofStatus { ProvenSafe, DefiniteBug(VerifyError), Uncertain(VerifyError) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScheduleReport { pub profile: ArchProfile, pub peak_gprs: usize, pub peak_vecs: usize, pub live_nodes: usize }
#[derive(Clone, Debug)]
pub struct AbstractReport { pub domains: Vec<Domain>, pub status: ProofStatus, pub schedule: ScheduleReport, pub checks_proven: usize }

fn uf_find(uf: &[usize], mut x: usize) -> usize { while uf[x] != x { x = uf[x]; } x }
fn uf_union(uf: &mut [usize], doms: &mut [Domain], a: usize, b: usize) {
    let (mut ra, mut rb) = (uf_find(uf, a), uf_find(uf, b));
    if ra == rb { return; }
    if ra > rb { std::mem::swap(&mut ra, &mut rb); }
    uf[rb] = ra; doms[ra] = doms[ra].meet(doms[rb]);
}
fn env_dom(env: &BTreeMap<usize, Domain>, base: &[Domain], uf: &[usize], id: NodeId) -> Domain {
    let r = uf_find(uf, id); env.get(&r).copied().unwrap_or(base[r])
}

#[derive(Clone, Copy)]
struct GuardCtx<'a> { prog: &'a Program, base: &'a [Domain], uf: &'a [usize] }
impl GuardCtx<'_> {
    fn get(self, env: &BTreeMap<usize, Domain>, id: NodeId) -> Domain { env_dom(env, self.base, self.uf, id) }
    fn tighten(self, env: &mut BTreeMap<usize, Domain>, id: NodeId, bound: Domain) -> Option<()> {
        let r = uf_find(self.uf, id);
        let next = self.get(env, r).try_meet(bound)?;
        env.insert(r, next);
        match self.prog.nodes[id] {
            Op::BoundsCheck { idx, .. } => self.tighten(env, idx, bound)?,
            Op::BitAnd(x, m_id) => if let (Some(m), Some(rv)) = (self.get(env, m_id).is_const(), next.is_const()) {
                if m > 0 && m < 64 && ((m + 1) & m) == 0 && rv >= 0 && rv <= m {
                    let dx = self.get(env, x); self.tighten(env, x, Domain::congruent(dx.lo, dx.hi, m + 1, rv))?;
                }
            },
            _ => {}
        }
        Some(())
    }
    fn merge_branch(self, env: &mut BTreeMap<usize, Domain>, r1: Option<BTreeMap<usize, Domain>>, r2: Option<BTreeMap<usize, Domain>>) -> Option<()> {
        *env = match (r1, r2) { (None, None) => return None, (Some(e), None) | (None, Some(e)) => e, (Some(a), Some(b)) => join_envs(self.base, a, b) };
        Some(())
    }
    fn apply(self, g: NodeId, pol: bool, env: &mut BTreeMap<usize, Domain>, depth: u8) -> Option<()> {
        if depth > 16 { return Some(()); }
        let dg = self.get(env, g);
        if (pol && dg.is_const() == Some(0)) || (!pol && !dg.contains(0)) { return None; }
        if !pol { self.tighten(env, g, Domain::exact(0))?; } else if dg == Domain::range(0, 1) { self.tighten(env, g, Domain::exact(1))?; }
        match self.prog.nodes[g] {
            Op::Cmp(k, a, b) => {
                let (eff, da, db) = (if pol { k } else { k.negate() }, self.get(env, a), self.get(env, b));
                match (eff, da.is_const(), db.is_const()) {
                    (CmpKind::Eq | CmpKind::Ne, _, Some(0)) => return self.apply(a, eff == CmpKind::Ne, env, depth + 1),
                    (CmpKind::Eq | CmpKind::Ne, Some(0), _) => return self.apply(b, eff == CmpKind::Ne, env, depth + 1),
                    _ => { self.tighten(env, a, cmp_bound(eff, da, db)?)?; self.tighten(env, b, cmp_bound(eff.flip(), db, da)?)?; }
                }
            }
            Op::BitAnd(a, b) if pol => { self.apply(a, true, env, depth + 1)?; self.apply(b, true, env, depth + 1)?; }
            Op::BitOr(a, b) if !pol => { self.apply(a, false, env, depth + 1)?; self.apply(b, false, env, depth + 1)?; }
            Op::Select { cond, t_val, f_val } => self.apply_select(cond, t_val, f_val, pol, env, depth + 1)?,
            Op::BitOr(a, b) | Op::BitAnd(a, b) => {
                let (mut e1, mut e2) = (env.clone(), env.clone());
                let (r1, r2) = (self.apply(a, pol, &mut e1, depth + 1).map(|()| e1), self.apply(b, pol, &mut e2, depth + 1).map(|()| e2));
                self.merge_branch(env, r1, r2)?;
            }
            _ => {}
        }
        Some(())
    }
    fn apply_select(self, cond: NodeId, t_val: NodeId, f_val: NodeId, pol: bool, env: &mut BTreeMap<usize, Domain>, depth: u8) -> Option<()> {
        let (dt, df) = (self.get(env, t_val), self.get(env, f_val));
        if (pol && df.is_const() == Some(0)) || (!pol && !df.contains(0)) { self.apply(cond, true, env, depth)?; self.apply(t_val, pol, env, depth)?; }
        else if (pol && dt.is_const() == Some(0)) || (!pol && !dt.contains(0)) { self.apply(cond, false, env, depth)?; self.apply(f_val, pol, env, depth)?; }
        else {
            let (mut e1, mut e2) = (env.clone(), env.clone());
            let r1 = self.apply(cond, true, &mut e1, depth).and_then(|()| self.apply(t_val, pol, &mut e1, depth)).map(|()| e1);
            let r2 = self.apply(cond, false, &mut e2, depth).and_then(|()| self.apply(f_val, pol, &mut e2, depth)).map(|()| e2);
            self.merge_branch(env, r1, r2)?;
        }
        Some(())
    }
}

fn cmp_bound(eff: CmpKind, lhs: Domain, rhs: Domain) -> Option<Domain> {
    match eff {
        CmpKind::Eq => Some(rhs),
        CmpKind::Ne => match rhs.is_const() {
            Some(k) if lhs.lo == k => k.checked_add(1).map(|lo| Domain::range(lo, i64::MAX)),
            Some(k) if lhs.hi == k => k.checked_sub(1).map(|hi| Domain::range(i64::MIN, hi)),
            _ => Some(Domain::top()),
        },
        CmpKind::Lt => rhs.hi.checked_sub(1).map(|hi| Domain::range(i64::MIN, hi)),
        CmpKind::Le => Some(Domain::range(i64::MIN, rhs.hi)),
        CmpKind::Gt => rhs.lo.checked_add(1).map(|lo| Domain::range(lo, i64::MAX)),
        CmpKind::Ge => Some(Domain::range(rhs.lo, i64::MAX)),
    }
}

fn join_envs(base: &[Domain], a: BTreeMap<usize, Domain>, b: BTreeMap<usize, Domain>) -> BTreeMap<usize, Domain> {
    let mut out = BTreeMap::new();
    for (&k, &da) in &a { out.insert(k, da.join(b.get(&k).copied().unwrap_or(base[k]))); }
    for (&k, &db) in &b { out.entry(k).or_insert_with(|| base[k].join(db)); }
    out
}

/// Non-contaminating read-only path-refined domain overlay (`None` = algebraically dead branch).
pub fn refine_guard_env(prog: &Program, g: NodeId, pol: bool, base: &[Domain], uf: &[usize]) -> Option<BTreeMap<usize, Domain>> {
    let mut env = BTreeMap::new();
    GuardCtx { prog, base, uf }.apply(g, pol, &mut env, 0)?;
    Some(env)
}

#[derive(Default)]
struct CheckAcc { proven: usize, uncertain: Option<VerifyError> }
impl CheckAcc {
    fn mark(&mut self, e: VerifyError) { if self.uncertain.is_none() { self.uncertain = Some(e); } }
    fn idx(&mut self, node: NodeId, d: Domain, limit: usize) -> Result<(), VerifyError> {
        let lim = limit as i128;
        if limit == 0 || d.hi < 0 || i128::from(d.lo) >= lim { return Err(VerifyError::OutOfBounds { node, idx_lo: d.lo, idx_hi: d.hi, limit }); }
        if d.lo >= 0 && i128::from(d.hi) < lim { self.proven += 1; } else { self.mark(VerifyError::OutOfBounds { node, idx_lo: d.lo, idx_hi: d.hi, limit }); }
        Ok(())
    }
    fn slot_init(&mut self, node: NodeId, buf: u8, d: Domain, bs: &BufInitState) -> Result<(), VerifyError> {
        if bs.st.all_init { self.proven += 1; return Ok(()); }
        let lim = bs.st.len as i128;
        let (lo_c, hi_c) = (i128::from(d.lo).max(0), i128::from(d.hi).min(lim.saturating_sub(1)));
        if lo_c > hi_c { return Ok(()); }
        let err = || VerifyError::UninitializedRead { node, buf, idx_lo: d.lo, idx_hi: d.hi };
        if let Some(c) = d.is_const() {
            return if bs.is_init(c as usize) { self.proven += 1; Ok(()) } else if bs.may_init.is_some_and(|m| m.contains(c)) { self.mark(err()); Ok(()) } else { Err(err()) };
        }
        let (start, end, mut any_init, mut all_init) = (lo_c as usize, hi_c as usize, false, true);
        if end - start <= 256 {
            for s in start..=end { if i64::try_from(s).is_ok_and(|sv| d.contains(sv)) { if bs.is_init(s) { any_init = true; } else { all_init = false; } } }
        } else {
            all_init = false;
            any_init = (start..end.min(64)).any(|s| d.contains(s as i64) && bs.st.is_slot_init(s))
                || bs.hi_init.range(start.max(64)..=end).any(|&s| i64::try_from(s).is_ok_and(|sv| d.contains(sv)));
        }
        let in_b = d.lo >= 0 && i128::from(d.hi) < lim;
        if all_init && in_b { self.proven += 1; } else if !any_init && !bs.may_init.is_some_and(|m| m.lo <= d.hi && d.lo <= m.hi) && in_b { return Err(err()); } else { self.mark(err()); }
        Ok(())
    }
}

struct BufInitState { st: AllocState, may_dead: bool, written_ec: BTreeSet<usize>, hi_init: BTreeSet<usize>, may_init: Option<Domain> }
impl BufInitState {
    fn from_buf(buf: &BufSpec) -> Self { Self { st: AllocState::from_buf(buf), may_dead: false, written_ec: BTreeSet::new(), hi_init: BTreeSet::new(), may_init: None } }
    fn reset_init(&mut self) { self.written_ec.clear(); self.hi_init.clear(); self.may_init = None; }
    fn is_init(&self, s: usize) -> bool { self.st.is_slot_init(s) || self.hi_init.contains(&s) }
}

fn calc_su(uniq: &[usize], su: &[usize]) -> usize {
    let mut w: Vec<usize> = uniq.iter().map(|&k| su[k]).collect();
    w.sort_unstable_by(|a, b| b.cmp(a));
    w.into_iter().enumerate().map(|(j, s)| s + j).max().unwrap_or(1).max(1)
}

fn apply_egraph_rules(nodes: &[IrOp], uf: &mut [usize], doms: &mut [Domain], id: usize, canon: IrOp) {
    match canon {
        Op::Sub(a, b) | Op::WrapSub(a, b) => {
            if a == b { let r = uf_find(uf, id); doms[r] = doms[r].meet(Domain::exact(0)); }
            if let Op::Add(x, y) | Op::WrapAdd(x, y) = nodes[a] {
                let (rx, ry) = (uf_find(uf, x), uf_find(uf, y));
                if ry == b { uf_union(uf, doms, id, rx); } else if rx == b { uf_union(uf, doms, id, ry); }
            }
        }
        Op::Add(a, b) | Op::WrapAdd(a, b) => {
            if let Op::Sub(x, y) | Op::WrapSub(x, y) = nodes[a] { if uf_find(uf, y) == b { uf_union(uf, doms, id, uf_find(uf, x)); } }
            if let (Op::Mul(a1, c1), Op::Mul(a2, c2)) = (nodes[a], nodes[b]) {
                let (rc1, rc2) = (uf_find(uf, c1), uf_find(uf, c2));
                if rc1 == rc2 { let r = uf_find(uf, id); doms[r] = doms[r].meet(doms[uf_find(uf, a1)].eval_add_sub(doms[uf_find(uf, a2)], false).0.eval_mul(doms[rc1]).0); }
            }
        }
        Op::BitXor(a, b) if a == b => { let r = uf_find(uf, id); doms[r] = doms[r].meet(Domain::exact(0)); }
        Op::BitAnd(a, b) | Op::BitOr(a, b) if a == b => uf_union(uf, doms, id, a),
        Op::Shr(a, s) => if let Op::Shl(x, s0) = nodes[a] {
            let rx = uf_find(uf, x);
            if s0 == s && s < 63 && doms[rx].is_nonneg() && ((doms[rx].hi as u128) << s) <= i64::MAX as u128 { uf_union(uf, doms, id, rx); }
        },
        Op::Div(a, b) => if let (Op::Mul(x, c), Some(cv)) = (nodes[a], doms[b].is_const()) {
            let (rx, rc) = (uf_find(uf, x), uf_find(uf, c));
            if cv > 0 && doms[rc].is_const() == Some(cv) && !doms[rx].eval_mul(Domain::exact(cv)).1 { uf_union(uf, doms, id, rx); }
        },
        _ => {}
    }
}

struct MemDomState { gens: Vec<(u32, bool)>, bg: Vec<Option<Domain>>, exact: Vec<BTreeMap<i64, Domain>> }
impl MemDomState {
    fn new(bufs: &[BufSpec]) -> Self {
        Self { gens: vec![(1, true); bufs.len()], bg: bufs.iter().map(|b| b.pre_init.then_some(b.elem_domain)).collect(), exact: vec![BTreeMap::new(); bufs.len()] }
    }
    fn eval(&mut self, bufs: &[BufSpec], op: IrOp, certain: bool, d_at: impl Fn(NodeId) -> Domain, pdoms: &[Domain]) -> Domain {
        match op {
            Op::Alloc { buf, .. } => {
                if !certain { return Domain::range(1, i64::MAX); }
                let bi = usize::from(buf); let (g, alive) = &mut self.gens[bi];
                *g = g.wrapping_add(1); *alive = true; self.bg[bi] = None; self.exact[bi].clear(); Domain::exact(i64::from(*g))
            }
            Op::Free(buf) => {
                if certain { let bi = usize::from(buf); let (g, alive) = &mut self.gens[bi]; if *alive { *g = g.wrapping_add(1); *alive = false; } self.bg[bi] = None; self.exact[bi].clear(); }
                Domain::exact(0)
            }
            Op::Store { buf, idx, val } => {
                let (bi, idom, vd) = (usize::from(buf), d_at(idx), d_at(val));
                if let Some(c) = idom.is_const() {
                    let nv = if certain { vd } else { self.exact[bi].get(&c).copied().or(self.bg[bi]).map_or(vd, |x| x.join(vd)) };
                    self.exact[bi].insert(c, nv);
                } else {
                    if certain { for &sd in self.exact[bi].values() { self.bg[bi] = Some(self.bg[bi].map_or(sd, |cur| cur.join(sd))); } self.exact[bi].clear(); }
                    self.bg[bi] = Some(self.bg[bi].map_or(vd, |cur| cur.join(vd)));
                }
                vd
            }
            Op::Load { buf, idx } => {
                let (bi, idom) = (usize::from(buf), d_at(idx));
                if let Some(c) = idom.is_const() { return self.exact[bi].get(&c).copied().or(self.bg[bi]).unwrap_or(bufs[bi].elem_domain); }
                let mut acc = self.bg[bi];
                for (&slot, &sd) in &self.exact[bi] { if idom.contains(slot) { acc = Some(acc.map_or(sd, |cur| cur.join(sd))); } }
                acc.unwrap_or(bufs[bi].elem_domain)
            }
            Op::Mul(a, b) if a == b => d_at(a).eval_square().0,
            Op::WrapMul(a, b) if a == b => { let (sq, ov) = d_at(a).eval_square(); if ov { Domain::top() } else { sq } }
            _ => op.eval_dom(d_at, |p| pdoms[usize::from(p)], |b| bufs[usize::from(b)].elem_domain),
        }
    }
}

fn check_mem_op(id: NodeId, op: IrOp, certain: bool, d_at: &impl Fn(NodeId) -> Domain, uf: &[usize], bstates: &mut [BufInitState], acc: &mut CheckAcc) -> Result<(), VerifyError> {
    match op {
        Op::Alloc { buf, len } => {
            let bs = &mut bstates[usize::from(buf)];
            if certain { bs.st.alloc(len); bs.may_dead = false; bs.reset_init(); acc.proven += 1; } else { bs.st.len = bs.st.len.min(len); }
        }
        Op::Free(buf) => {
            let bs = &mut bstates[usize::from(buf)];
            if !bs.st.alive { return Err(VerifyError::DoubleFree { node: id, buf, generation: bs.st.generation }); }
            if bs.may_dead { acc.mark(VerifyError::DoubleFree { node: id, buf, generation: bs.st.generation }); }
            if certain { let _ = bs.st.free(); bs.may_dead = false; bs.reset_init(); acc.proven += 1; } else { bs.may_dead = true; }
        }
        Op::CheckGen { buf, expected } => {
            let (bs, de) = (&bstates[usize::from(buf)], d_at(expected));
            if !bs.st.alive || !de.contains(i64::from(bs.st.generation)) { return Err(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
            if !bs.may_dead && de.is_const() == Some(i64::from(bs.st.generation)) { acc.proven += 1; } else { acc.mark(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
        }
        Op::Load { buf, idx } => {
            let (bs, di) = (&bstates[usize::from(buf)], d_at(idx));
            if !bs.st.alive { return Err(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
            if bs.may_dead { acc.mark(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
            acc.idx(id, di, bs.st.len)?;
            if bs.written_ec.contains(&uf_find(uf, idx)) { acc.proven += 1; } else { acc.slot_init(id, buf, di, bs)?; }
        }
        Op::Store { buf, idx, .. } => {
            let (bs, di) = (&mut bstates[usize::from(buf)], d_at(idx));
            if !bs.st.alive { return Err(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
            if bs.may_dead { acc.mark(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }); }
            acc.idx(id, di, bs.st.len)?;
            if certain {
                if let Some(c) = di.is_const().filter(|&c| c >= 0 && (c as usize) < bs.st.len) {
                    let s = c as usize; if s < 64 { bs.st.mark_init(s); } else { bs.hi_init.insert(s); }
                } else { bs.may_init = Some(bs.may_init.map_or(di, |cur| cur.join(di))); }
                bs.written_ec.insert(uf_find(uf, idx));
            } else { bs.may_init = Some(bs.may_init.map_or(di, |cur| cur.join(di))); }
        }
        _ => {}
    }
    Ok(())
}

fn check_arith_op(id: NodeId, op: IrOp, d_at: &impl Fn(NodeId) -> Domain, uf: &[usize], acc: &mut CheckAcc) -> Result<(), VerifyError> {
    match op {
        Op::BoundsCheck { idx, limit } => acc.idx(id, d_at(idx), limit)?,
        Op::Add(a, b) | Op::Sub(a, b) => if d_at(a).eval_add_sub(d_at(b), matches!(op, Op::Sub(_, _))).1 { acc.mark(VerifyError::IntOverflow { node: id }); } else { acc.proven += 1; },
        Op::Mul(a, b) => if if uf_find(uf, a) == uf_find(uf, b) { d_at(a).eval_square().1 } else { d_at(a).eval_mul(d_at(b)).1 } { acc.mark(VerifyError::IntOverflow { node: id }); } else { acc.proven += 1; },
        Op::Div(a, b) | Op::Rem(a, b) => {
            let (da, db) = (d_at(a), d_at(b));
            if db.is_const() == Some(0) || (da.is_const() == Some(i64::MIN) && db.is_const() == Some(-1)) { return Err(VerifyError::DivByZero { node: id }); }
            if da.eval_div_rem(db, matches!(op, Op::Rem(_, _))).1 { acc.mark(VerifyError::DivByZero { node: id }); } else { acc.proven += 1; }
        }
        Op::Shl(_, s) | Op::Shr(_, s) => if s >= 64 { return Err(VerifyError::ShiftOverflow { node: id, lo: i64::from(s), hi: i64::from(s) }); } else { acc.proven += 1; },
        Op::ShlVar(_, b) | Op::ShrVar(_, b) => {
            let db = d_at(b);
            if db.hi < 0 || db.lo >= 64 { return Err(VerifyError::ShiftOverflow { node: id, lo: db.lo, hi: db.hi }); }
            if db.lo >= 0 && db.hi < 64 { acc.proven += 1; } else { acc.mark(VerifyError::ShiftOverflow { node: id, lo: db.lo, hi: db.hi }); }
        }
        _ => {}
    }
    Ok(())
}

impl Program {
    #[must_use] pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), bufs: Vec::new(), param_domains: Vec::new(), nodes: Vec::new(), node_guards: Vec::new(), outputs: Vec::new(), simd_lanes: 8 }
    }
    pub fn add_buf(&mut self, name: impl Into<String>, len: usize, mutable: bool, region: u16, offset: usize, elem_domain: Domain) -> u8 {
        let id = self.bufs.len() as u8;
        self.bufs.push(BufSpec { id, name: name.into(), len, mutable, region, offset, elem_domain, pre_init: true }); id
    }
    pub fn add_uninit_buf(&mut self, name: impl Into<String>, len: usize, mutable: bool, region: u16, offset: usize, elem_domain: Domain) -> u8 {
        let id = self.add_buf(name, len, mutable, region, offset, elem_domain); self.bufs[usize::from(id)].pre_init = false; id
    }
    pub fn add_param(&mut self, domain: Domain) -> NodeId { let pid = self.param_domains.len() as u8; self.param_domains.push(domain); self.push(Op::Param(pid)) }
    pub fn push(&mut self, op: IrOp) -> NodeId { self.push_guarded(op, None) }
    pub fn push_guarded(&mut self, op: IrOp, guard: Option<(NodeId, bool)>) -> NodeId { let id = self.nodes.len(); self.nodes.push(op); self.node_guards.push(guard); id }
    #[must_use] pub fn guard_of(&self, id: NodeId) -> Option<(NodeId, bool)> { self.node_guards.get(id).copied().flatten() }
    pub fn add_output(&mut self, id: NodeId) { self.outputs.push(id); }

    pub fn validate(&self) -> Result<(), VerifyError> {
        for (pid, &d) in self.param_domains.iter().enumerate() { if d.tighten().is_none() { return Err(VerifyError::InvalidParam(pid as u8)); } }
        for b in &self.bufs { if b.elem_domain.tighten().is_none() { return Err(VerifyError::InvalidBuffer(b.id)); } }
        self.check_noalias()?;
        for (id, &op) in self.nodes.iter().enumerate() {
            let (kids, cnt) = op.children();
            for &k in &kids[..cnt] { if k >= id { return Err(VerifyError::InvalidNode(k)); } }
            if let Some((g, _)) = self.guard_of(id) { if g >= id { return Err(VerifyError::InvalidNode(g)); } }
            match op {
                Op::Param(p) if usize::from(p) >= self.param_domains.len() => return Err(VerifyError::InvalidParam(p)),
                Op::Load { buf, .. } | Op::CheckGen { buf, .. } if usize::from(buf) >= self.bufs.len() => return Err(VerifyError::InvalidBuffer(buf)),
                Op::Store { buf, .. } | Op::Alloc { buf, .. } | Op::Free(buf) if !self.bufs.get(usize::from(buf)).ok_or(VerifyError::InvalidBuffer(buf))?.mutable => return Err(VerifyError::WriteToReadOnly { buf }),
                _ => {}
            }
        }
        for &o in &self.outputs { if o >= self.nodes.len() { return Err(VerifyError::InvalidNode(o)); } }
        Ok(())
    }

    pub fn check_noalias(&self) -> Result<(), VerifyError> {
        let mut max_lens: Vec<usize> = self.bufs.iter().map(|b| b.len).collect();
        for &op in &self.nodes { if let Op::Alloc { buf, len } = op { if let Some(m) = max_lens.get_mut(usize::from(buf)) { *m = (*m).max(len); } } }
        for (i, a) in self.bufs.iter().enumerate() {
            if a.offset.checked_add(max_lens[i]).is_none() { return Err(VerifyError::NoAliasViolation { buf_a: a.id, buf_b: a.id, region: a.region }); }
        }
        for i in 0..self.bufs.len() {
            for j in (i + 1)..self.bufs.len() {
                let (a, b) = (&self.bufs[i], &self.bufs[j]);
                if a.region == b.region && (a.mutable || b.mutable) && (a.offset as u128) < (b.offset as u128) + (max_lens[j] as u128) && (b.offset as u128) < (a.offset as u128) + (max_lens[i] as u128) {
                    return Err(VerifyError::NoAliasViolation { buf_a: a.id, buf_b: b.id, region: a.region });
                }
            }
        }
        Ok(())
    }

    fn infer_domains_with_uf(&self, pdoms: &[Domain]) -> (Vec<Domain>, Vec<usize>) {
        type CseMemo = BTreeMap<(Option<(usize, bool)>, IrOp), usize>;
        let (n, mut mem) = (self.nodes.len(), MemDomState::new(&self.bufs));
        let (mut uf, mut doms, mut memo): (Vec<usize>, Vec<Domain>, CseMemo) = ((0..n).collect(), vec![Domain::top(); n], BTreeMap::new());
        for (id, &op) in self.nodes.iter().enumerate() {
            let (g_raw, canon) = (self.guard_of(id), op.map_ids(|k| uf_find(&uf, k)));
            let (overlay, certain) = match g_raw {
                None => (Some(BTreeMap::new()), true),
                Some((g, pol)) => {
                    let dg = doms[uf_find(&uf, g)];
                    (refine_guard_env(self, g, pol, &doms, &uf), if pol { !dg.contains(0) } else { dg.is_const() == Some(0) })
                }
            };
            let Some(ov) = overlay else { continue; };
            doms[id] = mem.eval(&self.bufs, canon, certain, |k| env_dom(&ov, &doms, &uf, k), pdoms);
            if g_raw.is_none() {
                if canon.is_pure() { let prev = *memo.entry((None, canon)).or_insert(id); if prev != id { uf_union(&mut uf, &mut doms, prev, id); } }
                apply_egraph_rules(&self.nodes, &mut uf, &mut doms, id, canon);
                if canon.is_pure() && !matches!(canon, Op::BoundsCheck { .. }) {
                    if let Some(c) = doms[uf_find(&uf, id)].is_const() { let prev = *memo.entry((None, Op::Const(c))).or_insert(id); if prev != id { uf_union(&mut uf, &mut doms, prev, id); } }
                }
            }
        }
        ((0..n).map(|i| doms[uf_find(&uf, i)]).collect(), uf)
    }

    #[must_use] pub fn infer_domains(&self, pdoms: &[Domain]) -> Vec<Domain> { self.infer_domains_with_uf(pdoms).0 }

    #[must_use] pub fn check_obligations(&self, pdoms: &[Domain]) -> (Vec<Domain>, ProofStatus, usize) {
        let (doms, uf) = self.infer_domains_with_uf(pdoms);
        let (mut bstates, mut acc): (Vec<BufInitState>, CheckAcc) = (self.bufs.iter().map(BufInitState::from_buf).collect(), CheckAcc::default());
        for (id, &op) in self.nodes.iter().enumerate() {
            let (overlay, certain) = match self.guard_of(id) {
                None => (BTreeMap::new(), true),
                Some((g, pol)) => {
                    let Some(ov) = refine_guard_env(self, g, pol, &doms, &uf) else { acc.proven += 1; continue; };
                    (ov, if pol { !doms[g].contains(0) } else { doms[g].is_const() == Some(0) })
                }
            };
            let d_at = |k: NodeId| env_dom(&overlay, &doms, &uf, k);
            if let Err(bug) = check_mem_op(id, op, certain, &d_at, &uf, &mut bstates, &mut acc).and_then(|()| check_arith_op(id, op, &d_at, &uf, &mut acc)) {
                if certain { return (doms, ProofStatus::DefiniteBug(bug), acc.proven); } else { acc.mark(bug); }
            }
        }
        (doms, acc.uncertain.map_or(ProofStatus::ProvenSafe, ProofStatus::Uncertain), acc.proven)
    }

    /// Dual-architecture live-register scheduler (x86_64 AVX2 14/16 & ARM64 AArch64 NEON 28/32).
    pub fn verify_schedule(&self, profile: ArchProfile) -> Result<ScheduleReport, VerifyError> {
        self.validate()?;
        let (n, is_imm) = (self.nodes.len(), |op: IrOp| matches!(op, Op::Const(_) | Op::Free(_)));
        let (mut reach, mut stack) = (vec![false; n], self.outputs.clone());
        if stack.is_empty() && n > 0 { stack.push(n - 1); }
        while let Some(u) = stack.pop() {
            if reach[u] { continue; }
            reach[u] = true;
            let (kids, cnt) = self.nodes[u].children(); stack.extend_from_slice(&kids[..cnt]);
            if let Some((g, _)) = self.guard_of(u) { stack.push(g); }
        }
        let (mut su, mut deps, mut cons, mut rem_uses) = (vec![0usize; n], vec![Vec::new(); n], vec![Vec::new(); n], vec![0usize; n]);
        for id in 0..n {
            if !reach[id] || is_imm(self.nodes[id]) { continue; }
            let (kids, cnt) = self.nodes[id].children();
            let mut uniq = Vec::new();
            for &k in &kids[..cnt] { if !is_imm(self.nodes[k]) && !uniq.contains(&k) { uniq.push(k); } }
            if let Some((g, _)) = self.guard_of(id) { if !is_imm(self.nodes[g]) && !uniq.contains(&g) { uniq.push(g); } }
            su[id] = calc_su(&uniq, &su);
            for &k in &uniq { cons[k].push(id); rem_uses[k] += 1; }
            deps[id] = uniq;
        }
        for &o in &self.outputs { if !is_imm(self.nodes[o]) && !matches!(self.nodes[o], Op::Store { .. }) { rem_uses[o] += 1; } }
        let (mut rem_deps, mut live, mut peak_ssa, mut live_nodes) = (deps.iter().map(Vec::len).collect::<Vec<_>>(), BTreeSet::new(), 0usize, 0usize);
        let mut ready: Vec<NodeId> = (0..n).filter(|&i| reach[i] && !is_imm(self.nodes[i]) && rem_deps[i] == 0).collect();
        while !ready.is_empty() {
            let best = ready.iter().enumerate().min_by_key(|&(_, &u)| {
                let kills = deps[u].iter().filter(|&&d| rem_uses[d] == 1).count() as isize;
                let helps = usize::from(!cons[u].iter().any(|&c| deps[c].iter().any(|d| live.contains(d))));
                (isize::from(rem_uses[u] > 0) - kills, helps, usize::MAX - su[u], u)
            }).map_or(0, |(pos, _)| pos);
            let u = ready.swap_remove(best);
            live_nodes += 1; peak_ssa = peak_ssa.max(live.len() + usize::from(rem_uses[u] > 0));
            if rem_uses[u] > 0 { live.insert(u); }
            for &d in &deps[u] { rem_uses[d] -= 1; if rem_uses[d] == 0 { live.remove(&d); } }
            for &c in &cons[u] { rem_deps[c] -= 1; if rem_deps[c] == 0 { ready.push(c); } }
        }
        let budget = profile.budget();
        let vecs_per_val = if self.simd_lanes == 0 { 0 } else { self.simd_lanes.div_ceil(budget.lanes_i64) };
        let (peak_gprs, peak_vecs) = (self.bufs.len() + peak_ssa, peak_ssa.saturating_mul(vecs_per_val));
        if peak_gprs > budget.max_gprs || peak_vecs > budget.max_vecs {
            return Err(VerifyError::RegisterSpill { profile, peak_gprs, max_gprs: budget.max_gprs, peak_vecs, max_vecs: budget.max_vecs });
        }
        Ok(ScheduleReport { profile, peak_gprs, peak_vecs, live_nodes })
    }

    pub fn verify_abstract(&self, profile: ArchProfile) -> Result<AbstractReport, VerifyError> {
        let schedule = self.verify_schedule(profile)?;
        let (domains, status, checks_proven) = self.check_obligations(&self.param_domains);
        Ok(AbstractReport { domains, status, schedule, checks_proven })
    }
}
