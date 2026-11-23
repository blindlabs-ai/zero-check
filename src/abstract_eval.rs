use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

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
    #[must_use] pub const fn name(self) -> &'static str {
        match self { Self::X86_64Avx2 => "x86_64-avx2", Self::Aarch64Neon => "aarch64-neon" }
    }
}

/// Generation-tagged ASan-class shadow-epoch allocation state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocState {
    pub len: usize,
    pub alive: bool,
    pub init_mask: u64,
    pub generation: u32,
    pub all_init: bool,
}

impl AllocState {
    #[must_use] pub const fn full_mask(len: usize) -> u64 {
        if len >= 64 { u64::MAX } else if len == 0 { 0 } else { (1u64 << len) - 1 }
    }
    #[must_use] pub const fn from_buf(buf: &BufSpec) -> Self {
        let init_mask = if buf.pre_init { Self::full_mask(buf.len) } else { 0 };
        Self { len: buf.len, alive: true, init_mask, generation: 1, all_init: buf.pre_init }
    }
    #[must_use] pub const fn is_slot_init(self, idx: usize) -> bool {
        if self.all_init { true } else if idx < 64 { ((self.init_mask >> idx) & 1) != 0 } else { false }
    }
    pub fn mark_init(&mut self, idx: usize) {
        if idx < 64 { self.init_mask |= 1u64 << idx; }
    }
    pub fn alloc(&mut self, len: usize) -> u32 {
        self.len = len;
        self.alive = true;
        self.init_mask = 0;
        self.all_init = false;
        self.generation = self.generation.wrapping_add(1);
        self.generation
    }
    pub fn free(&mut self) -> Result<u32, u32> {
        if !self.alive { return Err(self.generation); }
        self.alive = false;
        self.init_mask = 0;
        self.all_init = false;
        self.generation = self.generation.wrapping_add(1);
        Ok(self.generation)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    InvalidBuffer(u8), InvalidParam(u8), InvalidNode(NodeId),
    WriteToReadOnly { buf: u8 }, NoAliasViolation { buf_a: u8, buf_b: u8, region: u16 },
    UseAfterFree { node: NodeId, buf: u8, generation: u32 },
    DoubleFree { node: NodeId, buf: u8, generation: u32 },
    UninitializedRead { node: NodeId, buf: u8, idx_lo: i64, idx_hi: i64 },
    OutOfBounds { node: NodeId, idx_lo: i64, idx_hi: i64, limit: usize },
    IntOverflow { node: NodeId }, ShiftOverflow { node: NodeId, lo: i64, hi: i64 }, DivByZero { node: NodeId },
    RegisterSpill { profile: ArchProfile, peak_gprs: usize, max_gprs: usize, peak_vecs: usize, max_vecs: usize },
    CounterexampleFound { node: NodeId, fault: u8, inputs: Vec<i64> }, LintViolations { count: usize },
    Ntf1Violation(String), Io(String),
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBuffer(b) => write!(f, "invalid buffer {b}"),
            Self::InvalidParam(p) => write!(f, "invalid param {p}"),
            Self::InvalidNode(n) => write!(f, "invalid node {n}"),
            Self::WriteToReadOnly { buf } => write!(f, "write to read-only buffer {buf}"),
            Self::NoAliasViolation { buf_a, buf_b, region } => write!(f, "noalias overlap: bufs {buf_a},{buf_b} in region {region}"),
            Self::UseAfterFree { node, buf, generation } => write!(f, "node {node}: use-after-free on buf {buf} (gen {generation})"),
            Self::DoubleFree { node, buf, generation } => write!(f, "node {node}: double-free on buf {buf} (gen {generation})"),
            Self::UninitializedRead { node, buf, idx_lo, idx_hi } => write!(f, "node {node}: uninitialized read on buf {buf} idx [{idx_lo},{idx_hi}]"),
            Self::OutOfBounds { node, idx_lo, idx_hi, limit } => write!(f, "node {node}: idx [{idx_lo},{idx_hi}] outside 0..{limit}"),
            Self::IntOverflow { node } => write!(f, "node {node}: signed i64 overflow"),
            Self::ShiftOverflow { node, lo, hi } => write!(f, "node {node}: shift [{lo},{hi}] outside 0..64"),
            Self::DivByZero { node } => write!(f, "node {node}: div/rem by zero or i64::MIN / -1"),
            Self::RegisterSpill { profile, peak_gprs, max_gprs, peak_vecs, max_vecs } => write!(f, "register spill on {}: gprs {peak_gprs}/{max_gprs}, vecs {peak_vecs}/{max_vecs}", profile.name()),
            Self::CounterexampleFound { node, fault, inputs } => write!(f, "counterexample node {node} fault 0x{fault:02x}: {inputs:?}"),
            Self::LintViolations { count } => write!(f, "static Rust linter found {count} error(s)"),
            Self::Ntf1Violation(msg) => write!(f, "ntf1 violation: {msg}"),
            Self::Io(msg) => write!(f, "io error: {msg}"),
        }
    }
}

impl std::error::Error for VerifyError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Domain { pub lo: i64, pub hi: i64, pub modulus: i64, pub rem: i64 }

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.saturating_abs();
    b = b.saturating_abs();
    while b != 0 { let t = a % b; a = b; b = t; }
    if a == 0 { 1 } else { a }
}

fn gcd_i64(a: i64, b: i64) -> i64 {
    let g = gcd_i128(i128::from(a), i128::from(b));
    if g > i128::from(i64::MAX) { 1 } else { g as i64 }
}

impl Domain {
    #[must_use] pub const fn top() -> Self { Self { lo: i64::MIN, hi: i64::MAX, modulus: 1, rem: 0 } }
    #[must_use] pub const fn range(lo: i64, hi: i64) -> Self { if lo <= hi { Self { lo, hi, modulus: 1, rem: 0 } } else { Self::top() } }
    #[must_use] pub const fn exact(v: i64) -> Self { Self { lo: v, hi: v, modulus: 1, rem: 0 } }
    #[must_use] pub fn congruent(lo: i64, hi: i64, modulus: i64, rem: i64) -> Self {
        if lo > hi { return Self::top(); }
        if lo == hi { return Self::exact(lo); }
        let m = if modulus > 1 { modulus } else { 1 };
        let d = Self { lo, hi, modulus: m, rem: rem.rem_euclid(m) };
        d.tighten().unwrap_or(d)
    }
    #[must_use] pub const fn is_const(self) -> Option<i64> {
        if self.lo != self.hi || self.modulus < 1 || self.rem < 0 || self.rem >= self.modulus { return None; }
        if self.modulus == 1 { return Some(self.lo); }
        let r = self.lo % self.modulus;
        let eu = if r < 0 { r + self.modulus } else { r };
        if eu == self.rem { Some(self.lo) } else { None }
    }
    #[must_use] pub const fn is_nonneg(self) -> bool { self.lo >= 0 }
    #[must_use] pub fn contains(self, v: i64) -> bool {
        v >= self.lo && v <= self.hi && (self.modulus <= 1 || v.rem_euclid(self.modulus) == self.rem)
    }
    #[must_use] pub fn width_u128(self) -> u128 { (i128::from(self.hi) - i128::from(self.lo)) as u128 }

    /// Snap `[lo, hi]` inward to exact valid members of `x == rem (mod modulus)`.
    #[must_use] pub fn tighten(self) -> Option<Self> {
        if self.lo > self.hi || self.modulus < 1 || self.rem < 0 || self.rem >= self.modulus { return None; }
        if self.modulus == 1 { return Some(self); }
        let (m, r) = (i128::from(self.modulus), i128::from(self.rem));
        let (lo128, hi128) = (i128::from(self.lo), i128::from(self.hi));
        let nlo = lo128 + (r - lo128.rem_euclid(m)).rem_euclid(m);
        let nhi = hi128 - (hi128.rem_euclid(m) - r).rem_euclid(m);
        if nlo > nhi || nlo < i128::from(i64::MIN) || nhi > i128::from(i64::MAX) { None }
        else if nlo == nhi { Some(Self::exact(nlo as i64)) }
        else { Some(Self { lo: nlo as i64, hi: nhi as i64, modulus: self.modulus, rem: self.rem }) }
    }

    #[must_use] pub fn split_mid(self) -> Option<(Self, Self)> {
        let d = self.tighten()?;
        if d.lo >= d.hi { return None; }
        let mid = d.lo.wrapping_add(((i128::from(d.hi) - i128::from(d.lo)) / 2) as i64);
        let left = Self { hi: mid, ..d }.tighten()?;
        let right = Self { lo: mid.wrapping_add(1), ..d }.tighten()?;
        Some((left, right))
    }

    /// Exact disjoint parity split: `x == r (mod m)` -> `x == r (mod 2m)` U `x == r+m (mod 2m)`.
    #[must_use] pub fn split_mod2(self) -> Option<(Self, Self)> {
        let d = self.tighten()?;
        if d.lo >= d.hi || d.modulus > i64::MAX / 4 { return None; }
        let m2 = d.modulus * 2;
        let a = Self { lo: d.lo, hi: d.hi, modulus: m2, rem: d.rem }.tighten()?;
        let b = Self { lo: d.lo, hi: d.hi, modulus: m2, rem: d.rem + d.modulus }.tighten()?;
        Some((a, b))
    }

    #[must_use] pub fn rem_mod(self, d: i64) -> Option<i64> {
        if d <= 0 { None }
        else if let Some(c) = self.is_const() { Some(c.rem_euclid(d)) }
        else if self.modulus > 1 && self.modulus % d == 0 { Some(self.rem.rem_euclid(d)) }
        else { None }
    }
    #[must_use] pub fn meet(self, other: Self) -> Self {
        let (lo, hi) = (self.lo.max(other.lo), self.hi.min(other.hi));
        if lo > hi { return self; }
        let (modulus, rem) = if other.modulus > self.modulus { (other.modulus, other.rem) } else { (self.modulus, self.rem) };
        let cand = Self { lo, hi, modulus, rem };
        cand.tighten().unwrap_or(cand)
    }
    /// Sound congruence-preserving over-approximation of `self U other`.
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
        if lo >= i128::from(i64::MIN) && hi <= i128::from(i64::MAX) && lo <= hi {
            (Self::congruent(lo as i64, hi as i64, modulus, rem), false)
        } else { (Self::top(), true) }
    }
    #[must_use] pub fn eval_add_sub(self, rhs: Self, is_sub: bool) -> (Self, bool) {
        let (g, ra, rb) = match (self.is_const(), rhs.is_const()) {
            (Some(a), Some(b)) => (1i64, i128::from(a), i128::from(b)),
            (None, Some(b)) => (self.modulus, i128::from(self.rem), i128::from(b)),
            (Some(a), None) => (rhs.modulus, i128::from(a), i128::from(rhs.rem)),
            (None, None) => (gcd_i64(self.modulus, rhs.modulus), i128::from(self.rem), i128::from(rhs.rem)),
        };
        let g128 = i128::from(g);
        if is_sub {
            let rem = (ra - rb).rem_euclid(g128) as i64;
            Self::from_i128(i128::from(self.lo) - i128::from(rhs.hi), i128::from(self.hi) - i128::from(rhs.lo), g, rem)
        } else {
            let rem = (ra + rb).rem_euclid(g128) as i64;
            Self::from_i128(i128::from(self.lo) + i128::from(rhs.lo), i128::from(self.hi) + i128::from(rhs.hi), g, rem)
        }
    }
    /// Exact non-negative square domain with ring-lifting congruence: `(mk+r)^2 == r^2 (mod m*gcd(m+2r, 2m))`.
    #[must_use] pub fn eval_square(self) -> (Self, bool) {
        let (a0, a1) = (i128::from(self.lo), i128::from(self.hi));
        let (p0, p1) = (a0 * a0, a1 * a1);
        let lo = if self.lo <= 0 && self.hi >= 0 {
            if self.contains(0) { 0 } else {
                let pos = i128::from(self.rem);
                let neg = pos - i128::from(self.modulus);
                (pos * pos).min(neg * neg)
            }
        } else { p0.min(p1) };
        let hi = p0.max(p1);
        let (m, r) = if self.modulus > 1 {
            let (m128, r128) = (i128::from(self.modulus), i128::from(self.rem));
            let lifted = m128.saturating_mul(gcd_i128(m128 + 2 * r128, 2 * m128));
            let mm = if lifted <= i128::from(i64::MAX / 2) { lifted } else { m128 };
            (mm as i64, (r128 * r128).rem_euclid(mm) as i64)
        } else { (1, 0) };
        Self::from_i128(lo, hi, m, r)
    }
    #[must_use] pub fn eval_mul(self, rhs: Self) -> (Self, bool) {
        if self.is_const() == Some(0) || rhs.is_const() == Some(0) { return (Self::exact(0), false); }
        let (a0, a1, b0, b1) = (i128::from(self.lo), i128::from(self.hi), i128::from(rhs.lo), i128::from(rhs.hi));
        let p = [a0 * b0, a0 * b1, a1 * b0, a1 * b1];
        let lo = p.into_iter().min().unwrap_or(i128::from(i64::MIN));
        let hi = p.into_iter().max().unwrap_or(i128::from(i64::MAX));
        let cap = i128::from(i64::MAX / 2);
        let (m, rem) = if let Some(c) = rhs.is_const() {
            let mm = i128::from(self.modulus).saturating_mul(i128::from(c).abs());
            if mm > 1 && mm <= cap { (mm as i64, (i128::from(self.rem) * i128::from(c)).rem_euclid(mm) as i64) } else { (1, 0) }
        } else if let Some(c) = self.is_const() {
            let mm = i128::from(rhs.modulus).saturating_mul(i128::from(c).abs());
            if mm > 1 && mm <= cap { (mm as i64, (i128::from(rhs.rem) * i128::from(c)).rem_euclid(mm) as i64) } else { (1, 0) }
        } else {
            let (ma, ra, mb, rb) = (i128::from(self.modulus), i128::from(self.rem), i128::from(rhs.modulus), i128::from(rhs.rem));
            let mm = gcd_i128(gcd_i128(ma.saturating_mul(mb), ma.saturating_mul(rb)), mb.saturating_mul(ra));
            if mm > 1 && mm <= cap { (mm as i64, (ra * rb).rem_euclid(mm) as i64) } else { (1, 0) }
        };
        Self::from_i128(lo, hi, m, rem)
    }
    #[must_use] pub fn eval_div_rem(self, rhs_raw: Self, is_rem: bool) -> (Self, bool) {
        let Some(rhs) = rhs_raw.tighten() else { return (Self::top(), true); };
        if rhs.contains(0) || (self.lo == i64::MIN && rhs.contains(-1)) { return (Self::top(), true); }
        if let (Some(a), Some(b)) = (self.is_const(), rhs.is_const()) {
            return (Self::exact(if is_rem { a % b } else { a / b }), false);
        }
        if !is_rem {
            let mut c = vec![self.lo / rhs.lo, self.lo / rhs.hi, self.hi / rhs.lo, self.hi / rhs.hi];
            if rhs.lo < 0 && rhs.hi > 0 {
                let (pos_min, neg_max) = (rhs.rem, rhs.rem - rhs.modulus);
                for d in [pos_min, neg_max] {
                    if d != 0 && d >= rhs.lo && d <= rhs.hi { c.push(self.lo / d); c.push(self.hi / d); }
                }
            }
            return (Self::range(c.iter().copied().min().unwrap_or(i64::MIN), c.iter().copied().max().unwrap_or(i64::MAX)), false);
        }
        if let Some(d) = rhs.is_const().filter(|&d| d > 0) {
            if self.is_nonneg() {
                if self.hi < d { return (self, false); }
                let g = gcd_i64(self.modulus, d);
                if g > 1 {
                    let r0 = self.rem.rem_euclid(g);
                    let max_r = r0 + ((d - 1 - r0) / g) * g;
                    return (Self::congruent(r0, max_r, g, r0), false);
                }
                return (Self::range(0, d - 1), false);
            }
            return (Self::range(-(d - 1), d - 1), false);
        }
        let lim = (i128::from(rhs.lo).abs().max(i128::from(rhs.hi).abs()) - 1).min(i128::from(i64::MAX)) as i64;
        (Self::range(if self.is_nonneg() { 0 } else { -lim }, lim), false)
    }
    #[must_use] pub fn eval_shl(self, s: u8) -> (Self, bool) {
        if s >= 64 { return (Self::top(), true); }
        if s == 63 { return (Self::top(), false); }
        let m = if s > 0 && s < 62 { 1i64 << s } else { 1 };
        (Self::from_i128(i128::from(self.lo) << s, i128::from(self.hi) << s, m, 0).0, false)
    }
    #[must_use] pub fn eval_shr(self, s: u8) -> (Self, bool) {
        if s >= 64 { (Self::top(), true) } else { (Self::range(self.lo >> s, self.hi >> s), false) }
    }
    #[must_use] pub fn eval_bit(self, rhs: Self, kind: u8) -> Self {
        if let (Some(a), Some(b)) = (self.is_const(), rhs.is_const()) {
            return Self::exact(match kind { 0 => a & b, 1 => a | b, _ => a ^ b });
        }
        if kind == 0 { return match (self.is_nonneg(), rhs.is_nonneg()) { (true, true) => Self::range(0, self.hi.min(rhs.hi)), (false, true) => Self::range(0, rhs.hi), (true, false) => Self::range(0, self.hi), _ => Self::top() }; }
        if self.is_nonneg() && rhs.is_nonneg() {
            let mv = self.hi.max(rhs.hi) as u64;
            let bound = if mv == 0 { 0 } else { ((1u64 << (64 - mv.leading_zeros()).min(63)) - 1) as i64 };
            return Self::range(0, bound);
        }
        Self::top()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BufSpec {
    pub id: u8, pub name: String, pub len: usize, pub mutable: bool,
    pub region: u16, pub offset: usize, pub elem_domain: Domain, pub pre_init: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Op<Id> {
    Param(u8), Const(i64),
    Alloc { buf: u8, len: usize }, Free(u8), CheckGen { buf: u8, expected: Id },
    Load { buf: u8, idx: Id }, Store { buf: u8, idx: Id, val: Id }, BoundsCheck { idx: Id, limit: usize },
    Add(Id, Id), Sub(Id, Id), Mul(Id, Id), WrapAdd(Id, Id), WrapSub(Id, Id), WrapMul(Id, Id),
    Div(Id, Id), Rem(Id, Id), Shl(Id, u8), Shr(Id, u8), ShlVar(Id, Id), ShrVar(Id, Id),
    BitAnd(Id, Id), BitOr(Id, Id), BitXor(Id, Id),
}

impl<Id: Copy> Op<Id> {
    #[must_use] pub const fn is_pure(self) -> bool {
        !matches!(self, Self::Alloc { .. } | Self::Free(_) | Self::CheckGen { .. } | Self::Load { .. } | Self::Store { .. })
    }

    #[must_use] pub fn children(self) -> ([Id; 2], usize) where Id: Default {
        match self {
            Self::Param(_) | Self::Const(_) | Self::Alloc { .. } | Self::Free(_) => ([Id::default(), Id::default()], 0),
            Self::CheckGen { expected: a, .. } | Self::Load { idx: a, .. } | Self::BoundsCheck { idx: a, .. }
            | Self::Shl(a, _) | Self::Shr(a, _) => ([a, Id::default()], 1),
            Self::Store { idx: a, val: b, .. } | Self::Add(a, b) | Self::Sub(a, b) | Self::Mul(a, b)
            | Self::WrapAdd(a, b) | Self::WrapSub(a, b) | Self::WrapMul(a, b) | Self::Div(a, b) | Self::Rem(a, b)
            | Self::ShlVar(a, b) | Self::ShrVar(a, b) | Self::BitAnd(a, b) | Self::BitOr(a, b) | Self::BitXor(a, b) => ([a, b], 2),
        }
    }

    pub fn map_ids<Out>(self, mut f: impl FnMut(Id) -> Out) -> Op<Out> {
        match self {
            Self::Param(p) => Op::Param(p), Self::Const(c) => Op::Const(c),
            Self::Alloc { buf, len } => Op::Alloc { buf, len }, Self::Free(b) => Op::Free(b),
            Self::CheckGen { buf, expected } => Op::CheckGen { buf, expected: f(expected) },
            Self::Load { buf, idx } => Op::Load { buf, idx: f(idx) },
            Self::Store { buf, idx, val } => Op::Store { buf, idx: f(idx), val: f(val) },
            Self::BoundsCheck { idx, limit } => Op::BoundsCheck { idx: f(idx), limit },
            Self::Add(a, b) => Op::Add(f(a), f(b)), Self::Sub(a, b) => Op::Sub(f(a), f(b)), Self::Mul(a, b) => Op::Mul(f(a), f(b)),
            Self::WrapAdd(a, b) => Op::WrapAdd(f(a), f(b)), Self::WrapSub(a, b) => Op::WrapSub(f(a), f(b)), Self::WrapMul(a, b) => Op::WrapMul(f(a), f(b)),
            Self::Div(a, b) => Op::Div(f(a), f(b)), Self::Rem(a, b) => Op::Rem(f(a), f(b)),
            Self::Shl(a, s) => Op::Shl(f(a), s), Self::Shr(a, s) => Op::Shr(f(a), s),
            Self::ShlVar(a, b) => Op::ShlVar(f(a), f(b)), Self::ShrVar(a, b) => Op::ShrVar(f(a), f(b)),
            Self::BitAnd(a, b) => Op::BitAnd(f(a), f(b)), Self::BitOr(a, b) => Op::BitOr(f(a), f(b)), Self::BitXor(a, b) => Op::BitXor(f(a), f(b)),
        }
    }

    pub fn eval_dom(self, dom: impl Fn(Id) -> Domain, pdom: impl Fn(u8) -> Domain, bdom: impl Fn(u8) -> Domain) -> Domain {
        match self {
            Self::Param(p) => pdom(p), Self::Const(c) => Domain::exact(c),
            Self::Alloc { .. } => Domain::range(1, i64::MAX), Self::Free(_) => Domain::exact(0),
            Self::CheckGen { expected, .. } => dom(expected),
            Self::Load { buf, .. } => bdom(buf), Self::Store { val, .. } => dom(val),
            Self::BoundsCheck { idx, limit } => if limit > 0 { dom(idx).meet(Domain::range(0, i64::try_from(limit - 1).unwrap_or(i64::MAX))) } else { Domain::top() },
            Self::Add(a, b) | Self::WrapAdd(a, b) => dom(a).eval_add_sub(dom(b), false).0,
            Self::Sub(a, b) | Self::WrapSub(a, b) => dom(a).eval_add_sub(dom(b), true).0,
            Self::Mul(a, b) | Self::WrapMul(a, b) => dom(a).eval_mul(dom(b)).0,
            Self::Div(a, b) => dom(a).eval_div_rem(dom(b), false).0, Self::Rem(a, b) => dom(a).eval_div_rem(dom(b), true).0,
            Self::Shl(a, s) => dom(a).eval_shl(s).0, Self::Shr(a, s) => dom(a).eval_shr(s).0,
            Self::ShlVar(a, b) => dom(b).is_const().filter(|&s| (0..64).contains(&s)).map_or(Domain::top(), |s| dom(a).eval_shl(s as u8).0),
            Self::ShrVar(a, b) => dom(b).is_const().filter(|&s| (0..64).contains(&s)).map_or(Domain::top(), |s| dom(a).eval_shr(s as u8).0),
            Self::BitAnd(a, b) => dom(a).eval_bit(dom(b), 0), Self::BitOr(a, b) => dom(a).eval_bit(dom(b), 1), Self::BitXor(a, b) => dom(a).eval_bit(dom(b), 2),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    pub name: String, pub bufs: Vec<BufSpec>, pub param_domains: Vec<Domain>,
    pub nodes: Vec<IrOp>, pub outputs: Vec<NodeId>, pub simd_lanes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofStatus { ProvenSafe, DefiniteBug(VerifyError), Uncertain(VerifyError) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScheduleReport { pub profile: ArchProfile, pub peak_gprs: usize, pub peak_vecs: usize, pub live_nodes: usize }

#[derive(Clone, Debug)]
pub struct AbstractReport { pub domains: Vec<Domain>, pub status: ProofStatus, pub schedule: ScheduleReport, pub checks_proven: usize }

fn uf_find(uf: &[usize], mut x: usize) -> usize {
    while uf[x] != x { x = uf[x]; }
    x
}

fn check_idx_bound(node: NodeId, d: Domain, limit: usize, proven: &mut usize, uncertain: &mut Option<VerifyError>) -> Result<(), VerifyError> {
    let lim = limit as i128;
    if limit == 0 || d.hi < 0 || i128::from(d.lo) >= lim {
        return Err(VerifyError::OutOfBounds { node, idx_lo: d.lo, idx_hi: d.hi, limit });
    }
    if d.lo >= 0 && i128::from(d.hi) < lim { *proven += 1; }
    else if uncertain.is_none() { *uncertain = Some(VerifyError::OutOfBounds { node, idx_lo: d.lo, idx_hi: d.hi, limit }); }
    Ok(())
}

struct BufInitState {
    st: AllocState,
    written_ec: BTreeSet<usize>,
    hi_init: BTreeSet<usize>,
    may_init: Option<Domain>,
}

impl BufInitState {
    fn from_buf(buf: &BufSpec) -> Self {
        Self { st: AllocState::from_buf(buf), written_ec: BTreeSet::new(), hi_init: BTreeSet::new(), may_init: None }
    }
    fn reset_init(&mut self) {
        self.written_ec.clear();
        self.hi_init.clear();
        self.may_init = None;
    }
}

fn check_slot_init(
    node: NodeId, buf: u8, d: Domain, bs: &BufInitState,
    proven: &mut usize, uncertain: &mut Option<VerifyError>,
) -> Result<(), VerifyError> {
    if bs.st.all_init { *proven += 1; return Ok(()); }
    let lim = bs.st.len as i128;
    let hi_clamped = i128::from(d.hi).min(lim.saturating_sub(1));
    let lo_clamped = i128::from(d.lo).max(0);
    if lo_clamped > hi_clamped { return Ok(()); }
    if let Some(c) = d.is_const() {
        let slot = c as usize;
        if bs.st.is_slot_init(slot) || bs.hi_init.contains(&slot) { *proven += 1; return Ok(()); }
        if bs.may_init.is_some_and(|m| m.contains(c)) {
            if uncertain.is_none() { *uncertain = Some(VerifyError::UninitializedRead { node, buf, idx_lo: d.lo, idx_hi: d.hi }); }
            return Ok(());
        }
        return Err(VerifyError::UninitializedRead { node, buf, idx_lo: d.lo, idx_hi: d.hi });
    }
    let mut any_init = false;
    let mut all_slots_init = true;
    let scan_hi = hi_clamped.min(63) as i64;
    let scan_lo = lo_clamped.min(64) as i64;
    if scan_lo <= scan_hi {
        for v in scan_lo..=scan_hi {
            if d.contains(v) {
                if bs.st.is_slot_init(v as usize) { any_init = true; } else { all_slots_init = false; }
            }
        }
    }
    if hi_clamped >= 64 {
        let (hi_start, hi_end) = (lo_clamped.max(64) as usize, hi_clamped as usize);
        if bs.hi_init.range(hi_start..=hi_end).any(|&s| i64::try_from(s).is_ok_and(|sv| d.contains(sv))) {
            any_init = true;
        }
        if all_slots_init {
            if hi_end - hi_start <= 256 {
                for s in hi_start..=hi_end {
                    if i64::try_from(s).is_ok_and(|sv| d.contains(sv)) && !bs.hi_init.contains(&s) {
                        all_slots_init = false;
                        break;
                    }
                }
            } else {
                all_slots_init = false;
            }
        }
    }
    let may_overlap = bs.may_init.is_some_and(|m| m.lo <= d.hi && d.lo <= m.hi);
    if all_slots_init && d.lo >= 0 && i128::from(d.hi) < lim { *proven += 1; }
    else if !any_init && !may_overlap && d.lo >= 0 && i128::from(d.hi) < lim {
        return Err(VerifyError::UninitializedRead { node, buf, idx_lo: d.lo, idx_hi: d.hi });
    } else if uncertain.is_none() {
        *uncertain = Some(VerifyError::UninitializedRead { node, buf, idx_lo: d.lo, idx_hi: d.hi });
    }
    Ok(())
}

impl Program {
    #[must_use] pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), bufs: Vec::new(), param_domains: Vec::new(), nodes: Vec::new(), outputs: Vec::new(), simd_lanes: 8 }
    }
    pub fn add_buf(&mut self, name: impl Into<String>, len: usize, mutable: bool, region: u16, offset: usize, elem_domain: Domain) -> u8 {
        let id = self.bufs.len() as u8;
        self.bufs.push(BufSpec { id, name: name.into(), len, mutable, region, offset, elem_domain, pre_init: true });
        id
    }
    pub fn add_uninit_buf(&mut self, name: impl Into<String>, len: usize, mutable: bool, region: u16, offset: usize, elem_domain: Domain) -> u8 {
        let id = self.add_buf(name, len, mutable, region, offset, elem_domain);
        self.bufs[usize::from(id)].pre_init = false;
        id
    }
    pub fn add_param(&mut self, domain: Domain) -> NodeId {
        let pid = self.param_domains.len() as u8;
        self.param_domains.push(domain);
        self.push(Op::Param(pid))
    }
    pub fn push(&mut self, op: IrOp) -> NodeId { let id = self.nodes.len(); self.nodes.push(op); id }
    pub fn add_output(&mut self, id: NodeId) { self.outputs.push(id); }

    pub fn validate(&self) -> Result<(), VerifyError> {
        for (pid, &d) in self.param_domains.iter().enumerate() {
            if d.tighten().is_none() { return Err(VerifyError::InvalidParam(pid as u8)); }
        }
        for b in &self.bufs {
            if b.elem_domain.tighten().is_none() { return Err(VerifyError::InvalidBuffer(b.id)); }
        }
        self.check_noalias()?;
        for (id, &op) in self.nodes.iter().enumerate() {
            let (kids, cnt) = op.children();
            for &k in &kids[..cnt] { if k >= id { return Err(VerifyError::InvalidNode(k)); } }
            match op {
                Op::Param(p) if usize::from(p) >= self.param_domains.len() => return Err(VerifyError::InvalidParam(p)),
                Op::Load { buf, .. } | Op::CheckGen { buf, .. }
                    if usize::from(buf) >= self.bufs.len() => return Err(VerifyError::InvalidBuffer(buf)),
                Op::Store { buf, .. } | Op::Alloc { buf, .. } | Op::Free(buf) => {
                    let b = self.bufs.get(usize::from(buf)).ok_or(VerifyError::InvalidBuffer(buf))?;
                    if !b.mutable { return Err(VerifyError::WriteToReadOnly { buf }); }
                }
                _ => {}
            }
        }
        for &o in &self.outputs { if o >= self.nodes.len() { return Err(VerifyError::InvalidNode(o)); } }
        Ok(())
    }

    pub fn check_noalias(&self) -> Result<(), VerifyError> {
        let mut max_lens: Vec<usize> = self.bufs.iter().map(|b| b.len).collect();
        for &op in &self.nodes {
            if let Op::Alloc { buf, len } = op {
                if let Some(m) = max_lens.get_mut(usize::from(buf)) { *m = (*m).max(len); }
            }
        }
        for (i, a) in self.bufs.iter().enumerate() {
            if a.offset.checked_add(max_lens[i]).is_none() {
                return Err(VerifyError::NoAliasViolation { buf_a: a.id, buf_b: a.id, region: a.region });
            }
        }
        for i in 0..self.bufs.len() {
            for j in (i + 1)..self.bufs.len() {
                let (a, b) = (&self.bufs[i], &self.bufs[j]);
                if a.region == b.region && (a.mutable || b.mutable) {
                    let (a0, a1) = (a.offset as u128, (a.offset as u128) + (max_lens[i] as u128));
                    let (b0, b1) = (b.offset as u128, (b.offset as u128) + (max_lens[j] as u128));
                    if a0 < b1 && b0 < a1 { return Err(VerifyError::NoAliasViolation { buf_a: a.id, buf_b: b.id, region: a.region }); }
                }
            }
        }
        Ok(())
    }

    fn infer_domains_with_uf(&self, pdoms: &[Domain]) -> (Vec<Domain>, Vec<usize>) {
        let n = self.nodes.len();
        let (mut uf, mut doms, mut memo): (Vec<usize>, Vec<Domain>, BTreeMap<IrOp, usize>) = ((0..n).collect(), vec![Domain::top(); n], BTreeMap::new());
        let mut gens: Vec<(u32, bool)> = vec![(1, true); self.bufs.len()];
        let mut bg_doms: Vec<Option<Domain>> = self.bufs.iter().map(|b| if b.pre_init { Some(b.elem_domain) } else { None }).collect();
        let mut exact_stores: Vec<BTreeMap<i64, Domain>> = vec![BTreeMap::new(); self.bufs.len()];
        let union = |uf: &mut [usize], doms: &mut [Domain], a: usize, b: usize| {
            let (mut ra, mut rb) = (uf_find(uf, a), uf_find(uf, b));
            if ra == rb { return; }
            if ra > rb { std::mem::swap(&mut ra, &mut rb); }
            uf[rb] = ra;
            doms[ra] = doms[ra].meet(doms[rb]);
        };
        for (id, &op) in self.nodes.iter().enumerate() {
            let canon = op.map_ids(|k| uf_find(&uf, k));
            doms[id] = match canon {
                Op::Alloc { buf, .. } => {
                    let bi = usize::from(buf);
                    let (g, alive) = &mut gens[bi];
                    *g = g.wrapping_add(1);
                    *alive = true;
                    bg_doms[bi] = None;
                    exact_stores[bi].clear();
                    Domain::exact(i64::from(*g))
                }
                Op::Free(buf) => {
                    let bi = usize::from(buf);
                    let (g, alive) = &mut gens[bi];
                    if *alive { *g = g.wrapping_add(1); *alive = false; }
                    bg_doms[bi] = None;
                    exact_stores[bi].clear();
                    Domain::exact(0)
                }
                Op::Store { buf, idx, val } => {
                    let bi = usize::from(buf);
                    let (idom, vd) = (doms[uf_find(&uf, idx)], doms[uf_find(&uf, val)]);
                    if let Some(c) = idom.is_const() {
                        exact_stores[bi].insert(c, vd);
                    } else {
                        for &sd in exact_stores[bi].values() {
                            bg_doms[bi] = Some(bg_doms[bi].map_or(sd, |cur| cur.join(sd)));
                        }
                        exact_stores[bi].clear();
                        bg_doms[bi] = Some(bg_doms[bi].map_or(vd, |cur| cur.join(vd)));
                    }
                    vd
                }
                Op::Load { buf, idx } => {
                    let bi = usize::from(buf);
                    let idom = doms[uf_find(&uf, idx)];
                    if let Some(c) = idom.is_const() {
                        exact_stores[bi].get(&c).copied().or(bg_doms[bi]).unwrap_or(self.bufs[bi].elem_domain)
                    } else {
                        let mut acc = bg_doms[bi];
                        for (&slot, &sd) in &exact_stores[bi] {
                            if idom.contains(slot) { acc = Some(acc.map_or(sd, |cur| cur.join(sd))); }
                        }
                        acc.unwrap_or(self.bufs[bi].elem_domain)
                    }
                }
                Op::Mul(a, b) if a == b => doms[a].eval_square().0,
                Op::WrapMul(a, b) if a == b => { let (sq, ov) = doms[a].eval_square(); if ov { Domain::top() } else { sq } }
                _ => canon.eval_dom(|k| doms[uf_find(&uf, k)], |p| pdoms[usize::from(p)], |b| self.bufs[usize::from(b)].elem_domain),
            };
            if canon.is_pure() {
                if let Some(&prev) = memo.get(&canon) { union(&mut uf, &mut doms, prev, id); } else { memo.insert(canon, id); }
            }
            match canon {
                Op::Sub(a, b) | Op::WrapSub(a, b) => {
                    if a == b { let r = uf_find(&uf, id); doms[r] = doms[r].meet(Domain::exact(0)); }
                    if let Op::Add(x, y) | Op::WrapAdd(x, y) = self.nodes[a] {
                        let (rx, ry) = (uf_find(&uf, x), uf_find(&uf, y));
                        if ry == b { union(&mut uf, &mut doms, id, rx); } else if rx == b { union(&mut uf, &mut doms, id, ry); }
                    }
                }
                Op::Add(a, b) | Op::WrapAdd(a, b) => {
                    if let Op::Sub(x, y) | Op::WrapSub(x, y) = self.nodes[a] {
                        let (rx, ry) = (uf_find(&uf, x), uf_find(&uf, y));
                        if ry == b { union(&mut uf, &mut doms, id, rx); }
                    }
                    if let (Op::Mul(a1, c1), Op::Mul(a2, c2)) = (self.nodes[a], self.nodes[b]) {
                        let (rc1, rc2) = (uf_find(&uf, c1), uf_find(&uf, c2));
                        if rc1 == rc2 {
                            let s = doms[uf_find(&uf, a1)].eval_add_sub(doms[uf_find(&uf, a2)], false).0;
                            let r = uf_find(&uf, id);
                            doms[r] = doms[r].meet(s.eval_mul(doms[rc1]).0);
                        }
                    }
                }
                Op::BitXor(a, b) if a == b => { let r = uf_find(&uf, id); doms[r] = doms[r].meet(Domain::exact(0)); }
                Op::BitAnd(a, b) | Op::BitOr(a, b) if a == b => union(&mut uf, &mut doms, id, a),
                Op::Shr(a, s) => if let Op::Shl(x, s0) = self.nodes[a] {
                    let rx = uf_find(&uf, x);
                    if s0 == s && s < 63 && doms[rx].is_nonneg() && ((doms[rx].hi as u128) << s) <= i64::MAX as u128 { union(&mut uf, &mut doms, id, rx); }
                },
                Op::Div(a, b) => if let (Op::Mul(x, c), Some(cv)) = (self.nodes[a], doms[b].is_const()) {
                    let (rx, rc) = (uf_find(&uf, x), uf_find(&uf, c));
                    if cv > 0 && doms[rc].is_const() == Some(cv) && !doms[rx].eval_mul(Domain::exact(cv)).1 { union(&mut uf, &mut doms, id, rx); }
                },
                _ => {}
            }
            if canon.is_pure() && !matches!(canon, Op::BoundsCheck { .. }) {
                if let Some(c) = doms[uf_find(&uf, id)].is_const() {
                    let prev = *memo.entry(Op::Const(c)).or_insert(id);
                    if prev != id { union(&mut uf, &mut doms, prev, id); }
                }
            }
        }
        let final_doms = (0..n).map(|i| doms[uf_find(&uf, i)]).collect();
        (final_doms, uf)
    }

    /// Interval + modular + E-Graph equivalence domain inference (breaks dependency blowup).
    #[must_use] pub fn infer_domains(&self, pdoms: &[Domain]) -> Vec<Domain> {
        self.infer_domains_with_uf(pdoms).0
    }

    #[must_use] pub fn check_obligations(&self, pdoms: &[Domain]) -> (Vec<Domain>, ProofStatus, usize) {
        let (doms, uf) = self.infer_domains_with_uf(pdoms);
        let mut bstates: Vec<BufInitState> = self.bufs.iter().map(BufInitState::from_buf).collect();
        let (mut proven, mut first_uncertain) = (0usize, None);
        for (id, &op) in self.nodes.iter().enumerate() {
            match op {
                Op::Alloc { buf, len } => {
                    let bs = &mut bstates[usize::from(buf)];
                    bs.st.alloc(len);
                    bs.reset_init();
                    proven += 1;
                }
                Op::Free(buf) => {
                    let bs = &mut bstates[usize::from(buf)];
                    if let Err(generation) = bs.st.free() {
                        return (doms, ProofStatus::DefiniteBug(VerifyError::DoubleFree { node: id, buf, generation }), proven);
                    }
                    bs.reset_init();
                    proven += 1;
                }
                Op::CheckGen { buf, expected } => {
                    let st = bstates[usize::from(buf)].st;
                    let de = doms[expected];
                    if !st.alive || !de.contains(i64::from(st.generation)) {
                        return (doms, ProofStatus::DefiniteBug(VerifyError::UseAfterFree { node: id, buf, generation: st.generation }), proven);
                    }
                    if de.is_const() == Some(i64::from(st.generation)) { proven += 1; }
                    else if first_uncertain.is_none() { first_uncertain = Some(VerifyError::UseAfterFree { node: id, buf, generation: st.generation }); }
                }
                Op::Load { buf, idx } => {
                    let bs = &bstates[usize::from(buf)];
                    if !bs.st.alive {
                        return (doms, ProofStatus::DefiniteBug(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }), proven);
                    }
                    if let Err(bug) = check_idx_bound(id, doms[idx], bs.st.len, &mut proven, &mut first_uncertain) {
                        return (doms, ProofStatus::DefiniteBug(bug), proven);
                    }
                    if bs.written_ec.contains(&uf_find(&uf, idx)) {
                        proven += 1;
                    } else if let Err(bug) = check_slot_init(id, buf, doms[idx], bs, &mut proven, &mut first_uncertain) {
                        return (doms, ProofStatus::DefiniteBug(bug), proven);
                    }
                }
                Op::Store { buf, idx, .. } => {
                    let bs = &mut bstates[usize::from(buf)];
                    if !bs.st.alive {
                        return (doms, ProofStatus::DefiniteBug(VerifyError::UseAfterFree { node: id, buf, generation: bs.st.generation }), proven);
                    }
                    if let Err(bug) = check_idx_bound(id, doms[idx], bs.st.len, &mut proven, &mut first_uncertain) {
                        return (doms, ProofStatus::DefiniteBug(bug), proven);
                    }
                    if let Some(c) = doms[idx].is_const() {
                        if c >= 0 && (c as usize) < bs.st.len {
                            let slot = c as usize;
                            if slot < 64 { bs.st.mark_init(slot); } else { bs.hi_init.insert(slot); }
                        }
                    } else {
                        bs.may_init = Some(bs.may_init.map_or(doms[idx], |cur| cur.join(doms[idx])));
                    }
                    bs.written_ec.insert(uf_find(&uf, idx));
                }
                Op::BoundsCheck { idx, limit } => {
                    if let Err(bug) = check_idx_bound(id, doms[idx], limit, &mut proven, &mut first_uncertain) {
                        return (doms, ProofStatus::DefiniteBug(bug), proven);
                    }
                }
                Op::Add(a, b) | Op::Sub(a, b) => {
                    if doms[a].eval_add_sub(doms[b], matches!(op, Op::Sub(_, _))).1 {
                        if first_uncertain.is_none() { first_uncertain = Some(VerifyError::IntOverflow { node: id }); }
                    } else { proven += 1; }
                }
                Op::Mul(a, b) => {
                    let ov = if uf_find(&uf, a) == uf_find(&uf, b) { doms[a].eval_square().1 } else { doms[a].eval_mul(doms[b]).1 };
                    if ov {
                        if first_uncertain.is_none() { first_uncertain = Some(VerifyError::IntOverflow { node: id }); }
                    } else { proven += 1; }
                }
                Op::Div(a, b) | Op::Rem(a, b) => {
                    let (da, db) = (doms[a], doms[b]);
                    if db.is_const() == Some(0) || (da.is_const() == Some(i64::MIN) && db.is_const() == Some(-1)) {
                        return (doms, ProofStatus::DefiniteBug(VerifyError::DivByZero { node: id }), proven);
                    }
                    if da.eval_div_rem(db, matches!(op, Op::Rem(_, _))).1 {
                        if first_uncertain.is_none() { first_uncertain = Some(VerifyError::DivByZero { node: id }); }
                    } else { proven += 1; }
                }
                Op::Shl(_, s) | Op::Shr(_, s) => {
                    if s >= 64 { return (doms, ProofStatus::DefiniteBug(VerifyError::ShiftOverflow { node: id, lo: i64::from(s), hi: i64::from(s) }), proven); }
                    proven += 1;
                }
                Op::ShlVar(_, b) | Op::ShrVar(_, b) => {
                    let db = doms[b];
                    if db.hi < 0 || db.lo >= 64 { return (doms, ProofStatus::DefiniteBug(VerifyError::ShiftOverflow { node: id, lo: db.lo, hi: db.hi }), proven); }
                    if db.lo >= 0 && db.hi < 64 { proven += 1; }
                    else if first_uncertain.is_none() { first_uncertain = Some(VerifyError::ShiftOverflow { node: id, lo: db.lo, hi: db.hi }); }
                }
                _ => {}
            }
        }
        (doms, first_uncertain.map_or(ProofStatus::ProvenSafe, ProofStatus::Uncertain), proven)
    }

    /// Dual-architecture live-register scheduler (x86_64 AVX2 14/16 & ARM64 AArch64 NEON 28/32).
    pub fn verify_schedule(&self, profile: ArchProfile) -> Result<ScheduleReport, VerifyError> {
        self.validate()?;
        let n = self.nodes.len();
        let (mut reach, mut stack) = (vec![false; n], self.outputs.clone());
        if stack.is_empty() && n > 0 { stack.push(n - 1); }
        while let Some(u) = stack.pop() {
            if reach[u] { continue; }
            reach[u] = true;
            let (kids, cnt) = self.nodes[u].children();
            stack.extend_from_slice(&kids[..cnt]);
        }
        let is_imm = |op: IrOp| matches!(op, Op::Const(_) | Op::Free(_));
        let (mut su, mut deps, mut cons, mut rem_uses) = (vec![0usize; n], vec![Vec::new(); n], vec![Vec::new(); n], vec![0usize; n]);
        for id in 0..n {
            if !reach[id] || is_imm(self.nodes[id]) { continue; }
            let (kids, cnt) = self.nodes[id].children();
            let mut uniq = Vec::new();
            for &k in &kids[..cnt] { if !is_imm(self.nodes[k]) && !uniq.contains(&k) { uniq.push(k); } }
            su[id] = match uniq.as_slice() {
                [] => 1,
                [a] => su[*a].max(1),
                [a, b] => if su[*a] == su[*b] { su[*a] + 1 } else { su[*a].max(su[*b]) },
                _ => 1,
            };
            for &k in &uniq { cons[k].push(id); rem_uses[k] += 1; }
            deps[id] = uniq;
        }
        for &o in &self.outputs {
            if !is_imm(self.nodes[o]) && !matches!(self.nodes[o], Op::Store { .. }) { rem_uses[o] += 1; }
        }
        let mut rem_deps: Vec<usize> = deps.iter().map(Vec::len).collect();
        let mut ready: Vec<NodeId> = (0..n).filter(|&i| reach[i] && !is_imm(self.nodes[i]) && rem_deps[i] == 0).collect();
        let (mut live, mut peak_ssa, mut live_nodes) = (BTreeSet::new(), 0usize, 0usize);
        while !ready.is_empty() {
            let mut best = (0usize, (isize::MAX, 1usize, usize::MAX, usize::MAX));
            for (pos, &u) in ready.iter().enumerate() {
                let kills = deps[u].iter().filter(|&&d| rem_uses[d] == 1).count() as isize;
                let delta = isize::from(rem_uses[u] > 0) - kills;
                let helps = usize::from(!cons[u].iter().any(|&c| deps[c].iter().any(|d| live.contains(d))));
                let key = (delta, helps, usize::MAX - su[u], u);
                if key < best.1 { best = (pos, key); }
            }
            let u = ready.swap_remove(best.0);
            live_nodes += 1;
            peak_ssa = peak_ssa.max(live.len() + usize::from(rem_uses[u] > 0));
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
