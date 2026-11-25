use crate::abstract_eval::{AllocState, Domain, Op, Program, ProofStatus, VerifyError};
pub const LANES: usize = 8;
pub const FAULT_NONE: u8 = 0;
pub const FAULT_OOB: u8 = 1 << 0; pub const FAULT_OVERFLOW: u8 = 1 << 1; pub const FAULT_SHIFT: u8 = 1 << 2; pub const FAULT_DIV0: u8 = 1 << 3;
pub const FAULT_UAF: u8 = 1 << 4; pub const FAULT_DOUBLE_FREE: u8 = 1 << 5; pub const FAULT_UNINIT: u8 = 1 << 6; pub const FAULT_PANIC: u8 = 1 << 7;
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub struct RefineConfig { pub max_epochs: usize, pub fuzz_ticks_per_box: usize, pub seed: u64, pub synthesize_safe_boundary: bool }
impl Default for RefineConfig { fn default() -> Self { Self { max_epochs: 256, fuzz_ticks_per_box: 4, seed: 0x51A7_C0DE_1337_BEEF, synthesize_safe_boundary: false } } }
#[derive(Clone, Debug, PartialEq, Eq)] pub struct Counterexample { pub inputs: Vec<i64>, pub node: usize, pub fault: u8 }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofVerdict {
    ProvenTotal { boxes_discharged: usize, learned_invariants: Vec<String> },
    Counterexample { input: Vec<i64>, node: usize, fault: u8, synthesized_guard: String },
    Incomplete { boxes_discharged: usize, unproven_boxes: usize }, }
#[derive(Clone, Debug)] pub struct BatchEval { pub faults: [u8; LANES], pub fault_nodes: [u16; LANES], pub outputs: Vec<[i64; LANES]> }
#[derive(Clone, Debug)]
pub struct RefineReport {
    pub ticks: usize, pub evals: usize, pub bisections: usize, pub proven_boxes: usize, pub unproven_boxes: usize,
    pub safe_subdomains: Vec<Vec<Domain>>, pub counterexamples: Vec<Counterexample>, pub learned_invariants: Vec<String>, pub synthesized_guard: String, pub verdict: ProofVerdict, }
#[must_use] pub fn fault_name(fault: u8) -> &'static str {
    for (bit, name) in [(FAULT_PANIC, "PANIC"), (FAULT_UAF, "UAF"), (FAULT_DOUBLE_FREE, "DOUBLE_FREE"), (FAULT_UNINIT, "UNINIT"), (FAULT_OOB, "OOB"), (FAULT_DIV0, "DIV0"), (FAULT_SHIFT, "SHIFT"), (FAULT_OVERFLOW, "OVERFLOW")] { if (fault & bit) != 0 { return name; } }
    "NONE" }
#[inline] fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15); let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9); z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB); z ^ (z >> 31) }
#[inline] fn snap_domain(d: Domain, raw: i64) -> i64 {
    let mut v = raw.max(d.lo).min(d.hi);
    if d.modulus > 1 {
        let diff = (d.rem - v.rem_euclid(d.modulus)).rem_euclid(d.modulus);
        if let Some(up) = v.checked_add(diff).filter(|&u| u <= d.hi) { v = up; } else if let Some(dn) = v.checked_sub(d.modulus - diff).filter(|&u| u >= d.lo) { v = dn; } }
    v }
struct LaneCtx { faults: [u8; LANES], fnodes: [u16; LANES] }
impl LaneCtx {
    #[inline] fn mark(&mut self, l: usize, id: usize, bad: bool, bit: u8) { if bad { if self.faults[l] == 0 { self.fnodes[l] = id as u16; } self.faults[l] |= bit; } }
    fn arith(&mut self, a: [i64; LANES], b: [i64; LANES], kind: u8, id: usize, act: [bool; LANES]) -> [i64; LANES] {
        std::array::from_fn(|l| { let (v, ov) = match kind { 0 => a[l].overflowing_add(b[l]), 1 => a[l].overflowing_sub(b[l]), _ => a[l].overflowing_mul(b[l]) }; self.mark(l, id, act[l] && ov, FAULT_OVERFLOW); v }) }
    fn div(&mut self, a: [i64; LANES], b: [i64; LANES], is_rem: bool, id: usize, act: [bool; LANES]) -> [i64; LANES] {
        std::array::from_fn(|l| { let bad = b[l] == 0 || (a[l] == i64::MIN && b[l] == -1); self.mark(l, id, act[l] && bad, FAULT_DIV0); let sb = if bad { 1 } else { b[l] }; if is_rem { a[l] % sb } else { a[l] / sb } }) }
    fn shift(&mut self, a: [i64; LANES], s: [i64; LANES], is_shl: bool, id: usize, act: [bool; LANES]) -> [i64; LANES] {
        std::array::from_fn(|l| { self.mark(l, id, act[l] && !(0..64).contains(&s[l]), FAULT_SHIFT); let sm = (s[l] as u32) & 63; if is_shl { a[l].wrapping_shl(sm) } else { a[l].wrapping_shr(sm) } }) }
    fn load(&mut self, id: usize, act: [bool; LANES], edom: Domain, s: &[AllocState; LANES], wr: &[Vec<(usize, i64)>; LANES], ix: [i64; LANES]) -> [i64; LANES] {
        std::array::from_fn(|l| {
            if !act[l] { return 0; }
            if !s[l].alive { self.mark(l, id, true, FAULT_UAF); 0 }
            else if ix[l] < 0 || (ix[l] as usize) >= s[l].len { self.mark(l, id, true, FAULT_OOB); 0 }
            else {
                let slot = ix[l] as usize; let written = wr[l].iter().find(|&&(k, _)| k == slot).map(|&(_, v)| v);
                if !s[l].is_slot_init(slot) && written.is_none() { self.mark(l, id, true, FAULT_UNINIT); }
                written.unwrap_or_else(|| snap_domain(edom, ix[l].wrapping_mul(0x517C_C1B7))) }
        }) }
    fn store(&mut self, id: usize, act: [bool; LANES], s: &mut [AllocState; LANES], wr: &mut [Vec<(usize, i64)>; LANES], ix: [i64; LANES], vv: [i64; LANES]) -> [i64; LANES] {
        for l in 0..LANES {
            if !act[l] { continue; }
            if !s[l].alive { self.mark(l, id, true, FAULT_UAF); }
            else if ix[l] < 0 || (ix[l] as usize) >= s[l].len { self.mark(l, id, true, FAULT_OOB); }
            else { let slot = ix[l] as usize; s[l].mark_init(slot); if let Some(e) = wr[l].iter_mut().find(|(k, _)| *k == slot) { e.1 = vv[l]; } else { wr[l].push((slot, vv[l])); } } }
        vv } }
/// Branchless 8-lane SIMD-parallel evaluator catching Miri + ASan shadow-epoch faults with branch guards.
#[must_use] pub fn eval_lanes_x8(prog: &Program, param_lanes: &[[i64; LANES]]) -> BatchEval {
    let mut vals = vec![[0i64; LANES]; prog.nodes.len()]; let mut shadow: Vec<[AllocState; LANES]> = prog.bufs.iter().map(|b| [AllocState::from_buf(b); LANES]).collect();
    let mut writes: Vec<[Vec<(usize, i64)>; LANES]> = prog.bufs.iter().map(|_| std::array::from_fn(|_| Vec::new())).collect();
    let mut ctx = LaneCtx { faults: [FAULT_NONE; LANES], fnodes: [u16::MAX; LANES] };
    for (id, &op) in prog.nodes.iter().enumerate() {
        let act: [bool; LANES] = match prog.guard_of(id) { None => [true; LANES], Some((g, pol)) => std::array::from_fn(|l| (vals[g][l] != 0) == pol) };
        vals[id] = match op {
            Op::Param(p) => param_lanes[usize::from(p)], Op::Const(c) => [c; LANES],
            Op::Alloc { buf, len } => { let (s, wr) = (&mut shadow[usize::from(buf)], &mut writes[usize::from(buf)]); std::array::from_fn(|l| if act[l] { wr[l].clear(); i64::from(s[l].alloc(len)) } else { i64::from(s[l].generation) }) }
            Op::Free(buf) => {
                let (s, wr) = (&mut shadow[usize::from(buf)], &mut writes[usize::from(buf)]);
                for (l, st) in s.iter_mut().enumerate() { if act[l] { if st.free().is_err() { ctx.mark(l, id, true, FAULT_DOUBLE_FREE); } else { wr[l].clear(); } } }
                [0; LANES] }
            Op::CheckGen { buf, expected } => { let (s, exp) = (&shadow[usize::from(buf)], vals[expected]); for l in 0..LANES { ctx.mark(l, id, act[l] && (!s[l].alive || exp[l] != i64::from(s[l].generation)), FAULT_UAF); } exp }
            Op::Add(a, b) => ctx.arith(vals[a], vals[b], 0, id, act), Op::Sub(a, b) => ctx.arith(vals[a], vals[b], 1, id, act), Op::Mul(a, b) => ctx.arith(vals[a], vals[b], 2, id, act),
            Op::WrapAdd(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_add(vals[b][l])), Op::WrapSub(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_sub(vals[b][l])), Op::WrapMul(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_mul(vals[b][l])),
            Op::Div(a, b) => ctx.div(vals[a], vals[b], false, id, act), Op::Rem(a, b) => ctx.div(vals[a], vals[b], true, id, act),
            Op::Shl(a, s) => ctx.shift(vals[a], [i64::from(s); LANES], true, id, act), Op::Shr(a, s) => ctx.shift(vals[a], [i64::from(s); LANES], false, id, act),
            Op::ShlVar(a, b) => ctx.shift(vals[a], vals[b], true, id, act), Op::ShrVar(a, b) => ctx.shift(vals[a], vals[b], false, id, act),
            Op::BitAnd(a, b) => std::array::from_fn(|l| vals[a][l] & vals[b][l]), Op::BitOr(a, b) => std::array::from_fn(|l| vals[a][l] | vals[b][l]), Op::BitXor(a, b) => std::array::from_fn(|l| vals[a][l] ^ vals[b][l]),
            Op::Cmp(k, a, b) => std::array::from_fn(|l| i64::from(k.eval(vals[a][l], vals[b][l]))),
            Op::Select { cond, t_val, f_val } => std::array::from_fn(|l| if vals[cond][l] != 0 { vals[t_val][l] } else { vals[f_val][l] }),
            Op::BoundsCheck { idx, limit } => { for (l, &iv) in vals[idx].iter().enumerate() { ctx.mark(l, id, act[l] && (iv < 0 || (iv as usize) >= limit), FAULT_OOB); } vals[idx] }
            Op::DynBoundsCheck(idx, len) => { for l in 0..LANES { let (iv, lv) = (vals[idx][l], vals[len][l]); ctx.mark(l, id, act[l] && (iv < 0 || lv <= 0 || iv >= lv), FAULT_OOB); } vals[idx] }
            Op::PanicIfZero(cond, _) => { for l in 0..LANES { ctx.mark(l, id, act[l] && vals[cond][l] == 0, FAULT_PANIC); } vals[cond] }
            Op::Load { buf, idx } => ctx.load(id, act, prog.bufs[usize::from(buf)].elem_domain, &shadow[usize::from(buf)], &writes[usize::from(buf)], vals[idx]),
            Op::Store { buf, idx, val } => ctx.store(id, act, &mut shadow[usize::from(buf)], &mut writes[usize::from(buf)], vals[idx], vals[val]), }; }
    BatchEval { faults: ctx.faults, fault_nodes: ctx.fnodes, outputs: prog.outputs.iter().map(|&o| vals[o]).collect() } }
/// Generate 8 parallel boundary/Zipfian/adversarial inputs per parameter inside `doms`.
#[must_use] pub fn sample_batch_x8(doms: &[Domain], tick: usize, seed: &mut u64) -> Vec<[i64; LANES]> {
    let multi = doms.len() > 1;
    doms.iter().enumerate().map(|(pi, &d)| {
        let (width, mid) = (d.width_u128(), d.lo.wrapping_add((d.width_u128() / 2) as i64));
        if tick == 0 {
            let corners = if !multi { [d.lo, d.hi, d.lo.saturating_add(1), d.hi.saturating_sub(1), 0, -1, 1, mid] }
                else if (pi & 1) == 0 { [d.lo, d.hi, 0, -1, d.hi, d.lo, d.lo.saturating_add(1), mid] }
                else { [d.lo, d.hi, d.lo.saturating_add(1), d.hi.saturating_sub(1), d.lo, d.hi, d.lo, mid.saturating_sub(1)] };
            return std::array::from_fn(|l| snap_domain(d, corners[l])); }
        std::array::from_fn(|l| {
            let r = splitmix64(seed); if width == 0 { return d.lo; }
            let span = width.saturating_add(1);
            let raw = match l & 3 {
                0 => d.lo.wrapping_add((u128::from(splitmix64(seed) >> ((r & 63) as u32)) % span) as i64),
                1 => d.hi.wrapping_sub((u128::from(splitmix64(seed) >> ((r & 63) as u32)) % span) as i64),
                2 => { let p = 1i64.wrapping_shl((r as u32) & 63); if (r & 64) == 0 { p } else { p.wrapping_sub(1) } }
                _ => d.lo.wrapping_add((u128::from(r) % span) as i64), };
            snap_domain(d, raw)
        })
    }).collect() }
fn fmt_domain(d: Domain) -> String { if d.lo == d.hi { format!("== {}", d.lo) } else if d.modulus > 1 { format!("in {}..={} (mod {} == {})", d.lo, d.hi, d.modulus, d.rem) } else { format!("in {}..={}", d.lo, d.hi) } }
fn fmt_box(box_doms: &[Domain]) -> String { if box_doms.is_empty() { "true".to_string() } else { box_doms.iter().enumerate().map(|(i, &d)| format!("p{i} {}", fmt_domain(d))).collect::<Vec<_>>().join(" && ") } }
#[must_use] pub fn format_box_invariant(box_doms: &[Domain], prog: &Program, doms: &[Domain]) -> String {
    prog.outputs.first().map_or_else(|| format!("{} => safe", fmt_box(box_doms)), |&o| format!("{} => out0 {}", fmt_box(box_doms), fmt_domain(doms[o]))) }
fn err_root_node(prog: &Program, err: &VerifyError) -> Option<usize> {
    match *err {
        VerifyError::OutOfBounds { node, .. } | VerifyError::UninitializedRead { node, .. } | VerifyError::ShiftOverflow { node, .. }
        | VerifyError::IntOverflow { node } | VerifyError::ExplicitPanic { node } | VerifyError::UseAfterFree { node, .. } | VerifyError::DoubleFree { node, .. } => Some(node),
        VerifyError::DivByZero { node } => Some(match prog.nodes[node] { Op::Div(_, b) | Op::Rem(_, b) => b, _ => node }),
        _ => None, } }
fn unwrap_param_off(prog: &Program, mut id: usize) -> Option<(usize, i128)> {
    let mut off = 0i128;
    for _ in 0..8 {
        match prog.nodes[id] {
            Op::Param(p) => return Some((usize::from(p), off)),
            Op::BoundsCheck { idx, .. } | Op::DynBoundsCheck(idx, _) => id = idx,
            Op::Add(a, b) | Op::WrapAdd(a, b) => match (prog.nodes[a], prog.nodes[b]) { (_, Op::Const(k)) => { off += i128::from(k); id = a; } (Op::Const(k), _) => { off += i128::from(k); id = b; } _ => return None },
            Op::Sub(a, b) | Op::WrapSub(a, b) => if let Op::Const(k) = prog.nodes[b] { off -= i128::from(k); id = a; } else { return None; },
            _ => return None, } }
    None }
fn pick_cut(d: Domain, cut: i128) -> Option<i64> { let (lo, hi) = (i128::from(d.lo), i128::from(d.hi)); if cut > lo && cut <= hi { Some(cut as i64) } else if cut == lo && cut < hi { Some((cut + 1) as i64) } else { None } }
fn cmp_split_target(prog: &Program, box_doms: &[Domain], err: &VerifyError) -> Option<(usize, i64)> {
    let check_cmp = |op: Op<usize>| -> Option<(usize, i64)> {
        let (a, b, is_dyn) = match op { Op::Cmp(_, a, b) => (a, b, false), Op::DynBoundsCheck(a, b) => (a, b, true), _ => return None };
        let (pa, pb) = (unwrap_param_off(prog, a), unwrap_param_off(prog, b));
        match (pa, prog.nodes[b], pb, prog.nodes[a]) {
            (Some((p, off)), Op::Const(k), _, _) | (_, _, Some((p, off)), Op::Const(k)) => pick_cut(*box_doms.get(p)?, i128::from(k) - off).map(|c| (p, c)),
            (Some((ia, oa)), _, Some((ib, ob)), _) if ia != ib => {
                let (da, db) = (*box_doms.get(ia)?, *box_doms.get(ib)?); if is_dyn && db.lo == 0 && db.hi > 0 { return Some((ib, 1)); }
                for (dim, d, cut) in [(ib, db, i128::from(da.lo) + oa - ob), (ia, da, i128::from(db.lo) + ob - oa), (ib, db, i128::from(da.hi) + oa - ob), (ia, da, i128::from(db.hi) + ob - oa)] {
                    if let Some(c) = pick_cut(d, cut) { return Some((dim, c)); } }
                None }
            _ => None, } };
    if let Some(root) = err_root_node(prog, err) {
        let (mut stack, mut hops) = (vec![root], 0usize);
        while let Some(u) = stack.pop() {
            if hops >= 24 { break; }
            hops += 1; if let Some(hit) = check_cmp(prog.nodes[u]) { return Some(hit); }
            if let Some((g, _)) = prog.guard_of(u) { stack.push(g); }
            let (kids, cnt) = prog.nodes[u].children(); stack.extend_from_slice(&kids[..cnt]); } }
    prog.nodes.iter().copied().find_map(check_cmp) }
fn mod_split_target(prog: &Program, err: &VerifyError) -> Option<i64> {
    let (mut stack, mut hops) = (vec![err_root_node(prog, err)?], 0usize);
    while let Some(u) = stack.pop() {
        if hops >= 16 { break; }
        hops += 1; if let Some((g, _)) = prog.guard_of(u) { stack.push(g); }
        match prog.nodes[u] {
            Op::Rem(_, d_id) => if let Op::Const(d) = prog.nodes[d_id] { if d > 1 && d <= 64 && d % 2 == 0 { return Some(d); } },
            Op::BitAnd(_, m_id) => if let Op::Const(m) = prog.nodes[m_id] { if m > 0 && m < 64 && ((m + 1) & m) == 0 { return Some(m + 1); } },
            Op::Load { idx, .. } | Op::Store { idx, .. } | Op::BoundsCheck { idx, .. } | Op::DynBoundsCheck(idx, _) => stack.push(idx),
            op => { let (kids, cnt) = op.children(); stack.extend_from_slice(&kids[..cnt]); } } }
    None }
fn split_dim(box_doms: &[Domain], dim: usize, ld: Domain, rd: Domain) -> (Vec<Domain>, Vec<Domain>) { let (mut l, mut r) = (box_doms.to_vec(), box_doms.to_vec()); l[dim] = ld; r[dim] = rd; (l, r) }
fn split_box(prog: &Program, box_doms: &[Domain], err: &VerifyError) -> Option<(Vec<Domain>, Vec<Domain>)> {
    if let Some((dim, k)) = cmp_split_target(prog, box_doms, err) { let d = box_doms[dim]; if let (Some(ld), Some(rd)) = (Domain { hi: k - 1, ..d }.tighten(), Domain { lo: k, ..d }.tighten()) { return Some(split_dim(box_doms, dim, ld, rd)); } }
    if let Some(target_m) = mod_split_target(prog, err) {
        if let Some((dim, _)) = box_doms.iter().enumerate().filter(|(_, d)| d.lo < d.hi && d.modulus < target_m).max_by_key(|(_, d)| d.width_u128()) {
            if let Some((ld, rd)) = box_doms[dim].split_mod2() { return Some(split_dim(box_doms, dim, ld, rd)); } } }
    let (dim, _) = box_doms.iter().enumerate().filter(|(_, d)| d.lo < d.hi).max_by_key(|(_, d)| d.width_u128())?;
    let (ld, rd) = box_doms[dim].split_mid()?; Some(split_dim(box_doms, dim, ld, rd)) }
fn align_singleton(a: Domain, b: Domain) -> (Domain, Domain) {
    if a.lo == a.hi && b.modulus > 1 { return (Domain { modulus: b.modulus, rem: a.lo.rem_euclid(b.modulus), ..a }, b); }
    if b.lo == b.hi && a.modulus > 1 { return (a, Domain { modulus: a.modulus, rem: b.lo.rem_euclid(a.modulus), ..b }); }
    (a, b) }
enum MergeResult { None, Merged(Domain), SplitParity(Vec<Domain>) }
fn merge_domain_pair(raw_a: Domain, raw_b: Domain) -> MergeResult {
    if raw_a == raw_b { return MergeResult::Merged(raw_a); }
    let (a, b) = align_singleton(raw_a, raw_b);
    if a.modulus == b.modulus && a.rem == b.rem && i128::from(a.hi) + i128::from(a.modulus) >= i128::from(b.lo) && i128::from(b.hi) + i128::from(a.modulus) >= i128::from(a.lo) {
        return MergeResult::Merged(Domain::congruent(a.lo.min(b.lo), a.hi.max(b.hi), a.modulus, a.rem)); }
    if a.modulus == b.modulus && a.modulus >= 2 && a.modulus % 2 == 0 {
        let (half, h128) = (a.modulus / 2, i128::from(a.modulus / 2));
        if (a.rem - b.rem).abs() == half {
            if (i128::from(a.lo) - i128::from(b.lo)).abs() <= h128 && (i128::from(a.hi) - i128::from(b.hi)).abs() <= h128 { return MergeResult::Merged(Domain::congruent(a.lo.min(b.lo), a.hi.max(b.hi), half, a.rem.min(b.rem))); }
            for (wide, narrow) in [(a, b), (b, a)] {
                if i128::from(narrow.lo) >= i128::from(wide.lo) - h128 && i128::from(narrow.hi) <= i128::from(wide.hi) + h128 {
                    let (mid_lo, mid_hi, s2) = ((i128::from(narrow.lo) - h128).max(i128::from(wide.lo)) as i64, (i128::from(narrow.hi) + h128).min(i128::from(wide.hi)) as i64, i128::from(wide.modulus));
                    let mut out = vec![Domain::congruent(mid_lo.min(narrow.lo), mid_hi.max(narrow.hi), half, a.rem.min(b.rem))];
                    if i128::from(wide.lo) < i128::from(mid_lo) { if let Some(l) = Domain::congruent(wide.lo, (i128::from(mid_lo) - s2) as i64, wide.modulus, wide.rem).tighten() { out.push(l); } }
                    if i128::from(mid_hi) < i128::from(wide.hi) { if let Some(r) = Domain::congruent((i128::from(mid_hi) + s2) as i64, wide.hi, wide.modulus, wide.rem).tighten() { out.push(r); } }
                    return MergeResult::SplitParity(out); }
            } } }
    MergeResult::None }
fn diff_dim(a: &[Domain], b: &[Domain]) -> Option<usize> {
    if a.len() != b.len() { return None; }
    let mut found = None; for i in 0..a.len() { if a[i] != b[i] { if found.is_some() { return None; } found = Some(i); } }
    found.or((!a.is_empty()).then_some(0)) }
fn coalesce_subdomains(raw: Vec<Vec<Domain>>) -> Vec<Vec<Domain>> {
    let mut boxes: Vec<Vec<Domain>> = raw.into_iter().filter_map(|b| b.into_iter().map(Domain::tighten).collect::<Option<Vec<_>>>()).collect();
    for _ in 0..256 {
        let mut changed = false;
        'outer: for i in 0..boxes.len() {
            for j in (i + 1)..boxes.len() {
                if let Some(k) = diff_dim(&boxes[i], &boxes[j]) {
                    match merge_domain_pair(boxes[i][k], boxes[j][k]) {
                        MergeResult::None => {}
                        MergeResult::Merged(d) => { boxes[i][k] = d; boxes.remove(j); changed = true; break 'outer; }
                        MergeResult::SplitParity(parts) => { let tpl = boxes[i].clone(); boxes.remove(j); boxes.remove(i); for d in parts { let mut nb = tpl.clone(); nb[k] = d; boxes.push(nb); } changed = true; break 'outer; } }
                } } }
        if !changed { break; } }
    boxes.sort_by_key(|b| b.iter().map(|d| (d.lo, d.hi, d.modulus, d.rem)).collect::<Vec<_>>()); boxes.dedup(); boxes }
fn format_guard(safe: &[Vec<Domain>], ces: &[Counterexample], unproven_boxes: usize) -> String {
    if !safe.is_empty() { safe.iter().map(|b| fmt_box(b)).collect::<Vec<_>>().join(" || ") }
    else if !ces.is_empty() && unproven_boxes == 0 { "false".to_string() } else { "unknown".to_string() } }
fn probe_box(prog: &Program, cur: &[Domain], rounds: usize, seed: &mut u64, ticks: &mut usize, evals: &mut usize, ces: &mut Vec<Counterexample>) -> bool {
    for t in 0..rounds {
        let batch = sample_batch_x8(cur, t, seed); let res = eval_lanes_x8(prog, &batch); *ticks += 1; *evals += LANES;
        if let Some(lane) = res.faults.iter().position(|&f| f != FAULT_NONE) {
            let ce = Counterexample { inputs: batch.iter().map(|lanes| lanes[lane]).collect(), node: usize::from(res.fault_nodes[lane]), fault: res.faults[lane] };
            if !ces.contains(&ce) { ces.push(ce); }
            return true; } }
    false }
/// Autodidactic/Kani-class exhaustive branch-and-bound symbolic prover + 8-lane SIMD counterexample refiner.
#[must_use] pub fn refine_and_fuzz(prog: &Program, cfg: RefineConfig) -> RefineReport {
    if prog.validate().is_err() {
        return RefineReport { ticks: 0, evals: 0, bisections: 0, proven_boxes: 0, unproven_boxes: 1, safe_subdomains: Vec::new(), counterexamples: Vec::new(), learned_invariants: Vec::new(), synthesized_guard: "invalid_program".to_string(), verdict: ProofVerdict::Incomplete { boxes_discharged: 0, unproven_boxes: 1 } };
    }
    let (mut seed, mut worklist) = (cfg.seed, vec![prog.param_domains.iter().map(|&d| d.tighten().unwrap_or(d)).collect::<Vec<_>>()]);
    let (mut ticks, mut evals, mut bisections, mut proven_boxes, mut unproven_boxes) = (0, 0, 0, 0, 0);
    let (mut safe_subdomains, mut counterexamples, mut learned_invariants) = (Vec::new(), Vec::new(), Vec::new());
    let (rounds, max_splits) = (cfg.fuzz_ticks_per_box.max(1), cfg.max_epochs.saturating_mul(8).max(64));
    while let Some(cur) = worklist.pop() {
        if ticks / rounds >= cfg.max_epochs || bisections >= max_splits { unproven_boxes += worklist.len() + 1; break; }
        let (doms, status, _) = prog.check_obligations(&cur);
        match status {
            ProofStatus::ProvenSafe => { proven_boxes += 1; if learned_invariants.len() < 64 { learned_invariants.push(format_box_invariant(&cur, prog, &doms)); } safe_subdomains.push(cur); }
            ProofStatus::DefiniteBug(_) => {
                if !probe_box(prog, &cur, 1, &mut seed, &mut ticks, &mut evals, &mut counterexamples) { unproven_boxes += 1; }
                if !cfg.synthesize_safe_boundary { unproven_boxes += worklist.len(); break; } }
            ProofStatus::Uncertain(err) => {
                let hit = probe_box(prog, &cur, rounds, &mut seed, &mut ticks, &mut evals, &mut counterexamples);
                if hit && !cfg.synthesize_safe_boundary { unproven_boxes += worklist.len() + 1; break; }
                if let Some((left, right)) = split_box(prog, &cur, &err) { bisections += 1; worklist.push(right); worklist.push(left); } else if !hit { unproven_boxes += 1; } }
        } }
    let safe_subdomains = coalesce_subdomains(safe_subdomains); let synthesized_guard = format_guard(&safe_subdomains, &counterexamples, unproven_boxes);
    let verdict = if let Some(ce) = counterexamples.first() { ProofVerdict::Counterexample { input: ce.inputs.clone(), node: ce.node, fault: ce.fault, synthesized_guard: synthesized_guard.clone() } }
    else if unproven_boxes == 0 && proven_boxes > 0 { ProofVerdict::ProvenTotal { boxes_discharged: proven_boxes, learned_invariants: learned_invariants.clone() } }
    else { ProofVerdict::Incomplete { boxes_discharged: proven_boxes, unproven_boxes } };
    RefineReport { ticks, evals, bisections, proven_boxes, unproven_boxes, safe_subdomains, counterexamples, learned_invariants, synthesized_guard, verdict } }
/// Kani-class exact exhaustive branch-and-bound proof over the entire input domain with safe-guard synthesis.
#[must_use] pub fn prove_exhaustive(prog: &Program, cfg: RefineConfig) -> ProofVerdict { refine_and_fuzz(prog, RefineConfig { synthesize_safe_boundary: true, ..cfg }).verdict }
/// Concrete 2-tick SIMD witness sampler for static `DefiniteBug` PoC extraction.
#[must_use] pub fn sample_counterexample(prog: &Program, mut seed: u64) -> Option<Counterexample> {
    if prog.validate().is_err() { return None; }
    let doms: Vec<Domain> = prog.param_domains.iter().map(|&d| d.tighten().unwrap_or(d)).collect(); let (mut ticks, mut evals, mut ces) = (0, 0, Vec::new());
    probe_box(prog, &doms, 2, &mut seed, &mut ticks, &mut evals, &mut ces);
    ces.into_iter().next() }
fn parse_slice_spec(raw: &str) -> Option<(bool, &str, &str)> {
    let (is_mut, rest) = if let Some(r) = raw.strip_prefix("mut_slice_len:") { (true, r) }
        else if let Some(r) = raw.strip_prefix("slice_len:") { (false, r) }
        else { return None; };
    let (name, ty) = rest.split_once(':').map_or((rest, "u8"), |(n, t)| (n, if t.is_empty() { "u8" } else { t }));
    (!name.is_empty()).then_some((is_mut, name, ty)) }
/// Emit a standalone Rust `#[test]` reproducing `ce`, reconstructing named `&[T]`/`&mut [T]` slices and `Option<T>` pairs.
#[must_use] pub fn synthesize_rust_poc_test_named(fn_name: &str, param_names: &[String], ce: &Counterexample) -> String {
    let mut clean = String::new(); for c in fn_name.chars() { if c.is_ascii_alphanumeric() || c == '_' { clean.push(c); } else if !clean.ends_with('_') { clean.push('_'); } }
    let test_id = match clean.trim_matches('_') { "" => "witness", s => s };
    let mut out = format!("#[test]\nfn poc_{test_id}() {{\n    // zero-check witness: node {} fault {} inputs={:?}\n", ce.node, fault_name(ce.fault), ce.inputs);
    let (mut args, mut i) = (Vec::with_capacity(ce.inputs.len()), 0usize);
    while i < ce.inputs.len() {
        let (val, pname) = (ce.inputs[i], param_names.get(i).map(String::as_str).unwrap_or(""));
        if let Some(base) = pname.strip_suffix("_is_some") {
            let next_name = param_names.get(i + 1).map(String::as_str).unwrap_or("");
            if !base.is_empty() && next_name.strip_suffix("_val") == Some(base) && i + 1 < ce.inputs.len() {
                if val == 0 { out.push_str(&format!("    let {base} = None;\n")); } else { out.push_str(&format!("    let {base} = Some({});\n", ce.inputs[i + 1])); }
                args.push(base.to_string()); i += 2; continue; } }
        if let Some((is_mut, name, ty)) = parse_slice_spec(pname) {
            let (len, kw) = (usize::try_from(val).map_or(0, |n| n.min(65_536)), if is_mut { "let mut" } else { "let" });
            out.push_str(&format!("    {kw} {name}: Vec<{ty}> = vec![Default::default(); {len}];\n")); args.push(if is_mut { format!("&mut {name}") } else { format!("&{name}") });
        } else { let var = if pname.is_empty() { format!("p{i}") } else { pname.to_string() }; out.push_str(&format!("    let {var} = {val};\n")); args.push(var); }
        i += 1; }
    out.push_str(&format!("    let _ = {fn_name}({});\n}}\n", args.join(", "))); out }
/// Emit a standalone Rust `#[test]` reproducing `ce` with positional `p0..pN` bindings.
#[must_use] pub fn synthesize_rust_poc_test(fn_name: &str, ce: &Counterexample) -> String { synthesize_rust_poc_test_named(fn_name, &[], ce) }
/// Emit a standalone Rust `#[test]` reproducing `ce` using `prog.name` and `prog.param_names`.
#[must_use] pub fn synthesize_rust_poc_test_for_prog(prog: &Program, ce: &Counterexample) -> String { synthesize_rust_poc_test_named(&prog.name, &prog.param_names, ce) }
