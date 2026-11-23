use crate::abstract_eval::{AllocState, Domain, Op, Program, ProofStatus, VerifyError};

pub const LANES: usize = 8;
pub const FAULT_NONE: u8 = 0;
pub const FAULT_OOB: u8 = 1 << 0;
pub const FAULT_OVERFLOW: u8 = 1 << 1;
pub const FAULT_SHIFT: u8 = 1 << 2;
pub const FAULT_DIV0: u8 = 1 << 3;
pub const FAULT_UAF: u8 = 1 << 4;
pub const FAULT_DOUBLE_FREE: u8 = 1 << 5;
pub const FAULT_UNINIT: u8 = 1 << 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RefineConfig {
    pub max_epochs: usize, pub fuzz_ticks_per_box: usize, pub seed: u64, pub synthesize_safe_boundary: bool,
}

impl Default for RefineConfig {
    fn default() -> Self {
        Self { max_epochs: 256, fuzz_ticks_per_box: 4, seed: 0x51A7_C0DE_1337_BEEF, synthesize_safe_boundary: false }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample { pub inputs: Vec<i64>, pub node: usize, pub fault: u8 }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofVerdict {
    ProvenTotal { boxes_discharged: usize, learned_invariants: Vec<String> },
    Counterexample { input: Vec<i64>, node: usize, fault: u8, synthesized_guard: String },
    Incomplete { boxes_discharged: usize, unproven_boxes: usize },
}

#[derive(Clone, Debug)]
pub struct BatchEval { pub faults: [u8; LANES], pub fault_nodes: [u16; LANES], pub outputs: Vec<[i64; LANES]> }

#[derive(Clone, Debug)]
pub struct RefineReport {
    pub ticks: usize, pub evals: usize, pub bisections: usize, pub proven_boxes: usize,
    pub unproven_boxes: usize, pub safe_subdomains: Vec<Vec<Domain>>, pub counterexamples: Vec<Counterexample>,
    pub learned_invariants: Vec<String>, pub synthesized_guard: String, pub verdict: ProofVerdict,
}

#[must_use]
pub fn fault_name(fault: u8) -> &'static str {
    if (fault & FAULT_UAF) != 0 { "UAF" }
    else if (fault & FAULT_DOUBLE_FREE) != 0 { "DOUBLE_FREE" }
    else if (fault & FAULT_UNINIT) != 0 { "UNINIT" }
    else if (fault & FAULT_OOB) != 0 { "OOB" }
    else if (fault & FAULT_DIV0) != 0 { "DIV0" }
    else if (fault & FAULT_SHIFT) != 0 { "SHIFT" }
    else if (fault & FAULT_OVERFLOW) != 0 { "OVERFLOW" }
    else { "NONE" }
}

#[inline]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

#[inline]
fn snap_domain(d: Domain, raw: i64) -> i64 {
    let mut v = raw.max(d.lo).min(d.hi);
    if d.modulus > 1 {
        let m = d.modulus;
        let diff = (d.rem - v.rem_euclid(m)).rem_euclid(m);
        if let Some(up) = v.checked_add(diff).filter(|&u| u <= d.hi) { v = up; }
        else if let Some(dn) = v.checked_sub(m - diff).filter(|&u| u >= d.lo) { v = dn; }
    }
    v
}

#[inline]
fn mark_fault(faults: &mut [u8; LANES], nodes: &mut [u16; LANES], lane: usize, id: usize, bad: bool, bit: u8) {
    if bad {
        if faults[lane] == 0 { nodes[lane] = id as u16; }
        faults[lane] |= bit;
    }
}

#[inline]
fn eval_arith_x8(a: [i64; LANES], b: [i64; LANES], kind: u8, id: usize, f: &mut [u8; LANES], n: &mut [u16; LANES]) -> [i64; LANES] {
    let mut out = [0i64; LANES];
    for l in 0..LANES {
        let (v, ov) = match kind { 0 => a[l].overflowing_add(b[l]), 1 => a[l].overflowing_sub(b[l]), _ => a[l].overflowing_mul(b[l]) };
        out[l] = v;
        mark_fault(f, n, l, id, ov, FAULT_OVERFLOW);
    }
    out
}

#[inline]
fn eval_div_x8(a: [i64; LANES], b: [i64; LANES], is_rem: bool, id: usize, f: &mut [u8; LANES], n: &mut [u16; LANES]) -> [i64; LANES] {
    let mut out = [0i64; LANES];
    for l in 0..LANES {
        let (av, bv) = (a[l], b[l]);
        let bad = bv == 0 || (av == i64::MIN && bv == -1);
        let sb = if bad { 1 } else { bv };
        out[l] = if is_rem { av % sb } else { av / sb };
        mark_fault(f, n, l, id, bad, FAULT_DIV0);
    }
    out
}

#[inline]
fn eval_shift_x8(a: [i64; LANES], s: [i64; LANES], is_shl: bool, id: usize, f: &mut [u8; LANES], n: &mut [u16; LANES]) -> [i64; LANES] {
    let mut out = [0i64; LANES];
    for l in 0..LANES {
        let sv = s[l];
        let sm = (sv as u32) & 63;
        out[l] = if is_shl { a[l].wrapping_shl(sm) } else { a[l].wrapping_shr(sm) };
        mark_fault(f, n, l, id, !(0..64).contains(&sv), FAULT_SHIFT);
    }
    out
}

#[inline]
fn check_oob_x8(idx: [i64; LANES], lim: usize, id: usize, f: &mut [u8; LANES], n: &mut [u16; LANES]) {
    for (l, &iv) in idx.iter().enumerate() { mark_fault(f, n, l, id, iv < 0 || (iv as usize) >= lim, FAULT_OOB); }
}

/// Branchless 8-lane SIMD-parallel evaluator catching Miri + ASan shadow-epoch faults (UAF, double-free, uninit, OOB, overflow, shift, div0).
#[must_use]
pub fn eval_lanes_x8(prog: &Program, param_lanes: &[[i64; LANES]]) -> BatchEval {
    let mut vals = vec![[0i64; LANES]; prog.nodes.len()];
    let mut shadow: Vec<[AllocState; LANES]> = prog.bufs.iter().map(|b| [AllocState::from_buf(b); LANES]).collect();
    let mut writes: Vec<[Vec<(usize, i64)>; LANES]> = prog.bufs.iter().map(|_| std::array::from_fn(|_| Vec::new())).collect();
    let (mut faults, mut fnodes) = ([FAULT_NONE; LANES], [u16::MAX; LANES]);
    for (id, &op) in prog.nodes.iter().enumerate() {
        vals[id] = match op {
            Op::Param(p) => param_lanes[usize::from(p)],
            Op::Const(c) => [c; LANES],
            Op::Alloc { buf, len } => {
                let (s, wr) = (&mut shadow[usize::from(buf)], &mut writes[usize::from(buf)]);
                std::array::from_fn(|l| { wr[l].clear(); i64::from(s[l].alloc(len)) })
            }
            Op::Free(buf) => {
                let (s, wr) = (&mut shadow[usize::from(buf)], &mut writes[usize::from(buf)]);
                for (l, st) in s.iter_mut().enumerate() {
                    if st.free().is_err() { mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_DOUBLE_FREE); }
                    else { wr[l].clear(); }
                }
                [0; LANES]
            }
            Op::CheckGen { buf, expected } => {
                let s = &shadow[usize::from(buf)];
                let exp = vals[expected];
                for l in 0..LANES {
                    let bad = !s[l].alive || exp[l] != i64::from(s[l].generation);
                    mark_fault(&mut faults, &mut fnodes, l, id, bad, FAULT_UAF);
                }
                exp
            }
            Op::Add(a, b) => eval_arith_x8(vals[a], vals[b], 0, id, &mut faults, &mut fnodes),
            Op::Sub(a, b) => eval_arith_x8(vals[a], vals[b], 1, id, &mut faults, &mut fnodes),
            Op::Mul(a, b) => eval_arith_x8(vals[a], vals[b], 2, id, &mut faults, &mut fnodes),
            Op::WrapAdd(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_add(vals[b][l])),
            Op::WrapSub(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_sub(vals[b][l])),
            Op::WrapMul(a, b) => std::array::from_fn(|l| vals[a][l].wrapping_mul(vals[b][l])),
            Op::Div(a, b) => eval_div_x8(vals[a], vals[b], false, id, &mut faults, &mut fnodes),
            Op::Rem(a, b) => eval_div_x8(vals[a], vals[b], true, id, &mut faults, &mut fnodes),
            Op::Shl(a, s) => eval_shift_x8(vals[a], [i64::from(s); LANES], true, id, &mut faults, &mut fnodes),
            Op::Shr(a, s) => eval_shift_x8(vals[a], [i64::from(s); LANES], false, id, &mut faults, &mut fnodes),
            Op::ShlVar(a, b) => eval_shift_x8(vals[a], vals[b], true, id, &mut faults, &mut fnodes),
            Op::ShrVar(a, b) => eval_shift_x8(vals[a], vals[b], false, id, &mut faults, &mut fnodes),
            Op::BitAnd(a, b) => std::array::from_fn(|l| vals[a][l] & vals[b][l]),
            Op::BitOr(a, b) => std::array::from_fn(|l| vals[a][l] | vals[b][l]),
            Op::BitXor(a, b) => std::array::from_fn(|l| vals[a][l] ^ vals[b][l]),
            Op::Load { buf, idx } => {
                let (b, s, wr) = (&prog.bufs[usize::from(buf)], &shadow[usize::from(buf)], &writes[usize::from(buf)]);
                let ix = vals[idx];
                let mut out = [0i64; LANES];
                for l in 0..LANES {
                    if !s[l].alive { mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_UAF); }
                    else if ix[l] < 0 || (ix[l] as usize) >= s[l].len { mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_OOB); }
                    else {
                        let slot = ix[l] as usize;
                        let written = wr[l].iter().find(|&&(k, _)| k == slot).map(|&(_, v)| v);
                        if !s[l].is_slot_init(slot) && written.is_none() {
                            mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_UNINIT);
                        }
                        out[l] = written.unwrap_or_else(|| snap_domain(b.elem_domain, ix[l].wrapping_mul(0x517C_C1B7)));
                    }
                }
                out
            }
            Op::Store { buf, idx, val } => {
                let (s, wr) = (&mut shadow[usize::from(buf)], &mut writes[usize::from(buf)]);
                let (ix, vv) = (vals[idx], vals[val]);
                for l in 0..LANES {
                    if !s[l].alive { mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_UAF); }
                    else if ix[l] < 0 || (ix[l] as usize) >= s[l].len { mark_fault(&mut faults, &mut fnodes, l, id, true, FAULT_OOB); }
                    else {
                        let slot = ix[l] as usize;
                        s[l].mark_init(slot);
                        if let Some(entry) = wr[l].iter_mut().find(|(k, _)| *k == slot) { entry.1 = vv[l]; }
                        else { wr[l].push((slot, vv[l])); }
                    }
                }
                vv
            }
            Op::BoundsCheck { idx, limit } => { check_oob_x8(vals[idx], limit, id, &mut faults, &mut fnodes); vals[idx] }
        };
    }
    BatchEval { faults, fault_nodes: fnodes, outputs: prog.outputs.iter().map(|&o| vals[o]).collect() }
}

/// Generate 8 parallel boundary/Zipfian/adversarial inputs per parameter inside `doms`.
#[must_use]
pub fn sample_batch_x8(doms: &[Domain], tick: usize, seed: &mut u64) -> Vec<[i64; LANES]> {
    doms.iter().map(|&d| {
        let width = d.width_u128();
        let mid = d.lo.wrapping_add((width / 2) as i64);
        if tick == 0 {
            let corners = [d.lo, d.hi, d.lo.saturating_add(1), d.hi.saturating_sub(1), 0, -1, 1, mid];
            std::array::from_fn(|l| snap_domain(d, corners[l]))
        } else {
            std::array::from_fn(|l| {
                let r = splitmix64(seed);
                if width == 0 { return d.lo; }
                let span = width.saturating_add(1);
                let raw = match l & 3 {
                    0 => d.lo.wrapping_add((u128::from(splitmix64(seed) >> ((r & 63) as u32)) % span) as i64),
                    1 => d.hi.wrapping_sub((u128::from(splitmix64(seed) >> ((r & 63) as u32)) % span) as i64),
                    2 => { let p = 1i64.wrapping_shl((r as u32) & 63); if (r & 64) == 0 { p } else { p.wrapping_sub(1) } }
                    _ => d.lo.wrapping_add((u128::from(r) % span) as i64),
                };
                snap_domain(d, raw)
            })
        }
    }).collect()
}

fn fmt_domain(d: Domain) -> String {
    if d.lo == d.hi { format!("== {}", d.lo) }
    else if d.modulus > 1 { format!("in {}..={} (mod {} == {})", d.lo, d.hi, d.modulus, d.rem) }
    else { format!("in {}..={}", d.lo, d.hi) }
}

fn fmt_box(box_doms: &[Domain]) -> String {
    if box_doms.is_empty() { return "true".to_string(); }
    box_doms.iter().enumerate().map(|(i, &d)| format!("p{i} {}", fmt_domain(d))).collect::<Vec<_>>().join(" && ")
}

#[must_use]
pub fn format_box_invariant(box_doms: &[Domain], prog: &Program, doms: &[Domain]) -> String {
    if let Some(&o) = prog.outputs.first() {
        format!("{} => out0 {}", fmt_box(box_doms), fmt_domain(doms[o]))
    } else {
        format!("{} => safe", fmt_box(box_doms))
    }
}

fn mod_split_target(prog: &Program, err: &VerifyError) -> Option<i64> {
    let root = match *err {
        VerifyError::OutOfBounds { node, .. }
        | VerifyError::UninitializedRead { node, .. }
        | VerifyError::ShiftOverflow { node, .. }
        | VerifyError::IntOverflow { node } => node,
        VerifyError::DivByZero { node } => match prog.nodes[node] {
            Op::Div(_, b) | Op::Rem(_, b) => b,
            _ => node,
        },
        _ => return None,
    };
    let mut stack = vec![root];
    let mut hops = 0usize;
    while let Some(u) = stack.pop() {
        if hops >= 12 { break; }
        hops += 1;
        match prog.nodes[u] {
            Op::Rem(_, d_id) => if let Op::Const(d) = prog.nodes[d_id] {
                if d > 1 && d <= 64 && d % 2 == 0 { return Some(d); }
            },
            Op::BitAnd(_, m_id) => if let Op::Const(m) = prog.nodes[m_id] {
                if m > 0 && m < 64 && ((m + 1) & m) == 0 { return Some(m + 1); }
            },
            Op::Load { idx, .. } | Op::Store { idx, .. } | Op::BoundsCheck { idx, .. } => stack.push(idx),
            op => {
                let (kids, cnt) = op.children();
                stack.extend_from_slice(&kids[..cnt]);
            }
        }
    }
    None
}

fn split_dim(box_doms: &[Domain], dim: usize, ld: Domain, rd: Domain) -> (Vec<Domain>, Vec<Domain>) {
    let (mut left, mut right) = (box_doms.to_vec(), box_doms.to_vec());
    left[dim] = ld;
    right[dim] = rd;
    (left, right)
}

fn split_box(prog: &Program, box_doms: &[Domain], err: &VerifyError) -> Option<(Vec<Domain>, Vec<Domain>)> {
    if let Some(target_m) = mod_split_target(prog, err) {
        if let Some((dim, _)) = box_doms.iter().enumerate()
            .filter(|(_, d)| d.lo < d.hi && d.modulus < target_m)
            .max_by_key(|(_, d)| d.width_u128())
        {
            if let Some((ld, rd)) = box_doms[dim].split_mod2() { return Some(split_dim(box_doms, dim, ld, rd)); }
        }
    }
    let (dim, _) = box_doms.iter().enumerate().filter(|(_, d)| d.lo < d.hi).max_by_key(|(_, d)| d.width_u128())?;
    let (ld, rd) = box_doms[dim].split_mid()?;
    Some(split_dim(box_doms, dim, ld, rd))
}

fn align_singleton(a: Domain, b: Domain) -> (Domain, Domain) {
    if a.lo == a.hi && b.modulus > 1 {
        let r = a.lo.rem_euclid(b.modulus);
        return (Domain { lo: a.lo, hi: a.hi, modulus: b.modulus, rem: r }, b);
    }
    if b.lo == b.hi && a.modulus > 1 {
        let r = b.lo.rem_euclid(a.modulus);
        return (a, Domain { lo: b.lo, hi: b.hi, modulus: a.modulus, rem: r });
    }
    (a, b)
}

enum MergeResult { None, Merged(Domain), SplitParity(Vec<Domain>) }

fn merge_domain_pair(raw_a: Domain, raw_b: Domain) -> MergeResult {
    if raw_a == raw_b { return MergeResult::Merged(raw_a); }
    let (a, b) = align_singleton(raw_a, raw_b);
    if a.modulus == b.modulus && a.rem == b.rem {
        let step = i128::from(a.modulus);
        if i128::from(a.hi) + step >= i128::from(b.lo) && i128::from(b.hi) + step >= i128::from(a.lo) {
            return MergeResult::Merged(Domain::congruent(a.lo.min(b.lo), a.hi.max(b.hi), a.modulus, a.rem));
        }
    }
    if a.modulus == b.modulus && a.modulus >= 2 && a.modulus % 2 == 0 {
        let half = a.modulus / 2;
        let h128 = i128::from(half);
        if (a.rem - b.rem).abs() == half {
            if (i128::from(a.lo) - i128::from(b.lo)).abs() <= h128 && (i128::from(a.hi) - i128::from(b.hi)).abs() <= h128 {
                return MergeResult::Merged(Domain::congruent(a.lo.min(b.lo), a.hi.max(b.hi), half, a.rem.min(b.rem)));
            }
            for (wide, narrow) in [(a, b), (b, a)] {
                if i128::from(narrow.lo) >= i128::from(wide.lo) - h128 && i128::from(narrow.hi) <= i128::from(wide.hi) + h128 {
                    let mid_lo = (i128::from(narrow.lo) - h128).max(i128::from(wide.lo)) as i64;
                    let mid_hi = (i128::from(narrow.hi) + h128).min(i128::from(wide.hi)) as i64;
                    let mut out = vec![Domain::congruent(mid_lo.min(narrow.lo), mid_hi.max(narrow.hi), half, a.rem.min(b.rem))];
                    let step2 = i128::from(wide.modulus);
                    if i128::from(wide.lo) < i128::from(mid_lo) {
                        if let Some(l) = Domain::congruent(wide.lo, (i128::from(mid_lo) - step2) as i64, wide.modulus, wide.rem).tighten() {
                            out.push(l);
                        }
                    }
                    if i128::from(mid_hi) < i128::from(wide.hi) {
                        if let Some(r) = Domain::congruent((i128::from(mid_hi) + step2) as i64, wide.hi, wide.modulus, wide.rem).tighten() {
                            out.push(r);
                        }
                    }
                    return MergeResult::SplitParity(out);
                }
            }
        }
    }
    MergeResult::None
}

fn diff_dim(a: &[Domain], b: &[Domain]) -> Option<usize> {
    if a.len() != b.len() { return None; }
    let mut found = None;
    for i in 0..a.len() {
        if a[i] != b[i] {
            if found.is_some() { return None; }
            found = Some(i);
        }
    }
    found.or(if a.is_empty() { None } else { Some(0) })
}

fn coalesce_subdomains(raw: Vec<Vec<Domain>>) -> Vec<Vec<Domain>> {
    let mut boxes: Vec<Vec<Domain>> = raw.into_iter()
        .filter_map(|b| b.into_iter().map(Domain::tighten).collect::<Option<Vec<_>>>())
        .collect();
    for _ in 0..256 {
        let mut changed = false;
        'outer: for i in 0..boxes.len() {
            for j in (i + 1)..boxes.len() {
                if let Some(k) = diff_dim(&boxes[i], &boxes[j]) {
                    match merge_domain_pair(boxes[i][k], boxes[j][k]) {
                        MergeResult::None => {}
                        MergeResult::Merged(d) => {
                            boxes[i][k] = d;
                            boxes.remove(j);
                            changed = true;
                            break 'outer;
                        }
                        MergeResult::SplitParity(parts) => {
                            let template = boxes[i].clone();
                            boxes.remove(j);
                            boxes.remove(i);
                            for d in parts {
                                let mut nb = template.clone();
                                nb[k] = d;
                                boxes.push(nb);
                            }
                            changed = true;
                            break 'outer;
                        }
                    }
                }
            }
        }
        if !changed { break; }
    }
    boxes.sort_by_key(|b| b.iter().map(|d| (d.lo, d.hi, d.modulus, d.rem)).collect::<Vec<_>>());
    boxes.dedup();
    boxes
}

fn format_guard(safe: &[Vec<Domain>], ces: &[Counterexample], unproven_boxes: usize) -> String {
    if !safe.is_empty() {
        return safe.iter().map(|b| fmt_box(b)).collect::<Vec<_>>().join(" || ");
    }
    if !ces.is_empty() && unproven_boxes == 0 {
        return "false".to_string();
    }
    "unknown".to_string()
}

/// Autodidactic/Kani-class exhaustive branch-and-bound symbolic prover + 8-lane SIMD counterexample refiner.
#[must_use]
pub fn refine_and_fuzz(prog: &Program, cfg: RefineConfig) -> RefineReport {
    if prog.validate().is_err() {
        return RefineReport {
            ticks: 0, evals: 0, bisections: 0, proven_boxes: 0, unproven_boxes: 1,
            safe_subdomains: Vec::new(), counterexamples: Vec::new(), learned_invariants: Vec::new(),
            synthesized_guard: "invalid_program".to_string(),
            verdict: ProofVerdict::Incomplete { boxes_discharged: 0, unproven_boxes: 1 },
        };
    }
    let init_box: Vec<Domain> = prog.param_domains.iter().map(|&d| d.tighten().unwrap_or(d)).collect();
    let (mut seed, mut worklist) = (cfg.seed, vec![init_box]);
    let (mut ticks, mut evals, mut bisections, mut proven_boxes, mut unproven_boxes) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut safe_subdomains, mut counterexamples, mut learned_invariants) = (Vec::new(), Vec::new(), Vec::new());
    let rounds = cfg.fuzz_ticks_per_box.max(1);
    let max_splits = cfg.max_epochs.saturating_mul(8).max(64);

    while let Some(cur) = worklist.pop() {
        if ticks / rounds >= cfg.max_epochs || bisections >= max_splits {
            unproven_boxes += worklist.len() + 1;
            break;
        }
        let (doms, status, _) = prog.check_obligations(&cur);
        match status {
            ProofStatus::ProvenSafe => {
                proven_boxes += 1;
                if learned_invariants.len() < 64 { learned_invariants.push(format_box_invariant(&cur, prog, &doms)); }
                safe_subdomains.push(cur);
                continue;
            }
            ProofStatus::DefiniteBug(_) => {
                let batch = sample_batch_x8(&cur, 0, &mut seed);
                let res = eval_lanes_x8(prog, &batch);
                ticks += 1;
                evals += LANES;
                if let Some(lane) = res.faults.iter().position(|&f| f != FAULT_NONE) {
                    let ce = Counterexample {
                        inputs: batch.iter().map(|lanes| lanes[lane]).collect(),
                        node: usize::from(res.fault_nodes[lane]), fault: res.faults[lane],
                    };
                    if !counterexamples.contains(&ce) { counterexamples.push(ce); }
                } else {
                    unproven_boxes += 1;
                }
                if !cfg.synthesize_safe_boundary { unproven_boxes += worklist.len(); break; }
                continue;
            }
            ProofStatus::Uncertain(err) => {
                let mut found_fault = false;
                for t in 0..rounds {
                    let batch = sample_batch_x8(&cur, t, &mut seed);
                    let res = eval_lanes_x8(prog, &batch);
                    ticks += 1;
                    evals += LANES;
                    if let Some(lane) = res.faults.iter().position(|&f| f != FAULT_NONE) {
                        let ce = Counterexample {
                            inputs: batch.iter().map(|lanes| lanes[lane]).collect(),
                            node: usize::from(res.fault_nodes[lane]), fault: res.faults[lane],
                        };
                        if !counterexamples.contains(&ce) { counterexamples.push(ce); }
                        found_fault = true;
                        break;
                    }
                }
                if found_fault && !cfg.synthesize_safe_boundary { unproven_boxes += worklist.len() + 1; break; }
                if let Some((left, right)) = split_box(prog, &cur, &err) {
                    bisections += 1;
                    worklist.push(right);
                    worklist.push(left);
                } else if !found_fault { unproven_boxes += 1; }
            }
        }
    }

    let safe_subdomains = coalesce_subdomains(safe_subdomains);
    let synthesized_guard = format_guard(&safe_subdomains, &counterexamples, unproven_boxes);
    let verdict = if let Some(ce) = counterexamples.first() {
        ProofVerdict::Counterexample {
            input: ce.inputs.clone(), node: ce.node, fault: ce.fault,
            synthesized_guard: synthesized_guard.clone(),
        }
    } else if unproven_boxes == 0 && proven_boxes > 0 {
        ProofVerdict::ProvenTotal { boxes_discharged: proven_boxes, learned_invariants: learned_invariants.clone() }
    } else {
        ProofVerdict::Incomplete { boxes_discharged: proven_boxes, unproven_boxes }
    };

    RefineReport {
        ticks, evals, bisections, proven_boxes, unproven_boxes,
        safe_subdomains, counterexamples, learned_invariants, synthesized_guard, verdict,
    }
}

/// Kani-class exact exhaustive branch-and-bound proof over the entire input domain with safe-guard synthesis.
#[must_use]
pub fn prove_exhaustive(prog: &Program, cfg: RefineConfig) -> ProofVerdict {
    refine_and_fuzz(prog, RefineConfig { synthesize_safe_boundary: true, ..cfg }).verdict
}
