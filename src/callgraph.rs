use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::{Path, PathBuf};
use crate::abstract_eval::{ArchProfile, Domain, Program};
use crate::rust_fe::{tokenize_rust, LoweredFn, PocParam, RustProofReport, Tok, MAX_SYM_SLICE_LEN};
use crate::simd_fuzz::RefineConfig;
use crate::verify_program;
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CallerArgSummary { pub dom: Option<Domain>, pub slice_len: Option<Domain>, pub opt_is_some: Option<Domain>, pub pow2: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuppressedHelper { pub fn_name: String, pub caller_count: usize, pub reason: String }
#[derive(Clone, Debug, Default)]
pub struct CallGraph { pub fn_names: Vec<String>, pub edge_count: usize }
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ConstSet { vals: [i64; 8], len: u8 }
impl ConstSet {
    fn single(v: i64) -> Self { Self { vals: [v, 0, 0, 0, 0, 0, 0, 0], len: 1 } }
    fn as_slice(&self) -> &[i64] { self.vals.get(..usize::from(self.len).min(8)).unwrap_or(&[]) }
    fn push(&mut self, v: i64) -> bool {
        if self.as_slice().contains(&v) { return true; }
        let Some(slot) = self.vals.get_mut(usize::from(self.len)) else { return false; };
        *slot = v; self.len = self.len.saturating_add(1); true
    }
    fn union(mut self, o: Self) -> Option<Self> { for &v in o.as_slice() { if !self.push(v) { return None; } } Some(self) }
    fn exclude(self, bad: i64) -> Self { let mut out = Self::default(); for &v in self.as_slice() { if v != bad { let _ = out.push(v); } } out }
    fn dom(&self) -> Option<Domain> { let s = self.as_slice(); let &f = s.first()?; let (lo, hi) = s.iter().fold((f, f), |(a, b), &v| (a.min(v), b.max(v))); Some(Domain::range(lo, hi)) }
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ArgFact { s: CallerArgSummary, consts: Option<ConstSet>, nz_dom: Option<Domain>, from_param: Option<(usize, bool)> }
impl ArgFact {
    fn exact(v: i64) -> Self { Self { s: CallerArgSummary { dom: Some(Domain::exact(v)), ..CallerArgSummary::default() }, consts: Some(ConstSet::single(v)), nz_dom: (v != 0).then(|| Domain::exact(v)), from_param: None } }
    fn opt(is_some: i64, val: Option<Domain>) -> Self { Self { s: CallerArgSummary { dom: val, opt_is_some: Some(Domain::exact(is_some)), ..CallerArgSummary::default() }, ..Self::default() } }
    fn slice(d: Domain) -> Self { Self { s: CallerArgSummary { slice_len: Some(d), ..CallerArgSummary::default() }, ..Self::default() } }
    fn jdom(a: Option<Domain>, b: Option<Domain>) -> Option<Domain> { a.zip(b).map(|(x, y)| Domain::range(x.lo.min(y.lo), x.hi.max(y.hi))) }
    fn idom(a: Option<Domain>, b: Domain) -> Option<Domain> { a.map_or(Some(b), |x| x.try_meet(b)) }
    fn join(self, o: Self) -> Self {
        Self {
            s: CallerArgSummary { dom: Self::jdom(self.s.dom, o.s.dom), slice_len: Self::jdom(self.s.slice_len, o.s.slice_len), opt_is_some: Self::jdom(self.s.opt_is_some, o.s.opt_is_some), pow2: self.s.pow2 && o.s.pow2 },
            consts: self.consts.zip(o.consts).and_then(|(x, y)| x.union(y)), nz_dom: Self::jdom(self.nz_dom, o.nz_dom), from_param: (self.from_param == o.from_param).then_some(self.from_param).flatten(),
        }
    }
    fn apply_tz(self) -> Self {
        if let Some(cs) = self.consts.filter(|c| c.len > 0 && c.as_slice().iter().all(|&v| v > 0)) {
            let (mut out, mut ok) = (ConstSet::default(), true); for &v in cs.as_slice() { ok &= out.push(i64::from((v as u64).trailing_zeros())); }
            let dom = out.dom(); return Self { s: CallerArgSummary { dom, ..CallerArgSummary::default() }, consts: ok.then_some(out), nz_dom: dom, from_param: None };
        }
        if let Some(d) = self.s.pow2.then_some(self.s.dom).flatten().filter(|d| d.lo >= 2 && d.hi >= d.lo) {
            let (lo, hi) = (i64::from((d.lo as u64).next_power_of_two().trailing_zeros()), i64::from(63u32.saturating_sub((d.hi as u64).leading_zeros())));
            if lo <= hi { let dom = Domain::range(lo, hi); return Self { s: CallerArgSummary { dom: Some(dom), ..CallerArgSummary::default() }, consts: None, nz_dom: Some(dom), from_param: None }; }
        }
        Self::default()
    }
    fn resolve(self, cin: Option<&[ArgFact]>) -> Self {
        let Some((pidx, tz)) = self.from_param else { return self; }; let Some(mut m) = cin.and_then(|v| v.get(pidx)).copied() else { return if tz { self.apply_tz() } else { self }; };
        m.from_param = None; if let Some(d) = self.s.dom { m.s.dom = Self::idom(m.s.dom, d); }
        if let Some(d) = self.s.slice_len { m.s.slice_len = Self::idom(m.s.slice_len, d); }
        if let Some(d) = self.s.opt_is_some { m.s.opt_is_some = Self::idom(m.s.opt_is_some, d); }
        if let Some(d) = self.nz_dom { m.nz_dom = Self::idom(m.nz_dom, d); }
        if self.s.pow2 { m.s.pow2 = true; }
        if let Some(cs) = self.consts { m.consts = Some(cs); }
        if tz { m.apply_tz() } else { m }
    }
}
struct CgFn { file_idx: usize, short_name: String, self_ty: Option<String>, full_name: String, vis: u8, has_self: bool, params: Vec<String>, body: (usize, usize) }
struct CallSite { caller: usize, file_idx: usize, qual: Option<String>, short: String, is_method: bool, is_self: bool, args: Vec<ArgFact> }
fn skip_bal(toks: &[Tok], mut i: usize, end: usize, open: &str, close: &str) -> usize {
    if !matches!(toks.get(i), Some(Tok::Sym(s)) if *s == open) { return i; }
    let (mut d, is_ang) = (1usize, close == ">"); i = i.saturating_add(1);
    while i < end && d > 0 {
        match toks.get(i) {
            Some(Tok::Sym(s)) if *s == open => d = d.saturating_add(1),
            Some(Tok::Sym(s)) if *s == close => d = d.saturating_sub(1),
            Some(Tok::Sym(">>")) if is_ang => d = d.saturating_sub(2), _ => {}
        }
        i = i.saturating_add(1);
    }
    i
}
fn parse_attr_is_test(toks: &[Tok], i: &mut usize, end: usize) -> bool {
    *i = i.saturating_add(1); let inner = matches!(toks.get(*i), Some(Tok::Sym("!"))); if inner { *i = i.saturating_add(1); }
    let s = *i; *i = skip_bal(toks, *i, end, "[", "]"); let sl = toks.get(s.saturating_add(1)..(*i).saturating_sub(1)).unwrap_or(&[]);
    !inner && matches!(sl.first(), Some(Tok::Ident(n)) if n == "test" || (n == "cfg" && sl.iter().any(|t| matches!(t, Tok::Ident(w) if w == "test" || w == "kani"))))
}
fn parse_fn_params(toks: &[Tok], mut i: usize, end: usize) -> (bool, Vec<String>) {
    let (mut has_self, mut params) = (false, Vec::new());
    while i < end {
        while matches!(toks.get(i), Some(Tok::Sym("#"))) { let _ = parse_attr_is_test(toks, &mut i, end); }
        let (pstart, mut d) = (i, 0usize);
        while i < end {
            match toks.get(i) { Some(Tok::Sym("(" | "[" | "{" | "<")) => d = d.saturating_add(1), Some(Tok::Sym(")" | "]" | "}" | ">")) => d = d.saturating_sub(1), Some(Tok::Sym(">>")) => d = d.saturating_sub(2), Some(Tok::Sym(",")) if d == 0 => break, _ => {} }
            i = i.saturating_add(1);
        }
        let seg = toks.get(pstart..i).unwrap_or(&[]); if i < end { i = i.saturating_add(1); }
        if seg.iter().take(4).any(|t| matches!(t, Tok::Ident(w) if w == "self")) { has_self = true; }
        else if let Some(c) = seg.iter().position(|t| matches!(t, Tok::Sym(":"))) {
            params.push(seg.get(..c).and_then(|l| l.iter().rev().find_map(|t| if let Tok::Ident(w) = t { (w != "mut" && w != "ref").then(|| w.clone()) } else { None })).unwrap_or_else(|| "_".to_string()));
        }
    }
    (has_self, params)
}
fn scan_cg_block(toks: &[Tok], start: usize, end: usize, file_idx: usize, self_ty: Option<&str>, skip_cfg_test: bool, out: &mut Vec<CgFn>) {
    let (mut i, mut is_test, mut vis) = (start, false, 0u8);
    while i < end {
        match toks.get(i) {
            Some(Tok::Doc(_)) => i = i.saturating_add(1),
            Some(Tok::Sym("#")) => { is_test |= parse_attr_is_test(toks, &mut i, end); }
            Some(Tok::Ident(w)) if w == "pub" => { i = i.saturating_add(1); if matches!(toks.get(i), Some(Tok::Sym("("))) { i = skip_bal(toks, i, end, "(", ")"); vis = 1; } else { vis = 2; } }
            Some(Tok::Ident(w)) if matches!(w.as_str(), "async" | "unsafe" | "const" | "default") => i = i.saturating_add(1),
            Some(Tok::Ident(w)) if w == "extern" => { i = i.saturating_add(1); if matches!(toks.get(i), Some(Tok::Sym("\""))) { i = i.saturating_add(1); } }
            Some(Tok::Ident(w)) if w == "mod" || w == "impl" => {
                let (is_impl, t) = (w == "impl", is_test); is_test = false; vis = 0; i = i.saturating_add(1); if is_impl { i = skip_bal(toks, i, end, "<", ">"); }
                let (mut ty_name, mut after_for) = (None::<String>, false);
                while i < end && !matches!(toks.get(i), Some(Tok::Sym("{" | ";"))) {
                    if is_impl {
                        match toks.get(i) {
                            Some(Tok::Ident(n)) if n == "for" => { after_for = true; ty_name = None; i = i.saturating_add(1); }
                            Some(Tok::Ident(n)) if n == "where" => { while i < end && !matches!(toks.get(i), Some(Tok::Sym("{" | ";"))) { i = i.saturating_add(1); } }
                            Some(Tok::Ident(n)) if !matches!(n.as_str(), "dyn" | "mut" | "const") => { if ty_name.is_none() || after_for { ty_name = Some(n.clone()); } i = i.saturating_add(1); }
                            Some(Tok::Sym("<")) => i = skip_bal(toks, i, end, "<", ">"), Some(Tok::Sym("(")) => i = skip_bal(toks, i, end, "(", ")"), _ => i = i.saturating_add(1),
                        }
                    } else { i = i.saturating_add(1); }
                }
                if matches!(toks.get(i), Some(Tok::Sym("{"))) {
                    let be = skip_bal(toks, i, end, "{", "}");
                    if !(skip_cfg_test && t) { scan_cg_block(toks, i.saturating_add(1), be.saturating_sub(1), file_idx, if is_impl { ty_name.as_deref() } else { None }, skip_cfg_test, out); }
                    i = be;
                } else { i = i.saturating_add(1).min(end); }
            }
            Some(Tok::Ident(w)) if w == "fn" => {
                let (t, v) = (is_test, vis); is_test = false; vis = 0; i = i.saturating_add(1); let Some(Tok::Ident(short)) = toks.get(i) else { continue; };
                let short = short.clone(); i = skip_bal(toks, i.saturating_add(1), end, "<", ">"); if !matches!(toks.get(i), Some(Tok::Sym("("))) { continue; }
                let pend = skip_bal(toks, i, end, "(", ")"); let (has_self, params) = parse_fn_params(toks, i.saturating_add(1), pend.saturating_sub(1)); i = pend;
                while i < end && !matches!(toks.get(i), Some(Tok::Sym("{" | ";"))) { i = match toks.get(i) { Some(Tok::Sym("(")) => skip_bal(toks, i, end, "(", ")"), Some(Tok::Sym("[")) => skip_bal(toks, i, end, "[", "]"), _ => i.saturating_add(1) }; }
                if matches!(toks.get(i), Some(Tok::Sym("{"))) {
                    let be = skip_bal(toks, i, end, "{", "}");
                    if !(skip_cfg_test && t) {
                        let full = self_ty.map_or_else(|| short.clone(), |st| format!("{st}::{short}"));
                        out.push(CgFn { file_idx, short_name: short, self_ty: self_ty.map(str::to_string), full_name: full, vis: v, has_self, params, body: (i.saturating_add(1), be.saturating_sub(1)) });
                    }
                    i = be;
                } else { i = i.saturating_add(1).min(end); }
            }
            Some(Tok::Sym("{")) => { is_test = false; vis = 0; i = skip_bal(toks, i, end, "{", "}"); }
            _ => { is_test = false; vis = 0; i = i.saturating_add(1); }
        }
    }
}
fn find_top_pred(toks: &[Tok], s: usize, e: usize, pred: impl Fn(&Tok, Option<&Tok>) -> bool) -> Option<usize> {
    let (mut i, mut d) = (s, 0usize);
    while i < e {
        if let Some(t) = toks.get(i) {
            if d == 0 && pred(t, toks.get(i.saturating_add(1))) { return Some(i); }
            match t { Tok::Sym("(" | "[" | "{") => d = d.saturating_add(1), Tok::Sym(")" | "]" | "}") => d = d.saturating_sub(1), _ => {} }
        }
        i = i.saturating_add(1);
    }
    None
}
fn find_top(toks: &[Tok], s: usize, e: usize, sym: &str) -> Option<usize> { find_top_pred(toks, s, e, |t, _| matches!(t, Tok::Sym(x) if *x == sym)) }
fn block_diverges(toks: &[Tok], s: usize, e: usize) -> bool {
    find_top_pred(toks, s, e, |t, nxt| matches!(t, Tok::Ident(w) if matches!(w.as_str(), "return" | "break" | "continue") || (matches!(w.as_str(), "panic" | "unreachable") && matches!(nxt, Some(Tok::Sym("!")))))).is_some()
}
fn parse_int_slice(t: &[Tok]) -> Option<i64> { match t { [Tok::Int(v, _)] => Some(*v), [Tok::Sym("-"), Tok::Int(v, _)] => v.checked_neg(), _ => None } }
fn strip_parens(toks: &[Tok], mut s: usize, mut e: usize) -> (usize, usize) {
    while s < e && matches!(toks.get(s), Some(Tok::Sym("("))) && skip_bal(toks, s, e, "(", ")") == e { s = s.saturating_add(1); e = e.saturating_sub(1); }
    (s, e)
}
fn apply_cmp_var(env: &mut BTreeMap<String, ArgFact>, var: &str, op: &str, k: i64, is_len: bool) {
    let f = env.entry(var.to_string()).or_default();
    if is_len {
        let m = MAX_SYM_SLICE_LEN as i64;
        let d = match op { "==" => Domain::exact(k), "<" => Domain::range(0, k.saturating_sub(1)), "<=" => Domain::range(0, k), ">" => Domain::range(k.saturating_add(1), m), ">=" => Domain::range(k, m), _ => return };
        f.s.slice_len = ArgFact::idom(f.s.slice_len, d); return;
    }
    match op {
        "==" => { f.s.dom = Some(Domain::exact(k)); f.consts = Some(ConstSet::single(k)); if k != 0 { f.nz_dom = Some(Domain::exact(k)); } }
        "!=" => {
            if let Some(cs) = f.consts { let n = cs.exclude(k); f.consts = Some(n); if let Some(d) = n.dom() { f.s.dom = Some(d); } }
            if k == 0 { if let Some(nz) = f.nz_dom { f.s.dom = Some(nz); } else if let Some(d) = f.s.dom.filter(|d| d.lo == 0 && d.hi >= 1) { f.s.dom = Some(Domain::range(1, d.hi)); } }
        }
        "<" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(i64::MIN, k.saturating_sub(1))),
        "<=" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(i64::MIN, k)),
        ">" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(k.saturating_add(1), i64::MAX)),
        ">=" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(k, i64::MAX)), _ => {}
    }
}
fn parse_range_contains(toks: &[Tok]) -> Option<(String, i64, i64)> {
    let dot = toks.iter().position(|t| matches!(t, Tok::Sym(".")))?; if !matches!(toks.get(dot.saturating_add(1)), Some(Tok::Ident(w)) if w == "contains") { return None; }
    let (rs, re) = strip_parens(toks, 0, dot); let rt = toks.get(rs..re)?;
    let (a, b) = if let Some(p) = rt.iter().position(|t| matches!(t, Tok::Sym("..="))) { (parse_int_slice(rt.get(..p)?)?, parse_int_slice(rt.get(p.saturating_add(1)..)?)?) }
        else if let Some(p) = rt.iter().position(|t| matches!(t, Tok::Sym(".."))) { (parse_int_slice(rt.get(..p)?)?, parse_int_slice(rt.get(p.saturating_add(1)..)?)?.checked_sub(1)?) }
        else { return None; };
    let (as_, ae) = (dot.saturating_add(2), skip_bal(toks, dot.saturating_add(2), toks.len(), "(", ")"));
    match toks.get(as_.saturating_add(1)..ae.saturating_sub(1))? { [Tok::Sym("&"), Tok::Ident(v)] | [Tok::Ident(v)] => Some((v.clone(), a, b)), _ => None }
}
fn refine_cond(env: &mut BTreeMap<String, ArgFact>, toks: &[Tok], s: usize, e: usize, truth: bool) {
    let (s, e) = strip_parens(toks, s, e); if s >= e { return; }
    if let Some(p) = find_top(toks, s, e, "&&") {
        if truth { refine_cond(env, toks, s, p, true); refine_cond(env, toks, p.saturating_add(1), e, true); return; }
        let ((ls, le), (rs, re)) = (strip_parens(toks, s, p), strip_parens(toks, p.saturating_add(1), e)); let (a, b) = (toks.get(ls..le).unwrap_or(&[]), toks.get(rs..re).unwrap_or(&[]));
        for (x, y) in [(a, b), (b, a)] {
            if let [Tok::Ident(v), Tok::Sym("!="), Tok::Int(0, _)] = x {
                if let Some((v2, lo, hi)) = y.strip_prefix(&[Tok::Sym("!")]).and_then(parse_range_contains).filter(|(v2, lo, hi)| v == v2 && lo <= hi) {
                    let f = env.entry(v2).or_default(); f.s.dom = ArgFact::idom(f.s.dom, Domain::range(lo.min(0), hi.max(0))); f.nz_dom = ArgFact::idom(f.nz_dom, Domain::range(lo, hi));
                }
            }
        }
        return;
    }
    if let Some(p) = find_top(toks, s, e, "||") { if !truth { refine_cond(env, toks, s, p, false); refine_cond(env, toks, p.saturating_add(1), e, false); } return; }
    if matches!(toks.get(s), Some(Tok::Sym("!"))) { refine_cond(env, toks, s.saturating_add(1), e, !truth); return; }
    let sl = toks.get(s..e).unwrap_or(&[]);
    if let Some((v, lo, hi)) = parse_range_contains(sl).filter(|(_, lo, hi)| truth && lo <= hi) { let f = env.entry(v).or_default(); f.s.dom = ArgFact::idom(f.s.dom, Domain::range(lo, hi)); return; }
    if let [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] = sl {
        if m == "is_empty" { apply_cmp_var(env, v, if truth { "==" } else { ">=" }, i64::from(!truth), true); }
        else if m == "is_power_of_two" && truth { env.entry(v.clone()).or_default().s.pow2 = true; }
        return;
    }
    for op in ["==", "!=", "<=", ">=", "<", ">"] {
        if let Some(p) = find_top(toks, s, e, op) {
            let eff = if truth { op } else { match op { "==" => "!=", "!=" => "==", "<" => ">=", "<=" => ">", ">" => "<=", _ => "<" } };
            let (lhs, rhs) = (toks.get(s..p).unwrap_or(&[]), toks.get(p.saturating_add(1)..e).unwrap_or(&[]));
            if let Some(k) = parse_int_slice(rhs) {
                match lhs { [Tok::Ident(v)] => apply_cmp_var(env, v, eff, k, false), [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "len" => apply_cmp_var(env, v, eff, k, true), _ => {} }
            }
            return;
        }
    }
}
struct ExtractCtx<'a> { toks: &'a [Tok], caller: usize, file_idx: usize, calls: &'a mut Vec<CallSite> }
impl<'a> ExtractCtx<'a> {
    fn eval_args(&mut self, s: usize, e: usize, env: &BTreeMap<String, ArgFact>) -> Vec<ArgFact> {
        let (mut out, mut i) = (Vec::new(), s); while i < e { let j = find_top(self.toks, i, e, ",").unwrap_or(e); if j > i { out.push(self.eval_expr(i, j, env)); } i = j.saturating_add(1); }
        out
    }
    fn eval_match(&mut self, mut i: usize, e: usize, env: &BTreeMap<String, ArgFact>, tn: usize) -> (ArgFact, Vec<ArgFact>) {
        let ss = i; while i < e && !matches!(self.toks.get(i), Some(Tok::Sym("{"))) { i = i.saturating_add(1); }
        let svar = match self.toks.get(ss..i).unwrap_or(&[]) { [Tok::Ident(v)] => Some(v.clone()), _ => None }; let lim = skip_bal(self.toks, i, e, "{", "}").saturating_sub(1);
        let (mut j, mut acc, mut tacc, mut seen) = (i.saturating_add(1), None::<ArgFact>, vec![None::<ArgFact>; tn], Vec::<i64>::new());
        while j < lim {
            let Some(arr) = find_top(self.toks, j, lim, "=>") else { break; }; let pat = self.toks.get(j..arr).unwrap_or(&[]); if let Some(k) = parse_int_slice(pat) { seen.push(k); }
            let arm_s = arr.saturating_add(1);
            let arm_e = if matches!(self.toks.get(arm_s), Some(Tok::Sym("{"))) {
                let be = skip_bal(self.toks, arm_s, lim, "{", "}"); j = if matches!(self.toks.get(be), Some(Tok::Sym(","))) { be.saturating_add(1) } else { be }; be
            } else { let k = find_top(self.toks, arm_s, lim, ",").unwrap_or(lim); j = k.saturating_add(1).min(lim); k }; let mut aenv = env.clone();
            if matches!(pat, [Tok::Ident(w)] if w == "_") { if let Some(ref sv) = svar { for &k in &seen { apply_cmp_var(&mut aenv, sv, "!=", k, false); } } }
            let divs = block_diverges(self.toks, arm_s, arm_e);
            if tn > 0 && !divs && matches!(self.toks.get(arm_s), Some(Tok::Sym("("))) {
                let (a2, b2) = strip_parens(self.toks, arm_s, arm_e); for (slot, ef) in tacc.iter_mut().zip(self.eval_args(a2, b2, &aenv)) { *slot = Some(slot.map_or(ef, |p| p.join(ef))); }
            } else {
                let af = if matches!(self.toks.get(arm_s), Some(Tok::Sym("{"))) { self.scan_block(arm_s.saturating_add(1), arm_e.saturating_sub(1), &mut aenv) } else { self.eval_expr(arm_s, arm_e, &aenv) };
                if !divs { acc = Some(acc.map_or(af, |p| p.join(af))); }
            }
        }
        (acc.unwrap_or_default(), tacc.into_iter().map(Option::unwrap_or_default).collect())
    }
    fn scan_if(&mut self, s: usize, e: usize, env: &mut BTreeMap<String, ArgFact>, as_expr: bool) -> (usize, ArgFact) {
        let mut j = s.saturating_add(1); while j < e && !matches!(self.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); }
        let _ = self.eval_expr(s.saturating_add(1), j, env); let t_end = skip_bal(self.toks, j, e, "{", "}");
        let mut tenv = env.clone(); refine_cond(&mut tenv, self.toks, s.saturating_add(1), j, true);
        let (t_val, t_div) = (self.scan_block(j.saturating_add(1), t_end.saturating_sub(1), &mut tenv), block_diverges(self.toks, j.saturating_add(1), t_end.saturating_sub(1)));
        if matches!(self.toks.get(t_end), Some(Tok::Ident(w)) if w == "else") {
            let mut eenv = env.clone(); refine_cond(&mut eenv, self.toks, s.saturating_add(1), j, false); let es = t_end.saturating_add(1);
            let (ep, ev, ed) = if matches!(self.toks.get(es), Some(Tok::Ident(w)) if w == "if") { let (p, v) = self.scan_if(es, e, &mut eenv, as_expr); (p, v, false) }
                else if matches!(self.toks.get(es), Some(Tok::Sym("{"))) { let ee = skip_bal(self.toks, es, e, "{", "}"); (ee, self.scan_block(es.saturating_add(1), ee.saturating_sub(1), &mut eenv), block_diverges(self.toks, es.saturating_add(1), ee.saturating_sub(1))) }
                else { (es, ArgFact::default(), false) };
            if !as_expr { if t_div && !ed { *env = eenv; } else if ed && !t_div { *env = tenv; } }
            return (ep, if t_div { ev } else if ed { t_val } else { t_val.join(ev) });
        }
        if !as_expr {
            if t_div { refine_cond(env, self.toks, s.saturating_add(1), j, false); }
            else { for (k, tv) in tenv { if let Some(ov) = env.get(&k).copied().filter(|&ov| ov != tv) { env.insert(k, ov.join(tv)); } } }
        }
        (t_end, ArgFact::default())
    }
    fn eval_expr(&mut self, s: usize, e: usize, env: &BTreeMap<String, ArgFact>) -> ArgFact {
        let (s, e) = strip_parens(self.toks, s, e); if s >= e { return ArgFact::default(); }
        if matches!(self.toks.get(s), Some(Tok::Ident(w)) if w == "if") { let mut tmp = env.clone(); return self.scan_if(s, e, &mut tmp, true).1; }
        if matches!(self.toks.get(s), Some(Tok::Ident(w)) if w == "match") { return self.eval_match(s.saturating_add(1), e, env, 0).0; }
        if let Some(ap) = find_top_pred(self.toks, s, e, |t, _| matches!(t, Tok::Ident(w) if w == "as")) { return self.eval_expr(s, ap, env); }
        let sl = self.toks.get(s..e).unwrap_or(&[]); if let Some(v) = parse_int_slice(sl) { return ArgFact::exact(v); }
        if matches!(sl, [Tok::Ident(w)] if w == "None") { return ArgFact::opt(0, None); }
        if let [Tok::Ident(w)] = sl { return env.get(w).copied().unwrap_or_default(); }
        if matches!(sl.first(), Some(Tok::Ident(w)) if w == "Some") && matches!(sl.get(1), Some(Tok::Sym("("))) && skip_bal(self.toks, s.saturating_add(1), e, "(", ")") == e {
            return ArgFact::opt(1, self.eval_expr(s.saturating_add(2), e.saturating_sub(1), env).s.dom);
        }
        if let [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] = sl {
            if m == "trailing_zeros" { let b = env.get(v).copied().unwrap_or_default(); return if let Some((p, false)) = b.from_param { ArgFact { from_param: Some((p, true)), ..b } } else { b.apply_tz() }; }
        }
        if matches!(sl.first(), Some(Tok::Sym("&"))) && matches!(sl.last(), Some(Tok::Sym("]"))) {
            if let Some(lb) = (s..e).rev().find(|&k| matches!(self.toks.get(k), Some(Tok::Sym("[")))) {
                let inner = self.toks.get(lb.saturating_add(1)..e.saturating_sub(1)).unwrap_or(&[]);
                if let Some(rp) = inner.iter().position(|t| matches!(t, Tok::Sym(".." | "..="))) {
                    let lo = if rp == 0 { Some(0) } else { inner.get(..rp).and_then(parse_int_slice) };
                    if let (Some(a), Some(b)) = (lo, inner.get(rp.saturating_add(1)..).and_then(parse_int_slice)) {
                        let len = b.saturating_sub(a).saturating_add(i64::from(matches!(inner.get(rp), Some(Tok::Sym("..="))))); if len >= 0 { return ArgFact::slice(Domain::exact(len)); }
                    }
                }
            }
        }
        let mut i = s;
        while i < e {
            if let Some(Tok::Ident(name)) = self.toks.get(i) {
                let mut ci = i.saturating_add(1);
                if matches!(self.toks.get(ci), Some(Tok::Sym("::"))) && matches!(self.toks.get(ci.saturating_add(1)), Some(Tok::Sym("<"))) { ci = skip_bal(self.toks, ci.saturating_add(1), e, "<", ">"); }
                if !matches!(name.as_str(), "if" | "else" | "while" | "for" | "match" | "loop" | "return" | "let" | "Some" | "Ok" | "Err") && matches!(self.toks.get(ci), Some(Tok::Sym("("))) {
                    let ce = skip_bal(self.toks, ci, e, "(", ")"); let args = self.eval_args(ci.saturating_add(1), ce.saturating_sub(1), env);
                    let is_method = i > s && matches!(self.toks.get(i.saturating_sub(1)), Some(Tok::Sym(".")));
                    let is_self = is_method && i >= s.saturating_add(2) && matches!(self.toks.get(i.saturating_sub(2)), Some(Tok::Ident(w)) if w == "self");
                    let qual = (!is_method && i >= s.saturating_add(2) && matches!(self.toks.get(i.saturating_sub(1)), Some(Tok::Sym("::")))).then(|| match self.toks.get(i.saturating_sub(2)) { Some(Tok::Ident(q)) => Some(q.clone()), _ => None }).flatten();
                    self.calls.push(CallSite { caller: self.caller, file_idx: self.file_idx, qual, short: name.clone(), is_method, is_self, args }); i = ce; continue;
                }
            }
            if matches!(self.toks.get(i), Some(Tok::Sym("{"))) { let be = skip_bal(self.toks, i, e, "{", "}"); let mut sub = env.clone(); let _ = self.scan_block(i.saturating_add(1), be.saturating_sub(1), &mut sub); i = be; continue; }
            i = i.saturating_add(1);
        }
        ArgFact::default()
    }
    fn scan_block(&mut self, s: usize, e: usize, env: &mut BTreeMap<String, ArgFact>) -> ArgFact {
        let (mut i, mut last) = (s, ArgFact::default());
        while i < e {
            match self.toks.get(i) {
                Some(Tok::Ident(w)) if w == "let" => {
                    i = i.saturating_add(1); if matches!(self.toks.get(i), Some(Tok::Ident(m)) if m == "mut") { i = i.saturating_add(1); }
                    let mut vars = Vec::new();
                    if matches!(self.toks.get(i), Some(Tok::Sym("("))) {
                        let pe = skip_bal(self.toks, i, e, "(", ")");
                        for t in self.toks.get(i.saturating_add(1)..pe.saturating_sub(1)).unwrap_or(&[]) { if let Tok::Ident(v) = t { if v != "mut" { vars.push(v.clone()); } } }
                        i = pe;
                    } else if let Some(Tok::Ident(v)) = self.toks.get(i) { vars.push(v.clone()); i = i.saturating_add(1); }
                    let (mut eq, mut d) = (i, 0usize);
                    while eq < e { match self.toks.get(eq) { Some(Tok::Sym("(" | "[" | "{" | "<")) => d = d.saturating_add(1), Some(Tok::Sym(")" | "]" | "}" | ">")) => d = d.saturating_sub(1), Some(Tok::Sym(">>")) => d = d.saturating_sub(2), Some(Tok::Sym("=" | ";")) if d == 0 => break, _ => {} } eq = eq.saturating_add(1); }
                    if matches!(self.toks.get(eq), Some(Tok::Sym("="))) {
                        let rs = eq.saturating_add(1); let re = find_top(self.toks, rs, e, ";").unwrap_or(e);
                        if vars.len() > 1 && matches!(self.toks.get(rs), Some(Tok::Ident(m)) if m == "match") {
                            let tf = self.eval_match(rs.saturating_add(1), re, env, vars.len()).1; for (v, f) in vars.into_iter().zip(tf) { env.insert(v, f); }
                        } else if let Some(v) = vars.into_iter().next() { let f = self.eval_expr(rs, re, env); env.insert(v, f); }
                        else { let _ = self.eval_expr(rs, re, env); }
                        i = re.saturating_add(1).min(e);
                    } else { i = eq.saturating_add(1).min(e); }
                    last = ArgFact::default();
                }
                Some(Tok::Ident(w)) if w == "if" => { let (np, v) = self.scan_if(i, e, env, false); i = np; last = v; }
                Some(Tok::Ident(w)) if w == "match" => { let mut j = i.saturating_add(1); while j < e && !matches!(self.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); } let be = skip_bal(self.toks, j, e, "{", "}"); last = self.eval_match(i.saturating_add(1), be, env, 0).0; i = be; }
                Some(Tok::Ident(w)) if matches!(w.as_str(), "assert" | "debug_assert") && matches!(self.toks.get(i.saturating_add(1)), Some(Tok::Sym("!"))) => {
                    let pe = skip_bal(self.toks, i.saturating_add(2), e, "(", ")");
                    let ce = find_top(self.toks, i.saturating_add(3), pe.saturating_sub(1), ",").unwrap_or_else(|| pe.saturating_sub(1));
                    refine_cond(env, self.toks, i.saturating_add(3), ce, true); i = pe; last = ArgFact::default();
                }
                Some(Tok::Ident(w)) if matches!(w.as_str(), "while" | "for" | "loop") => {
                    let mut j = i.saturating_add(1); while j < e && !matches!(self.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); }
                    let be = skip_bal(self.toks, j, e, "{", "}"); let mut lenv = env.clone(); if w == "while" { refine_cond(&mut lenv, self.toks, i.saturating_add(1), j, true); }
                    let _ = self.scan_block(j.saturating_add(1), be.saturating_sub(1), &mut lenv); i = be; last = ArgFact::default();
                }
                Some(Tok::Ident(v)) if matches!(self.toks.get(i.saturating_add(1)), Some(Tok::Sym("="))) => {
                    let re = find_top(self.toks, i.saturating_add(2), e, ";").unwrap_or(e);
                    let f = self.eval_expr(i.saturating_add(2), re, env); env.insert(v.clone(), f); i = re.saturating_add(1).min(e); last = ArgFact::default();
                }
                Some(Tok::Sym("{")) => { let be = skip_bal(self.toks, i, e, "{", "}"); let mut sub = env.clone(); last = self.scan_block(i.saturating_add(1), be.saturating_sub(1), &mut sub); i = be; }
                _ => { let se = find_top(self.toks, i, e, ";").unwrap_or(e); let v = self.eval_expr(i, se, env); last = if se < e { ArgFact::default() } else { v }; i = se.saturating_add(1).min(e); }
            }
        }
        last
    }
}
fn find_workspace_root(dir: &Path) -> (Option<PathBuf>, bool) {
    let base = if dir.is_file() { dir.parent().unwrap_or(dir) } else { dir }; let mut cur = Some(base);
    for _ in 0..4 {
        if let Some(anc) = cur { if std::fs::read_to_string(anc.join("Cargo.toml")).is_ok_and(|s| s.contains("[workspace]")) { return (Some(anc.to_path_buf()), false); } cur = anc.parent(); }
    }
    let cd = if base.join("Cargo.toml").is_file() { Some(base) } else if base.file_name().and_then(|s| s.to_str()) == Some("src") && base.parent().is_some_and(|p| p.join("Cargo.toml").is_file()) { base.parent() } else { None };
    let Some(toml) = cd.and_then(|c| std::fs::read_to_string(c.join("Cargo.toml")).ok()) else { return (None, false); }; let Some(cd) = cd else { return (None, false); };
    if toml.contains(".workspace = true") || toml.contains(".workspace=true") {
        let mut anc = cd.parent();
        for _ in 0..2 { if let Some(a) = anc { if std::fs::read_dir(a).ok().map_or(0, |rd| rd.flatten().filter(|e| e.path().join("Cargo.toml").is_file()).count()) >= 2 { return (Some(a.to_path_buf()), false); } anc = a.parent(); } }
        return (None, false);
    }
    (None, toml.contains("[package]") && !cd.join("src/main.rs").is_file() && !cd.join("main.rs").is_file() && !toml.contains("publish = false") && !toml.contains("publish=false"))
}
fn collect_sibling_rs(root: &Path, skip: &[String], skip_tests: bool, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(root) else { return; };
    for entry in rd.flatten() {
        let (p, nm) = (entry.path(), entry.file_name()); let nms = nm.to_str().unwrap_or("");
        if p.is_dir() {
            if !(matches!(nms, "target" | ".git" | "node_modules" | "bench" | "benches" | "examples") || skip_tests && matches!(nms, "tests" | "test")) { collect_sibling_rs(&p, skip, skip_tests, out); }
        } else if p.extension().and_then(|s| s.to_str()) == Some("rs") && !skip.iter().any(|s| nms == s || p.ends_with(s)) { out.push(p); }
    }
}
fn narrow_program(lf: &LoweredFn, facts: &[ArgFact]) -> Option<Program> {
    let (mut prog, mut narrowed) = (lf.prog.clone(), false);
    let off = usize::from(lf.params.first().is_some_and(|p| matches!(p, PocParam::Struct { name, .. } | PocParam::Enum { name, .. } if name == "self_val")));
    for (ai, fact) in facts.iter().enumerate() {
        let Some(pp) = lf.params.get(ai.saturating_add(off)) else { continue; };
        let mut apply = |pidx: usize, d: Domain| { if let Some(slot) = prog.param_domains.get_mut(pidx) { if let Some(nd) = slot.try_meet(d).filter(|&nd| nd != *slot) { *slot = nd; narrowed = true; } } };
        match *pp {
            PocParam::Scalar { pidx, .. } => if let Some(d) = fact.s.dom { apply(pidx, d); },
            PocParam::Slice { pidx, .. } => if let Some(d) = fact.s.slice_len { apply(pidx, d); },
            PocParam::Opt { is_some, val, .. } => {
                if let Some(d) = fact.s.opt_is_some { apply(is_some, d); }
                if let Some(d) = fact.s.dom { apply(val, d); }
            }
            _ => {}
        }
    }
    narrowed.then_some(prog)
}
fn visible_to(f: &CgFn, c_file: usize, n_target: usize) -> bool { f.file_idx == c_file || f.vis == 2 || (f.vis >= 1 && f.file_idx < n_target && c_file < n_target) }
fn resolve_call_targets(c: &CallSite, fns: &[CgFn], n_target: usize) -> Vec<usize> {
    let ar = c.args.len();
    if c.is_method {
        if c.is_self {
            let ct = fns.get(c.caller).and_then(|f| f.self_ty.as_deref());
            let same: Vec<usize> = fns.iter().enumerate().filter(|(_, f)| f.file_idx == c.file_idx && f.has_self && f.short_name == c.short && f.params.len() == ar && f.self_ty.as_deref() == ct).map(|(i, _)| i).collect();
            if !same.is_empty() { return same; }
        }
        return fns.iter().enumerate().filter(|(_, f)| f.has_self && f.short_name == c.short && f.params.len() == ar && visible_to(f, c.file_idx, n_target)).map(|(i, _)| i).collect();
    }
    if let Some(ref q) = c.qual {
        let bt: Vec<usize> = fns.iter().enumerate().filter(|(_, f)| !f.has_self && f.short_name == c.short && f.params.len() == ar && f.self_ty.as_deref() == Some(q.as_str())).map(|(i, _)| i).collect();
        if !bt.is_empty() { return bt; }
        return fns.iter().enumerate().filter(|(_, f)| !f.has_self && f.self_ty.is_none() && f.short_name == c.short && f.params.len() == ar && visible_to(f, c.file_idx, n_target)).map(|(i, _)| i).collect();
    }
    let loc: Vec<usize> = fns.iter().enumerate().filter(|(_, f)| f.file_idx == c.file_idx && !f.has_self && f.self_ty.is_none() && f.short_name == c.short && f.params.len() == ar).map(|(i, _)| i).collect();
    if !loc.is_empty() { return loc; }
    fns.iter().enumerate().filter(|(_, f)| !f.has_self && f.self_ty.is_none() && f.short_name == c.short && f.params.len() == ar && visible_to(f, c.file_idx, n_target)).map(|(i, _)| i).collect()
}
fn extract_all_calls(fns: &[CgFn], all_toks: &[Vec<Tok>]) -> Vec<CallSite> {
    let mut calls = Vec::new();
    for (fid, f) in fns.iter().enumerate() {
        let Some(toks) = all_toks.get(f.file_idx) else { continue; };
        let mut env: BTreeMap<String, ArgFact> = f.params.iter().enumerate().map(|(pi, n)| (n.clone(), ArgFact { from_param: Some((pi, false)), ..ArgFact::default() })).collect();
        let mut ec = ExtractCtx { toks, caller: fid, file_idx: f.file_idx, calls: &mut calls }; let _ = ec.scan_block(f.body.0, f.body.1, &mut env);
    }
    calls
}
fn pub_pat(f: &CgFn) -> String { f.self_ty.as_ref().map_or_else(|| format!("{}(", f.short_name), |st| format!("{st}::{}(", f.short_name)) }
pub(crate) fn apply_interprocedural_reachability(
    dir: Option<&Path>, files: &[PathBuf], file_srcs: &[String], reports: &mut [RustProofReport],
    failed_lowered: &[(usize, usize, LoweredFn)], skip: &[String], (skip_cfg_test, profile, cfg): (bool, ArchProfile, RefineConfig),
) {
    if failed_lowered.is_empty() { return; }
    let ((ws_root, standalone_lib), n_target) = (dir.map_or((None, false), find_workspace_root), file_srcs.len());
    let mut all_toks: Vec<Vec<Tok>> = file_srcs.iter().map(|s| tokenize_rust(s)).collect(); let mut fns: Vec<CgFn> = Vec::new();
    for (fi, toks) in all_toks.iter().enumerate() { scan_cg_block(toks, 0, toks.len(), fi, None, skip_cfg_test, &mut fns); }
    if let Some(root) = ws_root {
        let (mut known, mut pool, mut frontier) = (files.iter().cloned().collect::<BTreeSet<_>>(), Vec::new(), BTreeSet::<String>::new());
        collect_sibling_rs(&root, skip, skip_cfg_test, &mut pool);
        for &(ridx, fidx, _) in failed_lowered {
            if let Some(fail) = reports.get(ridx).and_then(|r| r.failed.get(fidx)) {
                if let Some(cf) = fns.iter().find(|f| f.file_idx == ridx && f.full_name == fail.fn_name && f.vis == 2) { frontier.insert(format!("{}(", cf.short_name)); }
            }
        }
        for c in extract_all_calls(&fns, &all_toks) { if frontier.contains(&format!("{}(", c.short)) { if let Some(cf) = fns.get(c.caller).filter(|f| f.vis == 2) { frontier.insert(pub_pat(cf)); } } }
        let mut seen = frontier.clone();
        for _ in 0..3 {
            if frontier.is_empty() || all_toks.len() >= n_target.saturating_add(128) { break; }
            let pats: Vec<String> = frontier.iter().cloned().collect(); frontier.clear();
            for p in &pool {
                if known.contains(p) || all_toks.len() >= n_target.saturating_add(128) { continue; }
                let Ok(src) = std::fs::read_to_string(p) else { continue; }; if !pats.iter().any(|pat| src.contains(pat.as_str())) { continue; }
                known.insert(p.clone()); let (fi, toks, prev) = (all_toks.len(), tokenize_rust(&src), fns.len()); scan_cg_block(&toks, 0, toks.len(), fi, None, skip_cfg_test, &mut fns);
                for nf in fns.get(prev..).unwrap_or(&[]) { if nf.vis == 2 { let k = pub_pat(nf); if seen.insert(k.clone()) { frontier.insert(k); } } }
                all_toks.push(toks);
            }
        }
    }
    let mut incoming: Vec<Vec<(usize, Vec<ArgFact>)>> = vec![Vec::new(); fns.len()];
    for c in extract_all_calls(&fns, &all_toks) { for tgt in resolve_call_targets(&c, &fns, n_target) { if tgt != c.caller { if let Some(slot) = incoming.get_mut(tgt) { slot.push((c.caller, c.args.clone())); } } } }
    let mut in_params: Vec<Option<Vec<ArgFact>>> = vec![None; fns.len()];
    for _ in 0..6 {
        let mut next = in_params.clone();
        for (tgt, edges) in incoming.iter().enumerate() {
            let mut acc: Option<Vec<ArgFact>> = None;
            for (caller, raw) in edges {
                let res: Vec<ArgFact> = raw.iter().map(|a| a.resolve(in_params.get(*caller).and_then(|o| o.as_deref()))).collect();
                acc = Some(acc.map_or(res.clone(), |p| p.into_iter().zip(res).map(|(x, y)| x.join(y)).collect()));
            }
            if let Some(slot) = next.get_mut(tgt) { *slot = acc; }
        }
        in_params = next;
    }
    let (mut to_sup, mut traces) = (BTreeMap::<(usize, usize), SuppressedHelper>::new(), BTreeMap::<(usize, usize), Vec<String>>::new());
    for &(ridx, fidx, ref lf) in failed_lowered {
        let Some(fail) = reports.get(ridx).and_then(|r| r.failed.get(fidx)) else { continue; };
        let Some(fid) = fns.iter().position(|f| f.file_idx == ridx && f.full_name == fail.fn_name) else { traces.insert((ridx, fidx), vec![fail.fn_name.clone()]); continue; };
        let edges = incoming.get(fid).map_or(&[][..], Vec::as_slice);
        if edges.is_empty() || (standalone_lib && fns.get(fid).is_some_and(|f| f.vis == 2)) { traces.insert((ridx, fidx), vec![fail.fn_name.clone()]); continue; }
        if in_params.get(fid).and_then(|o| o.as_deref()).and_then(|j| narrow_program(lf, j)).is_some_and(|np| verify_program(&np, profile, cfg).is_ok()) {
            to_sup.insert((ridx, fidx), SuppressedHelper { fn_name: fail.fn_name.clone(), caller_count: edges.len(), reason: format!("all {} callers discharge precondition", edges.len()) }); continue;
        }
        let (mut q, mut vis, mut best) = (VecDeque::new(), BTreeSet::from([fid]), vec![fid]);
        for (caller, raw) in edges {
            let res: Vec<ArgFact> = raw.iter().map(|a| a.resolve(in_params.get(*caller).and_then(|o| o.as_deref()))).collect();
            if !narrow_program(lf, &res).is_some_and(|np| verify_program(&np, profile, cfg).is_ok()) && vis.insert(*caller) { q.push_back((*caller, vec![fid, *caller])); }
        }
        while let Some((cur, path)) = q.pop_front() {
            if path.len() > best.len() { best = path.clone(); }
            let cur_in = incoming.get(cur).map_or(&[][..], Vec::as_slice); if cur_in.is_empty() || fns.get(cur).is_some_and(|f| f.short_name == "main") || path.len() >= 12 { best = path; break; }
            for &(prev, _) in cur_in { if vis.insert(prev) { let mut np = path.clone(); np.push(prev); q.push_back((prev, np)); } }
        }
        traces.insert((ridx, fidx), best.into_iter().rev().filter_map(|id| fns.get(id).map(|f| f.full_name.clone())).collect());
    }
    for (ridx, rep) in reports.iter_mut().enumerate() {
        let mut kept = Vec::with_capacity(rep.failed.len());
        for (fidx, mut fail) in std::mem::take(&mut rep.failed).into_iter().enumerate() {
            if let Some(sup) = to_sup.remove(&(ridx, fidx)) { rep.suppressed_guarded.push(sup); }
            else {
                if let Some(ch) = traces.remove(&(ridx, fidx)) {
                    if let Some(ref mut poc) = fail.poc_test { *poc = format!("// call-chain: {}\n{poc}", ch.join(" -> ")); }
                    fail.entrypoint_trace = Some(ch);
                }
                kept.push(fail);
            }
        }
        rep.failed = kept;
    }
}
