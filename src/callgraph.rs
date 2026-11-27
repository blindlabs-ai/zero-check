use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use crate::abstract_eval::{ArchProfile, Domain, Program};
use crate::rust_fe::{
    audit_utf8_item, collect_utf8_call_witnesses, fn_sig_params, scan_file, skip_bal, tokenize_rust,
    BoundaryMorphism, FileIndex, LoweredFn, PocParam, RustProofReport, Tok, Utf8ParamInit, Utf8Pending, MAX_AST_DEPTH, MAX_SYM_SLICE_LEN, };
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
        *slot = v; self.len = self.len.saturating_add(1); true }
    fn union(mut self, o: Self) -> Option<Self> { for &v in o.as_slice() { if !self.push(v) { return None; } } Some(self) }
    fn exclude(self, bad: i64) -> Self { let mut out = Self::default(); for &v in self.as_slice() { if v != bad { let _ = out.push(v); } } out }
    fn dom(&self) -> Option<Domain> { let s = self.as_slice(); let &f = s.first()?; let (lo, hi) = s.iter().fold((f, f), |(a, b), &v| (a.min(v), b.max(v))); Some(Domain::range(lo, hi)) } }
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
            consts: self.consts.zip(o.consts).and_then(|(x, y)| x.union(y)), nz_dom: Self::jdom(self.nz_dom, o.nz_dom), from_param: (self.from_param == o.from_param).then_some(self.from_param).flatten(), } }
    fn apply_tz(self) -> Self {
        if let Some(cs) = self.consts.filter(|c| c.len > 0 && c.as_slice().iter().all(|&v| v > 0)) {
            let (mut out, mut ok) = (ConstSet::default(), true); for &v in cs.as_slice() { ok &= out.push(i64::from((v as u64).trailing_zeros())); }
            let dom = out.dom(); return Self { s: CallerArgSummary { dom, ..CallerArgSummary::default() }, consts: ok.then_some(out), nz_dom: dom, from_param: None }; }
        if let Some(d) = self.s.pow2.then_some(self.s.dom).flatten().filter(|d| d.lo >= 2 && d.hi >= d.lo) {
            let (lo, hi) = (i64::from((d.lo as u64).next_power_of_two().trailing_zeros()), i64::from(63u32.saturating_sub((d.hi as u64).leading_zeros())));
            if lo <= hi { let dom = Domain::range(lo, hi); return Self { s: CallerArgSummary { dom: Some(dom), ..CallerArgSummary::default() }, consts: None, nz_dom: Some(dom), from_param: None }; } }
        Self::default() }
    fn resolve(self, cin: Option<&[ArgFact]>) -> Self {
        let Some((pidx, tz)) = self.from_param else { return self; }; let Some(mut m) = cin.and_then(|v| v.get(pidx)).copied() else { return if tz { self.apply_tz() } else { self }; };
        m.from_param = None; if let Some(d) = self.s.dom { m.s.dom = Self::idom(m.s.dom, d); }
        if let Some(d) = self.s.slice_len { m.s.slice_len = Self::idom(m.s.slice_len, d); }
        if let Some(d) = self.s.opt_is_some { m.s.opt_is_some = Self::idom(m.s.opt_is_some, d); }
        if let Some(d) = self.nz_dom { m.nz_dom = Self::idom(m.nz_dom, d); }
        if self.s.pow2 { m.s.pow2 = true; }
        if let Some(cs) = self.consts { m.consts = Some(cs); }
        if tz { m.apply_tz() } else { m } } }
struct CgFn { file_idx: usize, item_idx: usize, short_name: String, self_ty: Option<String>, full_name: String, vis: u8, has_self: bool, params: Vec<String>, body: (usize, usize) }
struct CallSite { caller: usize, file_idx: usize, qual: Option<String>, short: String, is_method: bool, is_self: bool, args: Vec<ArgFact> }
fn push_cg_fns(fidx: &FileIndex, toks: &[Tok], file_idx: usize, skip_cfg_test: bool, out: &mut Vec<CgFn>) {
    for (item_idx, item) in fidx.fns.iter().enumerate() {
        if skip_cfg_test && item.is_test { continue; }
        let Some((has_self, params, _, _)) = fn_sig_params(item, toks) else { continue; };
        out.push(CgFn {
            file_idx, item_idx, short_name: item.short_name.clone(), self_ty: item.self_ty.clone(), full_name: item.name.clone(),
            vis: item.vis, has_self, params: params.into_iter().map(|(n, _)| n).collect(), body: item.body,
        }); } }
fn find_top_pred(toks: &[Tok], s: usize, e: usize, pred: impl Fn(&Tok, Option<&Tok>) -> bool) -> Option<usize> {
    let (mut i, mut d) = (s, 0usize);
    while i < e {
        if let Some(t) = toks.get(i) {
            if d == 0 && pred(t, toks.get(i.saturating_add(1))) { return Some(i); }
            match t { Tok::Sym("(" | "[" | "{") => d = d.saturating_add(1), Tok::Sym(")" | "]" | "}") => d = d.saturating_sub(1), _ => {} } }
        i = i.saturating_add(1); }
    None }
fn find_top(toks: &[Tok], s: usize, e: usize, sym: &str) -> Option<usize> { find_top_pred(toks, s, e, |t, _| matches!(t, Tok::Sym(x) if *x == sym)) }
fn block_diverges(toks: &[Tok], s: usize, e: usize) -> bool {
    find_top_pred(toks, s, e, |t, nxt| matches!(t, Tok::Ident(w) if matches!(w.as_str(), "return" | "break" | "continue") || (matches!(w.as_str(), "panic" | "unreachable") && matches!(nxt, Some(Tok::Sym("!")))))).is_some() }
fn parse_int_slice(t: &[Tok]) -> Option<i64> { match t { [Tok::Int(v, _)] => Some(*v), [Tok::Sym("-"), Tok::Int(v, _)] => v.checked_neg(), _ => None } }
fn strip_parens(toks: &[Tok], mut s: usize, mut e: usize) -> (usize, usize) {
    while s < e && matches!(toks.get(s), Some(Tok::Sym("("))) && skip_bal(toks, s, e, "(", ")") == e { s = s.saturating_add(1); e = e.saturating_sub(1); }
    (s, e) }
fn apply_cmp_var(env: &mut BTreeMap<String, ArgFact>, var: &str, op: &str, k: i64, is_len: bool) {
    let f = env.entry(var.to_string()).or_default();
    if is_len {
        let m = MAX_SYM_SLICE_LEN as i64;
        let d = match op { "==" => Domain::exact(k), "<" => Domain::range(0, k.saturating_sub(1)), "<=" => Domain::range(0, k), ">" => Domain::range(k.saturating_add(1), m), ">=" => Domain::range(k, m), _ => return };
        f.s.slice_len = ArgFact::idom(f.s.slice_len, d); return; }
    match op {
        "==" => { f.s.dom = Some(Domain::exact(k)); f.consts = Some(ConstSet::single(k)); if k != 0 { f.nz_dom = Some(Domain::exact(k)); } }
        "!=" => {
            if let Some(cs) = f.consts { let n = cs.exclude(k); f.consts = Some(n); if let Some(d) = n.dom() { f.s.dom = Some(d); } }
            if k == 0 { if let Some(nz) = f.nz_dom { f.s.dom = Some(nz); } else if let Some(d) = f.s.dom.filter(|d| d.lo == 0 && d.hi >= 1) { f.s.dom = Some(Domain::range(1, d.hi)); } } }
        "<" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(i64::MIN, k.saturating_sub(1))),
        "<=" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(i64::MIN, k)),
        ">" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(k.saturating_add(1), i64::MAX)),
        ">=" => f.s.dom = ArgFact::idom(f.s.dom, Domain::range(k, i64::MAX)), _ => {} } }
fn parse_range_contains(toks: &[Tok]) -> Option<(String, i64, i64)> {
    let dot = toks.iter().position(|t| matches!(t, Tok::Sym(".")))?; if !matches!(toks.get(dot.saturating_add(1)), Some(Tok::Ident(w)) if w == "contains") { return None; }
    let (rs, re) = strip_parens(toks, 0, dot); let rt = toks.get(rs..re)?;
    let (a, b) = if let Some(p) = rt.iter().position(|t| matches!(t, Tok::Sym("..="))) { (parse_int_slice(rt.get(..p)?)?, parse_int_slice(rt.get(p.saturating_add(1)..)?)?) }
        else if let Some(p) = rt.iter().position(|t| matches!(t, Tok::Sym(".."))) { (parse_int_slice(rt.get(..p)?)?, parse_int_slice(rt.get(p.saturating_add(1)..)?)?.checked_sub(1)?) }
        else { return None; };
    let (as_, ae) = (dot.saturating_add(2), skip_bal(toks, dot.saturating_add(2), toks.len(), "(", ")"));
    match toks.get(as_.saturating_add(1)..ae.saturating_sub(1))? { [Tok::Sym("&"), Tok::Ident(v)] | [Tok::Ident(v)] => Some((v.clone(), a, b)), _ => None } }
fn refine_cond(env: &mut BTreeMap<String, ArgFact>, toks: &[Tok], s: usize, e: usize, truth: bool, depth: u16) {
    if depth >= MAX_AST_DEPTH { return; }
    let (s, e) = strip_parens(toks, s, e); if s >= e { return; }
    if let Some(p) = find_top(toks, s, e, "&&") {
        if truth { refine_cond(env, toks, s, p, true, depth + 1); refine_cond(env, toks, p.saturating_add(1), e, true, depth + 1); return; }
        let ((ls, le), (rs, re)) = (strip_parens(toks, s, p), strip_parens(toks, p.saturating_add(1), e)); let (a, b) = (toks.get(ls..le).unwrap_or(&[]), toks.get(rs..re).unwrap_or(&[]));
        for (x, y) in [(a, b), (b, a)] {
            if let [Tok::Ident(v), Tok::Sym("!="), Tok::Int(0, _)] = x {
                if let Some((v2, lo, hi)) = y.strip_prefix(&[Tok::Sym("!")]).and_then(parse_range_contains).filter(|(v2, lo, hi)| v == v2 && lo <= hi) {
                    let f = env.entry(v2).or_default(); f.s.dom = ArgFact::idom(f.s.dom, Domain::range(lo.min(0), hi.max(0))); f.nz_dom = ArgFact::idom(f.nz_dom, Domain::range(lo, hi)); }
            } }
        return; }
    if let Some(p) = find_top(toks, s, e, "||") { if !truth { refine_cond(env, toks, s, p, false, depth + 1); refine_cond(env, toks, p.saturating_add(1), e, false, depth + 1); } return; }
    if matches!(toks.get(s), Some(Tok::Sym("!"))) { refine_cond(env, toks, s.saturating_add(1), e, !truth, depth + 1); return; }
    let sl = toks.get(s..e).unwrap_or(&[]);
    if let Some((v, lo, hi)) = parse_range_contains(sl).filter(|(_, lo, hi)| truth && lo <= hi) { let f = env.entry(v).or_default(); f.s.dom = ArgFact::idom(f.s.dom, Domain::range(lo, hi)); return; }
    if let [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] = sl {
        if m == "is_empty" { apply_cmp_var(env, v, if truth { "==" } else { ">=" }, i64::from(!truth), true); }
        else if m == "is_power_of_two" && truth { env.entry(v.clone()).or_default().s.pow2 = true; }
        return; }
    for op in ["==", "!=", "<=", ">=", "<", ">"] {
        if let Some(p) = find_top(toks, s, e, op) {
            let eff = if truth { op } else { match op { "==" => "!=", "!=" => "==", "<" => ">=", "<=" => ">", ">" => "<=", _ => "<" } };
            let (lhs, rhs) = (toks.get(s..p).unwrap_or(&[]), toks.get(p.saturating_add(1)..e).unwrap_or(&[]));
            if let Some(k) = parse_int_slice(rhs) {
                match lhs { [Tok::Ident(v)] => apply_cmp_var(env, v, eff, k, false), [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "len" => apply_cmp_var(env, v, eff, k, true), _ => {} } }
            return; } } }
struct ExtractCtx<'a> { toks: &'a [Tok], caller: usize, file_idx: usize, calls: &'a mut Vec<CallSite>, depth: u16, truncated: bool }
impl<'a> ExtractCtx<'a> {
    fn with_depth<T>(&mut self, fallback: T, f: impl FnOnce(&mut Self) -> T) -> T {
        if self.depth >= MAX_AST_DEPTH { self.truncated = true; return fallback; }
        self.depth += 1; let r = f(self); self.depth -= 1; r }
    fn eval_args(&mut self, s: usize, e: usize, env: &BTreeMap<String, ArgFact>) -> Vec<ArgFact> {
        let (mut out, mut i) = (Vec::new(), s); while i < e { let j = find_top(self.toks, i, e, ",").unwrap_or(e); if j > i { out.push(self.eval_expr(i, j, env)); } i = j.saturating_add(1); }
        out }
    fn eval_match(&mut self, mut i: usize, e: usize, env: &BTreeMap<String, ArgFact>, tn: usize) -> (ArgFact, Vec<ArgFact>) {
        self.with_depth((ArgFact::default(), vec![ArgFact::default(); tn]), |this| {
        let ss = i; while i < e && !matches!(this.toks.get(i), Some(Tok::Sym("{"))) { i = i.saturating_add(1); }
        let svar = match this.toks.get(ss..i).unwrap_or(&[]) { [Tok::Ident(v)] => Some(v.clone()), _ => None }; let lim = skip_bal(this.toks, i, e, "{", "}").saturating_sub(1);
        let (mut j, mut acc, mut tacc, mut seen) = (i.saturating_add(1), None::<ArgFact>, vec![None::<ArgFact>; tn], Vec::<i64>::new());
        while j < lim {
            let Some(arr) = find_top(this.toks, j, lim, "=>") else { break; }; let pat = this.toks.get(j..arr).unwrap_or(&[]); if let Some(k) = parse_int_slice(pat) { seen.push(k); }
            let arm_s = arr.saturating_add(1);
            let arm_e = if matches!(this.toks.get(arm_s), Some(Tok::Sym("{"))) {
                let be = skip_bal(this.toks, arm_s, lim, "{", "}"); j = if matches!(this.toks.get(be), Some(Tok::Sym(","))) { be.saturating_add(1) } else { be }; be
            } else { let k = find_top(this.toks, arm_s, lim, ",").unwrap_or(lim); j = k.saturating_add(1).min(lim); k }; let mut aenv = env.clone();
            if matches!(pat, [Tok::Ident(w)] if w == "_") { if let Some(ref sv) = svar { for &k in &seen { apply_cmp_var(&mut aenv, sv, "!=", k, false); } } }
            let divs = block_diverges(this.toks, arm_s, arm_e);
            if tn > 0 && !divs && matches!(this.toks.get(arm_s), Some(Tok::Sym("("))) {
                let (a2, b2) = strip_parens(this.toks, arm_s, arm_e); for (slot, ef) in tacc.iter_mut().zip(this.eval_args(a2, b2, &aenv)) { *slot = Some(slot.map_or(ef, |p| p.join(ef))); }
            } else {
                let af = if matches!(this.toks.get(arm_s), Some(Tok::Sym("{"))) { this.scan_block(arm_s.saturating_add(1), arm_e.saturating_sub(1), &mut aenv) } else { this.eval_expr(arm_s, arm_e, &aenv) };
                if !divs { acc = Some(acc.map_or(af, |p| p.join(af))); } } }
        (acc.unwrap_or_default(), tacc.into_iter().map(Option::unwrap_or_default).collect()) }) }
    fn scan_if(&mut self, s: usize, e: usize, env: &mut BTreeMap<String, ArgFact>, as_expr: bool) -> (usize, ArgFact) {
        self.with_depth((e, ArgFact::default()), |this| {
        let mut j = s.saturating_add(1); while j < e && !matches!(this.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); }
        let _ = this.eval_expr(s.saturating_add(1), j, env); let t_end = skip_bal(this.toks, j, e, "{", "}");
        let mut tenv = env.clone(); refine_cond(&mut tenv, this.toks, s.saturating_add(1), j, true, 0);
        let (t_val, t_div) = (this.scan_block(j.saturating_add(1), t_end.saturating_sub(1), &mut tenv), block_diverges(this.toks, j.saturating_add(1), t_end.saturating_sub(1)));
        if matches!(this.toks.get(t_end), Some(Tok::Ident(w)) if w == "else") {
            let mut eenv = env.clone(); refine_cond(&mut eenv, this.toks, s.saturating_add(1), j, false, 0); let es = t_end.saturating_add(1);
            let (ep, ev, ed) = if matches!(this.toks.get(es), Some(Tok::Ident(w)) if w == "if") { let (p, v) = this.scan_if(es, e, &mut eenv, as_expr); (p, v, false) }
                else if matches!(this.toks.get(es), Some(Tok::Sym("{"))) { let ee = skip_bal(this.toks, es, e, "{", "}"); (ee, this.scan_block(es.saturating_add(1), ee.saturating_sub(1), &mut eenv), block_diverges(this.toks, es.saturating_add(1), ee.saturating_sub(1))) }
                else { (es, ArgFact::default(), false) };
            if !as_expr { if t_div && !ed { *env = eenv; } else if ed && !t_div { *env = tenv; } }
            return (ep, if t_div { ev } else if ed { t_val } else { t_val.join(ev) }); }
        if !as_expr {
            if t_div { refine_cond(env, this.toks, s.saturating_add(1), j, false, 0); }
            else { for (k, tv) in tenv { if let Some(ov) = env.get(&k).copied().filter(|&ov| ov != tv) { env.insert(k, ov.join(tv)); } } } }
        (t_end, ArgFact::default()) }) }
    fn eval_expr(&mut self, s: usize, e: usize, env: &BTreeMap<String, ArgFact>) -> ArgFact {
        self.with_depth(ArgFact::default(), |this| {
        let (s, e) = strip_parens(this.toks, s, e); if s >= e { return ArgFact::default(); }
        if matches!(this.toks.get(s), Some(Tok::Ident(w)) if w == "if") { let mut tmp = env.clone(); return this.scan_if(s, e, &mut tmp, true).1; }
        if matches!(this.toks.get(s), Some(Tok::Ident(w)) if w == "match") { return this.eval_match(s.saturating_add(1), e, env, 0).0; }
        if let Some(ap) = find_top_pred(this.toks, s, e, |t, _| matches!(t, Tok::Ident(w) if w == "as")) { return this.eval_expr(s, ap, env); }
        let sl = this.toks.get(s..e).unwrap_or(&[]); if let Some(v) = parse_int_slice(sl) { return ArgFact::exact(v); }
        if matches!(sl, [Tok::Ident(w)] if w == "None") { return ArgFact::opt(0, None); }
        if let [Tok::Ident(w)] = sl { return env.get(w).copied().unwrap_or_default(); }
        if matches!(sl.first(), Some(Tok::Ident(w)) if w == "Some") && matches!(sl.get(1), Some(Tok::Sym("("))) && skip_bal(this.toks, s.saturating_add(1), e, "(", ")") == e {
            return ArgFact::opt(1, this.eval_expr(s.saturating_add(2), e.saturating_sub(1), env).s.dom); }
        if let [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] = sl {
            if m == "trailing_zeros" { let b = env.get(v).copied().unwrap_or_default(); return if let Some((p, false)) = b.from_param { ArgFact { from_param: Some((p, true)), ..b } } else { b.apply_tz() }; } }
        if matches!(sl.first(), Some(Tok::Sym("&"))) && matches!(sl.last(), Some(Tok::Sym("]"))) {
            if let Some(lb) = (s..e).rev().find(|&k| matches!(this.toks.get(k), Some(Tok::Sym("[")))) {
                let inner = this.toks.get(lb.saturating_add(1)..e.saturating_sub(1)).unwrap_or(&[]);
                if let Some(rp) = inner.iter().position(|t| matches!(t, Tok::Sym(".." | "..="))) {
                    let lo = if rp == 0 { Some(0) } else { inner.get(..rp).and_then(parse_int_slice) };
                    if let (Some(a), Some(b)) = (lo, inner.get(rp.saturating_add(1)..).and_then(parse_int_slice)) {
                        let len = b.saturating_sub(a).saturating_add(i64::from(matches!(inner.get(rp), Some(Tok::Sym("..="))))); if len >= 0 { return ArgFact::slice(Domain::exact(len)); } }
                } } }
        let mut i = s;
        while i < e {
            if let Some(Tok::Ident(name)) = this.toks.get(i) {
                let mut ci = i.saturating_add(1);
                if matches!(this.toks.get(ci), Some(Tok::Sym("::"))) && matches!(this.toks.get(ci.saturating_add(1)), Some(Tok::Sym("<"))) { ci = skip_bal(this.toks, ci.saturating_add(1), e, "<", ">"); }
                if !matches!(name.as_str(), "if" | "else" | "while" | "for" | "match" | "loop" | "return" | "let" | "Some" | "Ok" | "Err") && matches!(this.toks.get(ci), Some(Tok::Sym("("))) {
                    let ce = skip_bal(this.toks, ci, e, "(", ")"); let args = this.eval_args(ci.saturating_add(1), ce.saturating_sub(1), env);
                    let is_method = i > s && matches!(this.toks.get(i.saturating_sub(1)), Some(Tok::Sym(".")));
                    let is_self = is_method && i >= s.saturating_add(2) && matches!(this.toks.get(i.saturating_sub(2)), Some(Tok::Ident(w)) if w == "self");
                    let qual = (!is_method && i >= s.saturating_add(2) && matches!(this.toks.get(i.saturating_sub(1)), Some(Tok::Sym("::")))).then(|| match this.toks.get(i.saturating_sub(2)) { Some(Tok::Ident(q)) => Some(q.clone()), _ => None }).flatten();
                    this.calls.push(CallSite { caller: this.caller, file_idx: this.file_idx, qual, short: name.clone(), is_method, is_self, args }); i = ce; continue; } }
            if matches!(this.toks.get(i), Some(Tok::Sym("{"))) { let be = skip_bal(this.toks, i, e, "{", "}"); let mut sub = env.clone(); let _ = this.scan_block(i.saturating_add(1), be.saturating_sub(1), &mut sub); i = be; continue; }
            i = i.saturating_add(1); }
        ArgFact::default() }) }
    fn scan_block(&mut self, s: usize, e: usize, env: &mut BTreeMap<String, ArgFact>) -> ArgFact {
        self.with_depth(ArgFact::default(), |this| {
        let (mut i, mut last) = (s, ArgFact::default());
        while i < e {
            match this.toks.get(i) {
                Some(Tok::Ident(w)) if w == "let" => {
                    i = i.saturating_add(1); if matches!(this.toks.get(i), Some(Tok::Ident(m)) if m == "mut") { i = i.saturating_add(1); }
                    let mut vars = Vec::new();
                    if matches!(this.toks.get(i), Some(Tok::Sym("("))) {
                        let pe = skip_bal(this.toks, i, e, "(", ")");
                        for t in this.toks.get(i.saturating_add(1)..pe.saturating_sub(1)).unwrap_or(&[]) { if let Tok::Ident(v) = t { if v != "mut" { vars.push(v.clone()); } } }
                        i = pe;
                    } else if let Some(Tok::Ident(v)) = this.toks.get(i) { vars.push(v.clone()); i = i.saturating_add(1); }
                    let (mut eq, mut d) = (i, 0usize);
                    while eq < e { match this.toks.get(eq) { Some(Tok::Sym("(" | "[" | "{" | "<")) => d = d.saturating_add(1), Some(Tok::Sym(")" | "]" | "}" | ">")) => d = d.saturating_sub(1), Some(Tok::Sym(">>")) => d = d.saturating_sub(2), Some(Tok::Sym("=" | ";")) if d == 0 => break, _ => {} } eq = eq.saturating_add(1); }
                    if matches!(this.toks.get(eq), Some(Tok::Sym("="))) {
                        let rs = eq.saturating_add(1); let re = find_top(this.toks, rs, e, ";").unwrap_or(e);
                        if vars.len() > 1 && matches!(this.toks.get(rs), Some(Tok::Ident(m)) if m == "match") {
                            let tf = this.eval_match(rs.saturating_add(1), re, env, vars.len()).1; for (v, f) in vars.into_iter().zip(tf) { env.insert(v, f); }
                        } else if let Some(v) = vars.into_iter().next() { let f = this.eval_expr(rs, re, env); env.insert(v, f); }
                        else { let _ = this.eval_expr(rs, re, env); }
                        i = re.saturating_add(1).min(e);
                    } else { i = eq.saturating_add(1).min(e); }
                    last = ArgFact::default(); }
                Some(Tok::Ident(w)) if w == "if" => { let (np, v) = this.scan_if(i, e, env, false); i = np; last = v; }
                Some(Tok::Ident(w)) if w == "match" => { let mut j = i.saturating_add(1); while j < e && !matches!(this.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); } let be = skip_bal(this.toks, j, e, "{", "}"); last = this.eval_match(i.saturating_add(1), be, env, 0).0; i = be; }
                Some(Tok::Ident(w)) if matches!(w.as_str(), "assert" | "debug_assert") && matches!(this.toks.get(i.saturating_add(1)), Some(Tok::Sym("!"))) => {
                    let pe = skip_bal(this.toks, i.saturating_add(2), e, "(", ")");
                    let ce = find_top(this.toks, i.saturating_add(3), pe.saturating_sub(1), ",").unwrap_or_else(|| pe.saturating_sub(1));
                    refine_cond(env, this.toks, i.saturating_add(3), ce, true, 0); i = pe; last = ArgFact::default(); }
                Some(Tok::Ident(w)) if matches!(w.as_str(), "while" | "for" | "loop") => {
                    let mut j = i.saturating_add(1); while j < e && !matches!(this.toks.get(j), Some(Tok::Sym("{"))) { j = j.saturating_add(1); }
                    let be = skip_bal(this.toks, j, e, "{", "}"); let mut lenv = env.clone(); if w == "while" { refine_cond(&mut lenv, this.toks, i.saturating_add(1), j, true, 0); }
                    let _ = this.scan_block(j.saturating_add(1), be.saturating_sub(1), &mut lenv); i = be; last = ArgFact::default(); }
                Some(Tok::Ident(v)) if matches!(this.toks.get(i.saturating_add(1)), Some(Tok::Sym("="))) => {
                    let re = find_top(this.toks, i.saturating_add(2), e, ";").unwrap_or(e);
                    let f = this.eval_expr(i.saturating_add(2), re, env); env.insert(v.clone(), f); i = re.saturating_add(1).min(e); last = ArgFact::default(); }
                Some(Tok::Sym("{")) => { let be = skip_bal(this.toks, i, e, "{", "}"); let mut sub = env.clone(); last = this.scan_block(i.saturating_add(1), be.saturating_sub(1), &mut sub); i = be; }
                _ => { let se = find_top(this.toks, i, e, ";").unwrap_or(e); let v = this.eval_expr(i, se, env); last = if se < e { ArgFact::default() } else { v }; i = se.saturating_add(1).min(e); } } }
        last }) } }
fn find_workspace_root(dir: &Path) -> (Option<PathBuf>, bool) {
    let base = if dir.is_file() { dir.parent().unwrap_or(dir) } else { dir }; let mut cur = Some(base);
    for _ in 0..4 { if let Some(anc) = cur { if std::fs::read_to_string(anc.join("Cargo.toml")).is_ok_and(|s| s.contains("[workspace]")) { return (Some(anc.to_path_buf()), false); } cur = anc.parent(); } }
    let cd = if base.join("Cargo.toml").is_file() { Some(base) } else if base.file_name().and_then(|s| s.to_str()) == Some("src") && base.parent().is_some_and(|p| p.join("Cargo.toml").is_file()) { base.parent() } else { None };
    let Some(toml) = cd.and_then(|c| std::fs::read_to_string(c.join("Cargo.toml")).ok()) else { return (None, false); }; let Some(cd) = cd else { return (None, false); };
    if toml.contains(".workspace = true") || toml.contains(".workspace=true") {
        let mut anc = cd.parent();
        for _ in 0..2 { if let Some(a) = anc { if std::fs::read_dir(a).ok().map_or(0, |rd| rd.flatten().filter(|e| e.path().join("Cargo.toml").is_file()).count()) >= 2 { return (Some(a.to_path_buf()), false); } anc = a.parent(); } }
        return (None, false); }
    (None, toml.contains("[package]") && !cd.join("src/main.rs").is_file() && !cd.join("main.rs").is_file() && !toml.contains("publish = false") && !toml.contains("publish=false")) }
fn narrow_program(lf: &LoweredFn, facts: &[ArgFact]) -> Option<Program> {
    let (mut prog, mut narrowed) = (lf.prog.clone(), false);
    let off = usize::from(lf.params.first().is_some_and(|p| matches!(p, PocParam::Struct { name, .. } | PocParam::Enum { name, .. } if name == "self_val")));
    for (ai, fact) in facts.iter().enumerate() {
        let Some(pp) = lf.params.get(ai.saturating_add(off)) else { continue; };
        let mut apply = |pidx: usize, d: Domain| { if let Some(slot) = prog.param_domains.get_mut(pidx) { if let Some(nd) = slot.try_meet(d).filter(|&nd| nd != *slot) { *slot = nd; narrowed = true; } } };
        match *pp {
            PocParam::Scalar { pidx, .. } => if let Some(d) = fact.s.dom { apply(pidx, d); },
            PocParam::Slice { pidx, .. } | PocParam::Str { pidx, .. } => if let Some(d) = fact.s.slice_len { apply(pidx, d); },
            PocParam::Opt { is_some, val, .. } => {
                if let Some(d) = fact.s.opt_is_some { apply(is_some, d); }
                if let Some(d) = fact.s.dom { apply(val, d); } }
            _ => {} } }
    narrowed.then_some(prog) }
type IncomingEdges = Vec<Vec<(usize, Vec<ArgFact>)>>;
const MAX_INCOMING_EDGES: usize = 64;
const MAX_AMBIGUOUS_BUCKET: usize = 32;
struct CgIndex<'a> {
    by_file_full: HashMap<(usize, &'a str), usize>,
    by_method: HashMap<(&'a str, usize), Vec<usize>>,
    by_file_method: HashMap<(usize, &'a str, usize), Vec<usize>>,
    by_type_assoc: HashMap<(&'a str, &'a str, usize), Vec<usize>>,
    by_file_free: HashMap<(usize, &'a str, usize), Vec<usize>>,
    by_free: HashMap<(&'a str, usize), Vec<usize>>, }
impl<'a> CgIndex<'a> {
    fn build(fns: &'a [CgFn]) -> Self {
        let mut idx = Self {
            by_file_full: HashMap::with_capacity(fns.len()),
            by_method: HashMap::new(), by_file_method: HashMap::new(),
            by_type_assoc: HashMap::new(), by_file_free: HashMap::new(), by_free: HashMap::new(), };
        for (fid, f) in fns.iter().enumerate() {
            idx.by_file_full.entry((f.file_idx, f.full_name.as_str())).or_insert(fid); let ar = f.params.len();
            if f.has_self {
                idx.by_method.entry((f.short_name.as_str(), ar)).or_default().push(fid); idx.by_file_method.entry((f.file_idx, f.short_name.as_str(), ar)).or_default().push(fid);
            } else if let Some(ref st) = f.self_ty {
                idx.by_type_assoc.entry((st.as_str(), f.short_name.as_str(), ar)).or_default().push(fid);
            } else { idx.by_file_free.entry((f.file_idx, f.short_name.as_str(), ar)).or_default().push(fid); idx.by_free.entry((f.short_name.as_str(), ar)).or_default().push(fid); } }
        idx }
    fn mark_ambiguous(&self, fns: &[CgFn], ambiguous: &mut [bool]) {
        for b in self.by_method.values().chain(self.by_free.values()) {
            if b.len() > MAX_AMBIGUOUS_BUCKET { for &fid in b { if fns.get(fid).is_some_and(|f| f.vis >= 1) { if let Some(slot) = ambiguous.get_mut(fid) { *slot = true; } } } }
        } } }
fn push_call_edge(tgt: usize, c: &CallSite, incoming: &mut [Vec<(usize, Vec<ArgFact>)>], ambiguous: &mut [bool]) {
    if tgt == c.caller { return; }
    if let Some(slot) = incoming.get_mut(tgt) {
        if slot.len() < MAX_INCOMING_EDGES { slot.push((c.caller, c.args.clone())); }
        else if let Some(a) = ambiguous.get_mut(tgt) { *a = true; } } }
fn visible_to(f: &CgFn, c_file: usize, n_target: usize) -> bool { f.file_idx == c_file || f.vis == 2 || (f.vis >= 1 && f.file_idx < n_target && c_file < n_target) }
fn push_bucket(b: Option<&Vec<usize>>, loc: Option<&Vec<usize>>, c: &CallSite, fns: &[CgFn], n_target: usize, incoming: &mut IncomingEdges, ambiguous: &mut [bool]) {
    let Some(b) = b else { return; };
    if b.len() > MAX_AMBIGUOUS_BUCKET {
        if let Some(l) = loc { for &fid in l { push_call_edge(fid, c, incoming, ambiguous); } }
    } else { for &fid in b { if fns.get(fid).is_some_and(|f| visible_to(f, c.file_idx, n_target)) { push_call_edge(fid, c, incoming, ambiguous); } } } }
fn add_call_edges(c: &CallSite, fns: &[CgFn], idx: &CgIndex<'_>, n_target: usize, incoming: &mut IncomingEdges, ambiguous: &mut [bool]) {
    let ar = c.args.len();
    if c.is_method {
        if c.is_self {
            let ct = fns.get(c.caller).and_then(|f| f.self_ty.as_deref());
            if let Some(loc) = idx.by_file_method.get(&(c.file_idx, c.short.as_str(), ar)) {
                let mut hit = false;
                for &fid in loc { if fns.get(fid).is_some_and(|f| f.self_ty.as_deref() == ct) { push_call_edge(fid, c, incoming, ambiguous); hit = true; } }
                if hit { return; } } }
        push_bucket(idx.by_method.get(&(c.short.as_str(), ar)), idx.by_file_method.get(&(c.file_idx, c.short.as_str(), ar)), c, fns, n_target, incoming, ambiguous); return; }
    if let Some(ref q) = c.qual {
        let q_ty = if q == "Self" { fns.get(c.caller).and_then(|f| f.self_ty.as_deref()).unwrap_or(q.as_str()) } else { q.as_str() };
        if let Some(bt) = idx.by_type_assoc.get(&(q_ty, c.short.as_str(), ar)).filter(|bt| !bt.is_empty()) { for &fid in bt { push_call_edge(fid, c, incoming, ambiguous); } return; }
    } else if let Some(loc) = idx.by_file_free.get(&(c.file_idx, c.short.as_str(), ar)).filter(|l| !l.is_empty()) { for &fid in loc { push_call_edge(fid, c, incoming, ambiguous); } return; }
    push_bucket(idx.by_free.get(&(c.short.as_str(), ar)), idx.by_file_free.get(&(c.file_idx, c.short.as_str(), ar)), c, fns, n_target, incoming, ambiguous); }
fn extract_calls_range(fns: &[CgFn], start: usize, all_toks: &[Vec<Tok>], calls: &mut Vec<CallSite>) -> bool {
    let mut any_truncated = false;
    for (off, f) in fns.get(start..).unwrap_or(&[]).iter().enumerate() {
        let fid = start.saturating_add(off); let Some(toks) = all_toks.get(f.file_idx) else { continue; };
        let mut env: BTreeMap<String, ArgFact> = f.params.iter().enumerate().map(|(pi, n)| (n.clone(), ArgFact { from_param: Some((pi, false)), ..ArgFact::default() })).collect();
        let mut ec = ExtractCtx { toks, caller: fid, file_idx: f.file_idx, calls, depth: 0, truncated: false };
        let _ = ec.scan_block(f.body.0, f.body.1, &mut env);
        any_truncated |= ec.truncated; }
    any_truncated }
fn pub_pat(f: &CgFn) -> String { f.self_ty.as_ref().map_or_else(|| format!("{}(", f.short_name), |st| format!("{st}::{}(", f.short_name)) }
pub(crate) struct CgAuditCtx<'a> {
    pub(crate) dir: Option<&'a Path>, pub(crate) files: &'a [PathBuf], pub(crate) fidxs: &'a [FileIndex],
    pub(crate) failed_lowered: &'a [(usize, usize, LoweredFn)], pub(crate) utf8_pending: &'a [Utf8Pending],
    pub(crate) preds: &'a BTreeSet<String>, pub(crate) morphs: &'a BTreeMap<String, BoundaryMorphism>,
    pub(crate) skip: &'a [String], pub(crate) skip_cfg_test: bool, pub(crate) profile: ArchProfile, pub(crate) cfg: RefineConfig, }
fn discharge_utf8_airlock(ctx: &CgAuditCtx<'_>, g: (&[CgFn], &CgIndex<'_>, &IncomingEdges, &[bool]), toks_extra: (&[Vec<Tok>], &[FileIndex]), to_sup: &mut BTreeMap<(usize, usize), SuppressedHelper>) {
    let ((fns, idx, incoming, ambiguous), (all_toks, extra_fidxs)) = (g, toks_extra);
    if ctx.utf8_pending.is_empty() { return; }
    let n_base = ctx.fidxs.len(); let get_fidx = |fi: usize| ctx.fidxs.get(fi).or_else(|| fi.checked_sub(n_base).and_then(|k| extra_fidxs.get(k)));
    let (mut inits, mut work) = (HashMap::<usize, Utf8ParamInit>::new(), Vec::new());
    for u in ctx.utf8_pending {
        let Some(item) = ctx.fidxs.get(u.ridx).and_then(|f| f.fns.get(u.item_idx)) else { continue; };
        let Some(&fid) = idx.by_file_full.get(&(u.ridx, item.name.as_str())) else { continue; };
        if fns.get(fid).is_some_and(|f| f.vis < 2) && !ambiguous.get(fid).copied().unwrap_or(true) && !incoming.get(fid).map_or(true, Vec::is_empty) { work.push((fid, u)); } }
    if work.is_empty() { return; }
    let empty_init = Utf8ParamInit::default();
    for _ in 0..4 {
        let mut changed = false;
        for &(fid, u) in &work {
            if to_sup.contains_key(&(u.ridx, u.fidx)) { continue; }
            let Some(tf) = fns.get(fid) else { continue; }; let edges = incoming.get(fid).map_or(&[][..], Vec::as_slice);
            let (mut all_s, mut all_p, mut all_a, mut ok_all) = (None::<Vec<bool>>, None::<Vec<bool>>, None::<Vec<bool>>, !edges.is_empty());
            for &(cid, _) in edges {
                let (Some(cf), Some(cfi), Some(ctoks)) = (fns.get(cid), fns.get(cid).and_then(|c| get_fidx(c.file_idx)), fns.get(cid).and_then(|c| all_toks.get(c.file_idx))) else { ok_all = false; break; };
                let Some(citem) = cfi.fns.get(cf.item_idx) else { ok_all = false; break; }; let mut matched = false;
                for w in collect_utf8_call_witnesses(citem, cfi, ctoks, ctx.preds, ctx.morphs, inits.get(&cid).unwrap_or(&empty_init)) {
                    if w.short != tf.short_name || w.arg_safe.len() != tf.params.len() || w.is_method != tf.has_self { continue; }
                    if let Some(ref q) = w.qual { if tf.self_ty.as_deref().map_or(!q.bytes().next().is_some_and(|c| c.is_ascii_lowercase()), |st| st != if q == "Self" { cf.self_ty.as_deref().unwrap_or(q.as_str()) } else { q.as_str() }) { continue; } }
                    matched = true; all_s = Some(all_s.map_or(w.arg_safe.clone(), |o| o.into_iter().zip(w.arg_safe).map(|(x, y)| x && y).collect()));
                    all_p = Some(all_p.map_or(w.arg_plus1.clone(), |o| o.into_iter().zip(w.arg_plus1).map(|(x, y)| x && y).collect()));
                    all_a = Some(all_a.map_or(w.arg_ascii.clone(), |o| o.into_iter().zip(w.arg_ascii).map(|(x, y)| x && y).collect())); }
                if !matched { ok_all = false; break; } }
            if !ok_all { continue; }
            let mut ni = Utf8ParamInit::default();
            if let (Some(sv), Some(pv), Some(av)) = (all_s, all_p, all_a) {
                for (((p, s), p1), ac) in tf.params.iter().zip(sv).zip(pv).zip(av) {
                    if s { ni.safe.insert(p.clone()); }
                    if p1 { ni.plus1.insert(p.clone()); }
                    if ac { ni.ascii_str.insert(p.clone()); } } }
            if !matches!(inits.get(&fid), Some(o) if o.safe == ni.safe && o.plus1 == ni.plus1 && o.ascii_str == ni.ascii_str) { inits.insert(fid, ni.clone()); changed = true; }
            if let (Some(tfi), Some(ttoks)) = (ctx.fidxs.get(u.ridx), all_toks.get(u.ridx)) {
                if let Some(titem) = tfi.fns.get(u.item_idx) {
                    if audit_utf8_item(titem, tfi, ttoks, ctx.preds, ctx.morphs, &ni).is_none() {
                        to_sup.insert((u.ridx, u.fidx), SuppressedHelper { fn_name: titem.name.clone(), caller_count: edges.len(), reason: format!("all {} callers discharge UTF-8 precondition", edges.len()) }); }
                } } }
        if !changed { break; } } }
pub(crate) fn apply_interprocedural_reachability(ctx: CgAuditCtx<'_>, all_toks: &mut Vec<Vec<Tok>>, reports: &mut [RustProofReport]) {
    if ctx.failed_lowered.is_empty() && ctx.utf8_pending.is_empty() { return; }
    let ((ws_root, standalone_lib), n_target) = (ctx.dir.map_or((None, false), find_workspace_root), all_toks.len());
    let (mut fns, mut extra_fidxs): (Vec<CgFn>, Vec<FileIndex>) = (Vec::new(), Vec::new());
    for (fi, (fidx, toks)) in ctx.fidxs.iter().zip(all_toks.iter()).enumerate() { push_cg_fns(fidx, toks, fi, ctx.skip_cfg_test, &mut fns); }
    let mut calls = Vec::new(); let mut any_truncated = extract_calls_range(&fns, 0, all_toks, &mut calls);
    if let Some(root) = ws_root {
        let (mut known, mut pool, mut frontier, mut fshorts) = (ctx.files.iter().cloned().collect::<BTreeSet<_>>(), Vec::new(), BTreeSet::<String>::new(), HashSet::<String>::new());
        let init_map: HashMap<(usize, &str), usize> = fns.iter().enumerate().map(|(i, f)| ((f.file_idx, f.full_name.as_str()), i)).collect();
        let _ = crate::lint_rs::collect_rs_files_opts(&root, ctx.skip, ctx.skip_cfg_test, &mut pool);
        for &(ridx, fidx, _) in ctx.failed_lowered {
            if let Some(fail) = reports.get(ridx).and_then(|r| r.failed.get(fidx)) {
                if let Some(&fid) = init_map.get(&(ridx, fail.fn_name.as_str())) { if let Some(cf) = fns.get(fid).filter(|f| f.vis == 2) { frontier.insert(format!("{}(", cf.short_name)); fshorts.insert(cf.short_name.clone()); } }
            } }
        for c in &calls { if fshorts.contains(&c.short) { if let Some(cf) = fns.get(c.caller).filter(|f| f.vis == 2) { frontier.insert(pub_pat(cf)); } } }
        let (mut seen, base_fns) = (frontier.clone(), fns.len());
        for _ in 0..3 {
            if frontier.is_empty() || all_toks.len() >= n_target.saturating_add(128) { break; }
            let pats: Vec<String> = frontier.iter().cloned().collect(); frontier.clear();
            for p in &pool {
                if known.contains(p) || all_toks.len() >= n_target.saturating_add(128) { continue; }
                let Ok(src) = std::fs::read_to_string(p) else { continue; }; if !pats.iter().any(|pat| src.contains(pat.as_str())) { continue; }
                known.insert(p.clone()); let (fi, toks, prev) = (all_toks.len(), tokenize_rust(&src), fns.len());
                let xf = scan_file(&toks); push_cg_fns(&xf, &toks, fi, ctx.skip_cfg_test, &mut fns);
                for nf in fns.get(prev..).unwrap_or(&[]) { if nf.vis == 2 { let k = pub_pat(nf); if seen.insert(k.clone()) { frontier.insert(k); } } }
                extra_fidxs.push(xf); all_toks.push(toks); } }
        any_truncated |= extract_calls_range(&fns, base_fns, all_toks, &mut calls); }
    let idx = CgIndex::build(&fns); let (mut incoming, mut ambiguous): (IncomingEdges, Vec<bool>) = (vec![Vec::new(); fns.len()], vec![false; fns.len()]);
    idx.mark_ambiguous(&fns, &mut ambiguous);
    if any_truncated { ambiguous.fill(true); }
    for c in &calls { add_call_edges(c, &fns, &idx, n_target, &mut incoming, &mut ambiguous); }
    let (mut relevant, mut rel_seen, mut rq) = (Vec::new(), HashSet::new(), VecDeque::new());
    for &(ridx, fidx, _) in ctx.failed_lowered {
        if let Some(fail) = reports.get(ridx).and_then(|r| r.failed.get(fidx)) { if let Some(&fid) = idx.by_file_full.get(&(ridx, fail.fn_name.as_str())) { if rel_seen.insert(fid) { relevant.push(fid); rq.push_back((fid, 0usize)); } } } }
    while let Some((cur, depth)) = rq.pop_front() {
        if depth >= 12 { continue; }
        for &(caller, _) in incoming.get(cur).map_or(&[][..], Vec::as_slice) { if rel_seen.insert(caller) { relevant.push(caller); rq.push_back((caller, depth.saturating_add(1))); } } }
    let mut in_params: Vec<Option<Vec<ArgFact>>> = vec![None; fns.len()];
    for _ in 0..6 {
        let mut updates: Vec<(usize, Option<Vec<ArgFact>>)> = Vec::with_capacity(relevant.len());
        for &tgt in &relevant {
            let mut acc: Option<Vec<ArgFact>> = None;
            for (caller, raw) in incoming.get(tgt).map_or(&[][..], Vec::as_slice) {
                let res: Vec<ArgFact> = raw.iter().map(|a| a.resolve(in_params.get(*caller).and_then(|o| o.as_deref()))).collect();
                acc = Some(acc.map_or(res.clone(), |p| p.into_iter().zip(res).map(|(x, y)| x.join(y)).collect())); }
            updates.push((tgt, acc)); }
        for (tgt, acc) in updates { if let Some(slot) = in_params.get_mut(tgt) { *slot = acc; } } }
    let (mut to_sup, mut traces) = (BTreeMap::<(usize, usize), SuppressedHelper>::new(), BTreeMap::<(usize, usize), Vec<String>>::new());
    for &(ridx, fidx, ref lf) in ctx.failed_lowered {
        let Some(fail) = reports.get(ridx).and_then(|r| r.failed.get(fidx)) else { continue; };
        let Some(&fid) = idx.by_file_full.get(&(ridx, fail.fn_name.as_str())) else { traces.insert((ridx, fidx), vec![fail.fn_name.clone()]); continue; };
        let edges = incoming.get(fid).map_or(&[][..], Vec::as_slice); let is_amb = ambiguous.get(fid).copied().unwrap_or(false);
        if edges.is_empty() || (standalone_lib && fns.get(fid).is_some_and(|f| f.vis == 2)) { traces.insert((ridx, fidx), vec![fail.fn_name.clone()]); continue; }
        if !is_amb && in_params.get(fid).and_then(|o| o.as_deref()).and_then(|j| narrow_program(lf, j)).is_some_and(|np| verify_program(&np, ctx.profile, ctx.cfg).is_ok()) {
            to_sup.insert((ridx, fidx), SuppressedHelper { fn_name: fail.fn_name.clone(), caller_count: edges.len(), reason: format!("all {} callers discharge precondition", edges.len()) }); continue; }
        let (mut q, mut vis, mut best, mut vcache) = (VecDeque::new(), BTreeSet::from([fid]), vec![fid], HashMap::<Vec<Domain>, bool>::new());
        for (caller, raw) in edges {
            let res: Vec<ArgFact> = raw.iter().map(|a| a.resolve(in_params.get(*caller).and_then(|o| o.as_deref()))).collect();
            let safe = narrow_program(lf, &res).is_some_and(|np| *vcache.entry(np.param_domains.clone()).or_insert_with(|| verify_program(&np, ctx.profile, ctx.cfg).is_ok()));
            if !safe && vis.insert(*caller) { q.push_back((*caller, vec![fid, *caller])); } }
        while let Some((cur, path)) = q.pop_front() {
            if path.len() > best.len() { best = path.clone(); }
            let cur_in = incoming.get(cur).map_or(&[][..], Vec::as_slice); if cur_in.is_empty() || fns.get(cur).is_some_and(|f| f.short_name == "main") || path.len() >= 12 { best = path; break; }
            for &(prev, _) in cur_in { if vis.insert(prev) { let mut np = path.clone(); np.push(prev); q.push_back((prev, np)); } } }
        traces.insert((ridx, fidx), best.into_iter().rev().filter_map(|id| fns.get(id).map(|f| f.full_name.clone())).collect()); }
    discharge_utf8_airlock(&ctx, (&fns, &idx, &incoming, &ambiguous), (all_toks, &extra_fidxs), &mut to_sup);
    for (ridx, rep) in reports.iter_mut().enumerate() {
        let mut kept = Vec::with_capacity(rep.failed.len());
        for (fidx, mut fail) in std::mem::take(&mut rep.failed).into_iter().enumerate() {
            if let Some(sup) = to_sup.remove(&(ridx, fidx)) { rep.suppressed_guarded.push(sup); }
            else {
                if let Some(ch) = traces.remove(&(ridx, fidx)) {
                    if let Some(ref mut poc) = fail.poc_test { *poc = format!("// call-chain: {}\n{poc}", ch.join(" -> ")); }
                    fail.entrypoint_trace = Some(ch); }
                kept.push(fail); } }
        rep.failed = kept; } }
