use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use crate::abstract_eval::{ArchProfile, CmpKind, Domain, IrOp, Op, Program, VerifyError};
use crate::{simd_fuzz::RefineConfig, verify_program, ProgramReport};

#[derive(Clone, Debug)]
pub struct ParsedRustUnit { pub programs: Vec<Program>, pub skipped_non_kernel_fns: Vec<String> }
#[derive(Clone, Debug)]
pub struct RustFnFailure { pub fn_name: String, pub error: VerifyError }
#[derive(Clone, Debug)]
pub struct RustProofReport {
    pub file: String, pub proven: Vec<(String, ProgramReport)>, pub failed: Vec<RustFnFailure>, pub skipped_non_kernel_fns: Vec<String>,
}
impl RustProofReport { #[must_use] pub fn is_clean(&self) -> bool { self.failed.is_empty() } }

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok { Ident(String), Int(i64), Doc(String), Sym(&'static str) }

fn is_intrinsic(name: &str) -> bool { matches!(name, "zero_alloc" | "zero_free" | "zero_check_gen" | "zero_uninit_read" | "zero_uninit_write") }

fn parse_int_lit(raw: &str) -> Option<i64> {
    let clean: String = raw.chars().filter(|&c| c != '_').collect();
    let (radix, body) = [("0x", 16), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)]
        .into_iter().find_map(|(p, r)| clean.strip_prefix(p).map(|b| (r, b))).unwrap_or((10, clean.as_str()));
    let end = body.find(|c: char| !c.is_digit(radix)).unwrap_or(body.len());
    (end > 0).then(|| i64::from_str_radix(&body[..end], radix).ok()).flatten()
}

fn tokenize_rust(src: &str) -> Vec<Tok> {
    const MULTI: &[&str] = &["..=", "<<=", ">>=", "..", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "&=", "|=", "^=", "::"];
    const SINGLE: &[&str] = &["(", ")", "{", "}", "[", "]", ",", ":", ";", "=", "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "!", ".", "#"];
    let (b, n, mut i, mut out) = (src.as_bytes(), src.len(), 0usize, Vec::new());
    while i < n {
        if b[i].is_ascii_whitespace() { i += 1; continue; }
        let rest = &src[i..];
        if rest.starts_with("///") { let s = i + 3; while i < n && b[i] != b'\n' { i += 1; } out.push(Tok::Doc(src[s..i].trim().to_string())); }
        else if rest.starts_with("//") { while i < n && b[i] != b'\n' { i += 1; } }
        else if rest.starts_with("/*") {
            let mut d = 1usize; i += 2;
            while i < n && d > 0 { if src[i..].starts_with("/*") { d += 1; i += 2; } else if src[i..].starts_with("*/") { d -= 1; i += 2; } else { i += 1; } }
        } else if b[i] == b'"' {
            i += 1; while i < n { if b[i] == b'\\' && i + 1 < n { i += 2; } else if b[i] == b'"' { i += 1; break; } else { i += 1; } } out.push(Tok::Sym("\""));
        } else if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let s = i; while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; } out.push(Tok::Ident(src[s..i].to_string()));
        } else if b[i].is_ascii_digit() {
            let s = i; while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; } out.push(parse_int_lit(&src[s..i]).map_or(Tok::Sym("?"), Tok::Int));
        } else if let Some(&s) = MULTI.iter().find(|&&m| rest.starts_with(m)) { out.push(Tok::Sym(s)); i += s.len(); }
        else { out.push(Tok::Sym(SINGLE.iter().copied().find(|s| s.as_bytes()[0] == b[i]).unwrap_or("?"))); i += 1; }
    }
    out
}

fn scalar_type_domain(ty: &str) -> Option<Domain> {
    Some(match ty {
        "bool" => Domain::range(0, 1), "u8" => Domain::range(0, 255), "u16" => Domain::range(0, 65_535),
        "u32" => Domain::range(0, 4_294_967_295), "u64" | "usize" => Domain::range(0, i64::MAX),
        "i8" => Domain::range(-128, 127), "i16" => Domain::range(-32_768, 32_767),
        "i32" => Domain::range(-2_147_483_648, 2_147_483_647), "i64" | "isize" => Domain::top(), _ => return None,
    })
}

fn parse_signed(raw: &str) -> Option<i64> {
    let s = raw.trim();
    if let Some(r) = s.strip_prefix('-') { parse_int_lit(r.trim()).and_then(i64::checked_neg) } else { parse_int_lit(s) }
}

fn parse_domain_rhs(raw: &str) -> Option<Domain> {
    let s = raw.trim();
    let (rp, mp) = match s.find("mod") { Some(p) => (s[..p].trim(), Some(s[p + 3..].trim())), None => (s, None) };
    let (lo, hi) = if let Some((a, b)) = rp.split_once("..=") { (parse_signed(a)?, parse_signed(b)?) }
    else if let Some((a, b)) = rp.split_once("..") { (parse_signed(a)?, parse_signed(b)?.checked_sub(1)?) }
    else { let v = parse_signed(rp)?; (v, v) };
    if let Some(mstr) = mp {
        let (ms, rs) = mstr.split_once("==")?; let (m, r) = (parse_signed(ms)?, parse_signed(rs)?);
        (m > 0).then(|| Domain::congruent(lo, hi, m, r))
    } else { Some(Domain::range(lo, hi)) }
}

#[derive(Clone, Default)]
struct FnMeta { domains: BTreeMap<String, Domain>, uninit: BTreeSet<String>, regions: BTreeMap<String, (u16, usize)> }

fn collect_domain_spec(spec: &str, named: &mut BTreeMap<String, Domain>) -> Option<Domain> {
    let mut anon = None;
    for part in spec.trim().trim_start_matches('(').trim_end_matches(')').trim().split(',').map(str::trim).filter(|p| !p.is_empty()) {
        if let Some((k, v)) = part.split_once(':').or_else(|| part.split_once('=')) {
            let key = k.trim();
            if !key.is_empty() && key.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_') && !key.as_bytes()[0].is_ascii_digit() {
                if let Some(d) = parse_domain_rhs(v) { named.insert(key.to_string(), d); continue; }
            }
        }
        if let Some(d) = parse_domain_rhs(part) { anon = Some(d); }
    }
    anon
}

fn parse_pair_region(s: &str) -> Option<(u16, usize)> {
    let (a, b) = s.trim().trim_start_matches('(').trim_end_matches(')').split_once(',')?;
    Some((a.trim().parse().ok()?, b.trim().parse().ok()?))
}

fn parse_doc_meta(line: &str, meta: &mut FnMeta) {
    if let Some(rest) = line.strip_prefix("@domain").or_else(|| line.strip_prefix("@zero_domain")) { let _ = collect_domain_spec(rest, &mut meta.domains); }
    else if let Some(rest) = line.strip_prefix("@uninit") { for p in rest.split([',', ' ', '\t']).map(str::trim).filter(|s| !s.is_empty()) { meta.uninit.insert(p.to_string()); } }
    else if let Some(rest) = line.strip_prefix("@region") { if let Some((k, v)) = rest.split_once(':') { if let Some(p) = parse_pair_region(v) { meta.regions.insert(k.trim().to_string(), p); } } }
}

struct Cursor<'a> { toks: &'a [Tok], pos: usize }
impl<'a> Cursor<'a> {
    fn peek(&self) -> Option<&'a Tok> { self.toks.get(self.pos) }
    fn next(&mut self) -> Option<&'a Tok> { let t = self.toks.get(self.pos); if t.is_some() { self.pos += 1; } t }
    fn eat_if(&mut self, pred: impl FnOnce(&Tok) -> bool) -> bool { if self.peek().is_some_and(pred) { self.pos += 1; true } else { false } }
    fn eat_sym(&mut self, s: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Sym(x) if *x == s)) }
    fn eat_ident(&mut self, kw: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Ident(x) if x == kw)) }
    fn expect_ident(&mut self) -> Option<String> { if let Some(Tok::Ident(s)) = self.peek() { self.pos += 1; Some(s.clone()) } else { None } }
    fn parse_signed_tok(&mut self) -> Option<i64> {
        let neg = self.eat_sym("-");
        match self.next()? { &Tok::Int(v) => if neg { v.checked_neg() } else { Some(v) }, _ => None }
    }
    fn skip_balanced(&mut self, open: &str, close: &str) {
        if !self.eat_sym(open) { return; }
        let mut d = 1usize;
        while let Some(t) = self.next() { if matches!(t, Tok::Sym(s) if *s == open) { d += 1; } else if matches!(t, Tok::Sym(s) if *s == close) { d -= 1; if d == 0 { break; } } }
    }
    fn parse_attr(&mut self, meta: &mut FnMeta) -> (Option<Domain>, bool, Option<(u16, usize)>) {
        if !self.eat_sym("#") { return (None, false, None); }
        let _ = self.eat_sym("!");
        if !self.eat_sym("[") { return (None, false, None); }
        let (start, mut d) = (self.pos, 1usize);
        while let Some(t) = self.next() { match t { Tok::Sym("[") => d += 1, Tok::Sym("]") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let slice = &self.toks[start..self.pos.saturating_sub(1)];
        let Some(Tok::Ident(name)) = slice.first() else { return (None, false, None); };
        if name == "zero_uninit" { return (None, true, None); }
        let mut text = String::new();
        for t in &slice[1..] { match t { Tok::Ident(s) => { text.push(' '); text.push_str(s); } Tok::Int(v) => { text.push(' '); text.push_str(&v.to_string()); } Tok::Sym(s) => text.push_str(s), Tok::Doc(_) => {} } }
        if name == "zero_domain" && slice.len() >= 3 { (collect_domain_spec(&text, &mut meta.domains), false, None) }
        else if name == "zero_region" { (None, false, parse_pair_region(&text)) }
        else { (None, false, None) }
    }
}

struct FnItem { name: String, sig_pos: usize, meta: FnMeta }
#[derive(Clone, Copy)]
struct BufBind { id: u8, base: usize, len: usize, mutable: bool }
enum CallArg { Scalar(usize), Buf(BufBind) }

fn bin_prec(sym: &str) -> Option<u8> {
    match sym { "||" => Some(1), "&&" => Some(2), "==" | "!=" | "<" | "<=" | ">" | ">=" => Some(3), "|" => Some(4), "^" => Some(5), "&" => Some(6), "<<" | ">>" => Some(7), "+" | "-" => Some(8), "*" | "/" | "%" => Some(9), _ => None }
}

struct LowerCtx<'a> {
    prog: Program, vars: BTreeMap<String, usize>, bufs: BTreeMap<String, BufBind>, stores: Vec<usize>,
    cur_guard: Option<(usize, bool)>, early_rets: Vec<(usize, Vec<usize>)>,
    fns: &'a [FnItem], toks: &'a [Tok], depth: u8, inlined_fns: &'a mut BTreeSet<String>,
}

impl<'a> LowerCtx<'a> {
    fn push_g(&mut self, op: IrOp) -> usize { self.prog.push_guarded(op, self.cur_guard) }
    fn mk_bool(&mut self, c: usize, pol: bool) -> usize { if pol { c } else { let z = self.prog.push(Op::Const(0)); self.prog.push(Op::Cmp(CmpKind::Eq, c, z)) } }
    fn and_guard(&mut self, old: Option<(usize, bool)>, add: (usize, bool)) -> Option<(usize, bool)> {
        let Some((g0, p0)) = old else { return Some(add); };
        let (b0, b1, z) = (self.mk_bool(g0, p0), self.mk_bool(add.0, add.1), self.prog.push(Op::Const(0)));
        Some((self.prog.push(Op::Select { cond: b0, t_val: b1, f_val: z }), true))
    }
    fn buf_index(&mut self, bb: BufBind, idx: usize) -> usize {
        if bb.base == 0 && bb.len == self.prog.bufs[usize::from(bb.id)].len { return idx; }
        let (bc, off) = (self.push_g(Op::BoundsCheck { idx, limit: bb.len }), self.prog.push(Op::Const(bb.base as i64)));
        self.push_g(Op::Add(bc, off))
    }
    fn parse_expr(&mut self, c: &mut Cursor<'_>) -> Option<usize> { self.parse_binop(c, 1) }
    fn parse_binop(&mut self, c: &mut Cursor<'_>, min_p: u8) -> Option<usize> {
        let mut l = self.parse_cast(c)?;
        while let Some(&Tok::Sym(op)) = c.peek() {
            let Some(p) = bin_prec(op).filter(|&p| p >= min_p) else { break; };
            c.pos += 1;
            if op == "&&" || op == "||" {
                let old_g = self.cur_guard;
                self.cur_guard = self.and_guard(old_g, (l, op == "&&"));
                let r = self.parse_binop(c, p + 1)?;
                self.cur_guard = old_g;
                let k = self.prog.push(Op::Const(i64::from(op == "||")));
                l = self.prog.push_guarded(if op == "&&" { Op::Select { cond: l, t_val: r, f_val: k } } else { Op::Select { cond: l, t_val: k, f_val: r } }, old_g);
                continue;
            }
            let r = self.parse_binop(c, p + 1)?;
            l = self.push_g(match op {
                "==" => Op::Cmp(CmpKind::Eq, l, r), "!=" => Op::Cmp(CmpKind::Ne, l, r), "<" => Op::Cmp(CmpKind::Lt, l, r), "<=" => Op::Cmp(CmpKind::Le, l, r),
                ">" => Op::Cmp(CmpKind::Gt, l, r), ">=" => Op::Cmp(CmpKind::Ge, l, r), "|" => Op::BitOr(l, r), "^" => Op::BitXor(l, r), "&" => Op::BitAnd(l, r),
                "+" => Op::Add(l, r), "-" => Op::Sub(l, r), "*" => Op::Mul(l, r), "/" => Op::Div(l, r), "%" => Op::Rem(l, r),
                "<<" | ">>" => match (op == "<<", self.prog.nodes[r]) {
                    (true, Op::Const(v)) if (0..=255).contains(&v) => Op::Shl(l, v as u8), (false, Op::Const(v)) if (0..=255).contains(&v) => Op::Shr(l, v as u8),
                    (true, _) => Op::ShlVar(l, r), (false, _) => Op::ShrVar(l, r),
                },
                _ => return None,
            });
        }
        Some(l)
    }
    fn parse_cast(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        let mut v = self.parse_unary(c)?;
        while c.eat_ident("as") {
            v = match c.expect_ident()?.as_str() {
                "u8" => { let m = self.prog.push(Op::Const(0xFF)); self.push_g(Op::BitAnd(v, m)) }
                "u16" => { let m = self.prog.push(Op::Const(0xFFFF)); self.push_g(Op::BitAnd(v, m)) }
                "u32" => { let m = self.prog.push(Op::Const(0xFFFF_FFFF)); self.push_g(Op::BitAnd(v, m)) }
                "u64" | "usize" => self.push_g(Op::BoundsCheck { idx: v, limit: (i64::MAX as usize).saturating_add(1) }),
                "i64" | "isize" | "i32" | "i16" | "i8" | "bool" => v, _ => return None,
            };
        }
        Some(v)
    }
    fn parse_unary(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        if c.eat_sym("-") {
            if let Some(&Tok::Int(v)) = c.peek() { c.pos += 1; return Some(self.prog.push(Op::Const(v.checked_neg()?))); }
            let (r, z) = (self.parse_unary(c)?, self.prog.push(Op::Const(0))); return Some(self.push_g(Op::Sub(z, r)));
        }
        if c.eat_sym("!") { let (r, z) = (self.parse_unary(c)?, self.prog.push(Op::Const(0))); return Some(self.push_g(Op::Cmp(CmpKind::Eq, r, z))); }
        self.parse_postfix(c)
    }
    fn parse_postfix(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        let mut base = match c.peek()? {
            &Tok::Int(v) => { c.pos += 1; self.prog.push(Op::Const(v)) }
            Tok::Sym("(") => { c.pos += 1; let x = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } x }
            Tok::Sym("{") => self.parse_block(c)?.1?,
            Tok::Ident(kw) if kw == "true" || kw == "false" => { let v = i64::from(kw == "true"); c.pos += 1; self.prog.push(Op::Const(v)) }
            Tok::Ident(kw) if kw == "if" => { c.pos += 1; self.parse_if(c)?.0? }
            Tok::Ident(kw) if kw == "match" => { c.pos += 1; self.parse_match(c)? }
            Tok::Ident(nm) => {
                let nm = nm.clone(); c.pos += 1;
                if c.eat_sym("[") {
                    let (bb, idx) = (*self.bufs.get(&nm)?, self.parse_expr(c)?);
                    if !c.eat_sym("]") { return None; }
                    let ri = self.buf_index(bb, idx); self.push_g(Op::Load { buf: bb.id, idx: ri })
                } else if c.eat_sym("(") { self.parse_call(&nm, c)? } else { *self.vars.get(&nm)? }
            }
            _ => return None,
        };
        while c.eat_sym(".") {
            let m = c.expect_ident()?;
            if !c.eat_sym("(") { return None; }
            let r = self.parse_expr(c)?;
            if !c.eat_sym(")") { return None; }
            base = match m.as_str() {
                "wrapping_add" => self.push_g(Op::WrapAdd(base, r)), "wrapping_sub" => self.push_g(Op::WrapSub(base, r)), "wrapping_mul" => self.push_g(Op::WrapMul(base, r)),
                "wrapping_shl" | "wrapping_shr" => {
                    let shl = m == "wrapping_shl";
                    if let Op::Const(v) = self.prog.nodes[r] { self.push_g(if shl { Op::Shl(base, (v & 63) as u8) } else { Op::Shr(base, (v & 63) as u8) }) }
                    else { let m63 = self.prog.push(Op::Const(63)); let s = self.push_g(Op::BitAnd(r, m63)); self.push_g(if shl { Op::ShlVar(base, s) } else { Op::ShrVar(base, s) }) }
                }
                _ => return None,
            };
        }
        Some(base)
    }
    fn parse_call_arg(&mut self, c: &mut Cursor<'_>) -> Option<CallArg> {
        let (saved, is_ref) = (c.pos, c.eat_sym("&"));
        let is_mut = is_ref && c.eat_ident("mut");
        if let Some(Tok::Ident(nm)) = c.peek().cloned() {
            if let Some(&bb) = self.bufs.get(&nm) {
                if is_mut && !bb.mutable { return None; }
                c.pos += 1;
                if c.eat_sym("[") {
                    let a = usize::try_from(c.parse_signed_tok()?).ok()?;
                    let inc = if c.eat_sym("..=") { true } else if c.eat_sym("..") { false } else { return None };
                    let b = usize::try_from(c.parse_signed_tok()?).ok()?.checked_add(usize::from(inc))?;
                    if b < a || b > bb.len || !c.eat_sym("]") { return None; }
                    return Some(CallArg::Buf(BufBind { id: bb.id, base: bb.base + a, len: b - a, mutable: is_mut }));
                }
                if matches!(c.peek(), Some(Tok::Sym("," | ")"))) { return Some(CallArg::Buf(BufBind { mutable: if is_ref { is_mut } else { bb.mutable }, ..bb })); }
            }
        }
        c.pos = saved; Some(CallArg::Scalar(self.parse_expr(c)?))
    }
    fn parse_call(&mut self, name: &str, c: &mut Cursor<'_>) -> Option<usize> {
        let mut args = Vec::new();
        while !c.eat_sym(")") { args.push(self.parse_call_arg(c)?); let _ = c.eat_sym(","); }
        match name {
            "zero_alloc" => {
                let (CallArg::Buf(bb), CallArg::Scalar(ln)) = (args.first()?, args.get(1)?) else { return None; };
                let Op::Const(l) = self.prog.nodes[*ln] else { return None; };
                let n = self.push_g(Op::Alloc { buf: bb.id, len: usize::try_from(l).ok()? }); self.stores.push(n); Some(n)
            }
            "zero_free" => { let CallArg::Buf(bb) = args.first()? else { return None; }; let n = self.push_g(Op::Free(bb.id)); self.stores.push(n); Some(n) }
            "zero_check_gen" => {
                let (CallArg::Buf(bb), CallArg::Scalar(tok)) = (args.first()?, args.get(1)?) else { return None; };
                let n = self.push_g(Op::CheckGen { buf: bb.id, expected: *tok }); self.stores.push(n); Some(n)
            }
            "zero_uninit_write" => {
                let (CallArg::Buf(bb), CallArg::Scalar(idx), CallArg::Scalar(val)) = (args.first()?, args.get(1)?, args.get(2)?) else { return None; };
                let ri = self.buf_index(*bb, *idx); let n = self.push_g(Op::Store { buf: bb.id, idx: ri, val: *val }); self.stores.push(n); Some(n)
            }
            "zero_uninit_read" => {
                let (CallArg::Buf(bb), CallArg::Scalar(idx)) = (args.first()?, args.get(1)?) else { return None; };
                let ri = self.buf_index(*bb, *idx); Some(self.push_g(Op::Load { buf: bb.id, idx: ri }))
            }
            _ => self.inline_call(name, &args),
        }
    }
    fn inline_call(&mut self, name: &str, args: &[CallArg]) -> Option<usize> {
        if self.depth >= 4 { return None; }
        let item = self.fns.iter().find(|f| f.name == name)?;
        let buf_args: Vec<BufBind> = args.iter().filter_map(|a| if let CallArg::Buf(b) = a { Some(*b) } else { None }).collect();
        for i in 0..buf_args.len() {
            for j in (i + 1)..buf_args.len() {
                let (a, b) = (buf_args[i], buf_args[j]);
                if a.id == b.id && (a.mutable || b.mutable) && a.base < b.base + b.len && b.base < a.base + a.len {
                    let r = &self.prog.bufs[usize::from(a.id)];
                    self.prog.add_buf(format!("__alias_{name}"), b.len.max(1), true, r.region, r.offset + b.base, r.elem_domain);
                }
            }
        }
        let mut cc = Cursor { toks: self.toks, pos: item.sig_pos };
        if !cc.eat_sym("(") { return None; }
        let (mut nv, mut nb, mut ai, mut dm) = (BTreeMap::new(), BTreeMap::new(), 0usize, FnMeta::default());
        while !cc.eat_sym(")") {
            while let Some(Tok::Doc(l)) = cc.peek() { parse_doc_meta(l, &mut dm); cc.pos += 1; }
            while matches!(cc.peek(), Some(Tok::Sym("#"))) { let _ = cc.parse_attr(&mut dm); }
            let _ = cc.eat_ident("mut");
            let pname = cc.expect_ident()?;
            if !cc.eat_sym(":") { return None; }
            let arg = args.get(ai)?; ai += 1;
            if cc.eat_sym("&") {
                let _ = cc.eat_ident("mut");
                if !cc.eat_sym("[") || cc.expect_ident().is_none() || (cc.eat_sym(";") && cc.next().is_none()) || !cc.eat_sym("]") { return None; }
                let CallArg::Buf(bb) = *arg else { return None; }; nb.insert(pname, bb);
            } else { let _ = cc.expect_ident()?; let CallArg::Scalar(v) = *arg else { return None; }; nv.insert(pname, v); }
            let _ = cc.eat_sym(",");
        }
        if ai != args.len() { return None; }
        while let Some(t) = cc.peek() { if matches!(t, Tok::Sym("{")) { break; } cc.pos += 1; }
        let (sv, sb, se, sg) = (std::mem::replace(&mut self.vars, nv), std::mem::replace(&mut self.bufs, nb), std::mem::take(&mut self.early_rets), self.cur_guard);
        self.depth += 1; let res = self.parse_block(&mut cc); self.depth -= 1;
        let callee_early = std::mem::replace(&mut self.early_rets, se);
        (self.cur_guard, self.vars, self.bufs) = (sg, sv, sb);
        let (rets, tail, _) = res?;
        self.inlined_fns.insert(name.to_string());
        let mut val = tail.or_else(|| rets.first().copied()).unwrap_or_else(|| self.prog.push(Op::Const(0)));
        for (cond, erets) in callee_early.into_iter().rev() {
            if let Some(&ev) = erets.first() { val = self.prog.push_guarded(Op::Select { cond, t_val: ev, f_val: val }, self.cur_guard); }
        }
        Some(val)
    }
    fn parse_if(&mut self, c: &mut Cursor<'_>) -> Option<(Option<usize>, bool)> {
        let (cond, old_g, vars0) = (self.parse_expr(c)?, self.cur_guard, self.vars.clone());
        self.cur_guard = self.and_guard(old_g, (cond, true));
        let (t_rets, t_tail, t_ret) = self.parse_block(c)?;
        let vars_t = std::mem::replace(&mut self.vars, vars0.clone());
        let (f_rets, f_tail, f_ret, vars_f) = if c.eat_ident("else") {
            self.cur_guard = self.and_guard(old_g, (cond, false));
            let res = if c.eat_ident("if") { let (t, r) = self.parse_if(c)?; (Vec::new(), t, r) } else { self.parse_block(c)? };
            (res.0, res.1, res.2, std::mem::replace(&mut self.vars, vars0.clone()))
        } else { (Vec::new(), None, false, vars0.clone()) };
        self.cur_guard = old_g;
        for (k, v0) in vars0 {
            let (vt, vf) = (vars_t.get(&k).copied().unwrap_or(v0), vars_f.get(&k).copied().unwrap_or(v0));
            let mv = if vt == vf { vt } else if t_ret && !f_ret { vf } else if f_ret && !t_ret { vt } else { self.prog.push_guarded(Op::Select { cond, t_val: vt, f_val: vf }, old_g) };
            self.vars.insert(k, mv);
        }
        if t_ret && !f_ret { if !t_rets.is_empty() { self.early_rets.push((cond, t_rets)); } self.cur_guard = self.and_guard(old_g, (cond, false)); }
        else if f_ret && !t_ret { let nc = self.mk_bool(cond, false); if !f_rets.is_empty() { self.early_rets.push((nc, f_rets)); } self.cur_guard = self.and_guard(old_g, (cond, true)); }
        let val = match (t_tail, f_tail) { (Some(tt), Some(ft)) => Some(self.prog.push_guarded(Op::Select { cond, t_val: tt, f_val: ft }, old_g)), _ => None };
        Some((val, t_ret && f_ret))
    }
    fn parse_match_pat(&mut self, scrut: usize, c: &mut Cursor<'_>) -> Option<(Option<usize>, Option<String>)> {
        let (mut cond, mut bind): (Option<usize>, Option<String>) = (None, None);
        loop {
            let piece = match c.peek()? {
                Tok::Ident(s) if s == "_" => { c.pos += 1; None }
                Tok::Ident(s) if s == "true" || s == "false" => { let k = self.prog.push(Op::Const(i64::from(s == "true"))); c.pos += 1; Some(self.push_g(Op::Cmp(CmpKind::Eq, scrut, k))) }
                Tok::Ident(s) => { bind = Some(s.clone()); c.pos += 1; None }
                Tok::Sym("-") | Tok::Int(_) => {
                    let lo = c.parse_signed_tok()?;
                    if c.eat_sym("..=") {
                        let (klo, khi, z) = (self.prog.push(Op::Const(lo)), self.prog.push(Op::Const(c.parse_signed_tok()?)), self.prog.push(Op::Const(0)));
                        let (ge, le) = (self.push_g(Op::Cmp(CmpKind::Ge, scrut, klo)), self.push_g(Op::Cmp(CmpKind::Le, scrut, khi)));
                        Some(self.push_g(Op::Select { cond: ge, t_val: le, f_val: z }))
                    } else { let k = self.prog.push(Op::Const(lo)); Some(self.push_g(Op::Cmp(CmpKind::Eq, scrut, k))) }
                }
                _ => return None,
            };
            cond = match (cond, piece) { (None, p) => p, (c0, None) => c0, (Some(a), Some(b)) => { let one = self.prog.push(Op::Const(1)); Some(self.push_g(Op::Select { cond: a, t_val: one, f_val: b })) } };
            if !c.eat_sym("|") { break; }
        }
        Some((cond, bind))
    }
    fn parse_match(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        let scrut = self.parse_expr(c)?;
        if !c.eat_sym("{") { return None; }
        let (old_g, mut rem_g, mut arms) = (self.cur_guard, self.cur_guard, Vec::new());
        while !c.eat_sym("}") {
            let (pat_c, bind) = self.parse_match_pat(scrut, c)?;
            if !c.eat_sym("=>") { return None; }
            self.cur_guard = match pat_c { Some(pc) => self.and_guard(rem_g, (pc, true)), None => rem_g };
            let saved_bind = bind.as_ref().map(|k| (k.clone(), self.vars.insert(k.clone(), scrut)));
            let val = if matches!(c.peek(), Some(Tok::Sym("{"))) { self.parse_block(c)?.1? } else { self.parse_expr(c)? };
            if let Some((k, prev)) = saved_bind { if let Some(p) = prev { self.vars.insert(k, p); } else { self.vars.remove(&k); } }
            let _ = c.eat_sym(",");
            arms.push((pat_c, val));
            if let Some(pc) = pat_c { rem_g = self.and_guard(rem_g, (pc, false)); }
        }
        self.cur_guard = old_g;
        let mut it = arms.into_iter().rev(); let mut acc = it.next()?.1;
        for (pc, val) in it { if let Some(cond) = pc { acc = self.prog.push_guarded(Op::Select { cond, t_val: val, f_val: acc }, old_g); } }
        Some(acc)
    }
    fn parse_assert(&mut self, c: &mut Cursor<'_>) -> Option<()> {
        if !c.eat_sym("!") || !c.eat_sym("(") { return None; }
        loop {
            let nm = match c.peek() { Some(Tok::Ident(s)) => Some(s.clone()), _ => None };
            let (lhs, op, rhs) = (self.parse_binop(c, 4)?, match c.next()? { Tok::Sym(s) => *s, _ => return None }, self.parse_binop(c, 4)?);
            if let Op::Const(lim) = self.prog.nodes[rhs] {
                if let Some(limit) = match op { "<" if lim > 0 => Some(lim as usize), "<=" if lim >= 0 => usize::try_from(lim + 1).ok(), _ => None } {
                    let bc = self.push_g(Op::BoundsCheck { idx: lhs, limit });
                    if let Some(k) = nm.filter(|k| self.vars.contains_key(k)) { self.vars.insert(k, bc); }
                }
            }
            if !c.eat_sym("&&") { break; }
        }
        if !c.eat_sym(")") { return None; }
        let _ = c.eat_sym(";"); Some(())
    }
    fn looks_like_store(&self, c: &Cursor<'_>) -> bool {
        let mut k = c.pos + 1;
        if !matches!(c.toks.get(k), Some(Tok::Sym("["))) { return false; }
        let mut d = 1usize; k += 1;
        while k < c.toks.len() && d > 0 { match c.toks[k] { Tok::Sym("[") => d += 1, Tok::Sym("]") => d -= 1, _ => {} } k += 1; }
        matches!(c.toks.get(k), Some(Tok::Sym("=")))
    }
    fn parse_ret_values(&mut self, c: &mut Cursor<'_>, out: &mut Vec<usize>) -> Option<()> {
        if c.eat_sym("(") {
            if c.eat_sym(")") { return Some(()); }
            let (saved, first) = (c.pos, self.parse_expr(c)?);
            if c.eat_sym(",") { out.push(first); while !c.eat_sym(")") { out.push(self.parse_expr(c)?); let _ = c.eat_sym(","); } return Some(()); }
            c.pos = saved - 1;
        }
        out.push(self.parse_expr(c)?); Some(())
    }
    fn parse_block(&mut self, c: &mut Cursor<'_>) -> Option<(Vec<usize>, Option<usize>, bool)> {
        if !c.eat_sym("{") { return None; }
        let (mut rets, mut tail, mut returned) = (Vec::new(), None, false);
        while !c.eat_sym("}") {
            c.peek()?;
            if c.eat_ident("let") {
                let _ = c.eat_ident("mut"); let var = c.expect_ident()?;
                if c.eat_sym(":") { let _ = c.expect_ident()?; }
                if !c.eat_sym("=") { return None; }
                let val = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                self.vars.insert(var, val);
            } else if c.eat_ident("assert") { self.parse_assert(c)?; }
            else if c.eat_ident("if") {
                let (val, both_ret) = self.parse_if(c)?;
                if both_ret { returned = true; }
                let _ = c.eat_sym(";");
                if matches!(c.peek(), Some(Tok::Sym("}"))) { if let Some(v) = val { tail = Some(v); rets.push(v); } }
            } else if c.eat_ident("for") {
                let iv = c.expect_ident()?;
                if !c.eat_ident("in") { return None; }
                let lo = match c.next()? { &Tok::Int(v) => v, _ => return None };
                let inc = if c.eat_sym("..=") { true } else if c.eat_sym("..") { false } else { return None };
                let end = match c.next()? { &Tok::Int(v) => v.checked_add(i64::from(inc))?, _ => return None };
                if end < lo || (end - lo) > 16 { return None; }
                let bp = c.pos;
                if lo == end { c.skip_balanced("{", "}"); }
                else { for k in lo..end { c.pos = bp; let kid = self.prog.push(Op::Const(k)); self.vars.insert(iv.clone(), kid); rets.extend(self.parse_block(c)?.0); } }
            } else if c.eat_ident("return") {
                returned = true; if !c.eat_sym(";") { self.parse_ret_values(c, &mut rets)?; let _ = c.eat_sym(";"); }
            } else if matches!(c.peek(), Some(Tok::Ident(nm)) if self.bufs.contains_key(nm)) && self.looks_like_store(c) {
                let bb = *self.bufs.get(&c.expect_ident()?)?;
                if !c.eat_sym("[") { return None; }
                let idx = self.parse_expr(c)?;
                if !c.eat_sym("]") || !c.eat_sym("=") { return None; }
                let val = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                let ri = self.buf_index(bb, idx); let st = self.push_g(Op::Store { buf: bb.id, idx: ri, val }); self.stores.push(st);
            } else if matches!(c.peek(), Some(Tok::Ident(nm)) if self.vars.contains_key(nm)) && matches!(c.toks.get(c.pos + 1), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "&=" | "|=" | "^="))) {
                let (nm, op) = (c.expect_ident()?, match c.next()? { Tok::Sym(s) => *s, _ => return None });
                let r = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                let old = *self.vars.get(&nm)?;
                let nv = match op { "=" => r, "+=" => self.push_g(Op::Add(old, r)), "-=" => self.push_g(Op::Sub(old, r)), "*=" => self.push_g(Op::Mul(old, r)), "&=" => self.push_g(Op::BitAnd(old, r)), "|=" => self.push_g(Op::BitOr(old, r)), "^=" => self.push_g(Op::BitXor(old, r)), _ => return None };
                self.vars.insert(nm, nv);
            } else {
                let mut vals = Vec::new(); self.parse_ret_values(c, &mut vals)?;
                if c.eat_sym(";") { continue; }
                if vals.len() == 1 { tail = Some(vals[0]); }
                rets.extend(vals); return c.eat_sym("}").then_some((rets, tail, returned));
            }
        }
        Some((rets, tail, returned))
    }
}

fn scan_fn_items(toks: &[Tok]) -> Vec<FnItem> {
    let (mut c, mut items, mut pending) = (Cursor { toks, pos: 0 }, Vec::new(), FnMeta::default());
    while let Some(tok) = c.peek() {
        match tok {
            Tok::Doc(line) => { parse_doc_meta(line, &mut pending); c.pos += 1; }
            Tok::Sym("#") => { let _ = c.parse_attr(&mut pending); }
            Tok::Ident(w) if w == "pub" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); } }
            Tok::Ident(w) if matches!(w.as_str(), "const" | "unsafe" | "extern") => { c.pos += 1; }
            Tok::Ident(w) if w == "fn" => {
                c.pos += 1;
                let (name, sig_pos, meta) = (c.expect_ident().unwrap_or_else(|| "<anon>".to_string()), c.pos, std::mem::take(&mut pending));
                while let Some(t) = c.peek() { if matches!(t, Tok::Sym("{")) { break; } c.pos += 1; }
                c.skip_balanced("{", "}"); items.push(FnItem { name, sig_pos, meta });
            }
            Tok::Sym("{") => { pending = FnMeta::default(); c.skip_balanced("{", "}"); }
            _ => { pending = FnMeta::default(); c.pos += 1; }
        }
    }
    items
}

fn lower_fn_item(item: &FnItem, items: &[FnItem], toks: &[Tok], inlined: &mut BTreeSet<String>) -> Option<Program> {
    let mut c = Cursor { toks, pos: item.sig_pos };
    if !c.eat_sym("(") { return None; }
    let mut ctx = LowerCtx { prog: Program::new(&item.name), vars: BTreeMap::new(), bufs: BTreeMap::new(), stores: Vec::new(), cur_guard: None, early_rets: Vec::new(), fns: items, toks, depth: 0, inlined_fns: inlined };
    ctx.prog.simd_lanes = 1; let mut next_region = 1u16;
    while !c.eat_sym(")") {
        let (mut pm, mut pd, mut pu, mut pr) = (FnMeta::default(), None, false, None);
        loop {
            match c.peek() {
                Some(Tok::Doc(l)) => { parse_doc_meta(l, &mut pm); c.pos += 1; }
                Some(Tok::Sym("#")) => { let (d, u, r) = c.parse_attr(&mut pm); if d.is_some() { pd = d; } pu |= u; if r.is_some() { pr = r; } }
                _ => break,
            }
        }
        let _ = c.eat_ident("mut");
        let pname = c.expect_ident().filter(|p| p != "self")?;
        if !c.eat_sym(":") { return None; }
        let ov = pd.or_else(|| pm.domains.get(&pname).copied()).or_else(|| item.meta.domains.get(&pname).copied());
        let is_uninit = pu || pm.uninit.contains(&pname) || item.meta.uninit.contains(&pname);
        let reg_ov = pr.or_else(|| pm.regions.get(&pname).copied()).or_else(|| item.meta.regions.get(&pname).copied());
        if c.eat_sym("&") {
            let mutable = c.eat_ident("mut");
            let bd = c.eat_sym("[").then(|| c.expect_ident()).flatten().and_then(|e| scalar_type_domain(&e))?;
            if !c.eat_sym(";") { return None; }
            let &Tok::Int(len_i) = c.next()? else { return None; };
            if len_i <= 0 || !c.eat_sym("]") { return None; }
            let (region, offset) = reg_ov.unwrap_or_else(|| { let r = next_region; next_region = next_region.saturating_add(1); (r, 0) });
            let bid = if is_uninit { ctx.prog.add_uninit_buf(&pname, len_i as usize, mutable, region, offset, ov.unwrap_or(bd)) } else { ctx.prog.add_buf(&pname, len_i as usize, mutable, region, offset, ov.unwrap_or(bd)) };
            ctx.bufs.insert(pname, BufBind { id: bid, base: 0, len: len_i as usize, mutable });
        } else if let Some(bd) = c.expect_ident().and_then(|ty| scalar_type_domain(&ty)) {
            let pid = ctx.prog.add_param(ov.unwrap_or(bd)); ctx.vars.insert(pname, pid);
        } else { return None; }
        let _ = c.eat_sym(",");
    }
    if c.eat_sym("->") {
        if c.eat_sym("(") { while !c.eat_sym(")") { scalar_type_domain(&c.expect_ident()?)?; let _ = c.eat_sym(","); } } else { scalar_type_domain(&c.expect_ident()?)?; }
    }
    let (mut rets, _, _) = ctx.parse_block(&mut c)?;
    for (cond, erets) in ctx.early_rets.into_iter().rev() {
        for (i, &ev) in erets.iter().enumerate() { if let Some(rv) = rets.get_mut(i) { *rv = ctx.prog.push(Op::Select { cond, t_val: ev, f_val: *rv }); } else { rets.push(ev); } }
    }
    for r in rets { ctx.prog.add_output(r); }
    for s in ctx.stores { if !ctx.prog.outputs.contains(&s) { ctx.prog.add_output(s); } }
    Some(ctx.prog)
}

/// Parse kernel-subset Rust functions from raw `.rs` source into `Program` IR (2-pass with bounded helper inlining).
#[must_use] pub fn parse_rust_programs(src: &str) -> ParsedRustUnit {
    let (toks, mut programs, mut skipped_raw, mut inlined) = (tokenize_rust(src), Vec::new(), Vec::new(), BTreeSet::new());
    let items = scan_fn_items(&toks);
    for item in &items {
        if is_intrinsic(&item.name) { continue; }
        if let Some(p) = lower_fn_item(item, &items, &toks, &mut inlined) { programs.push(p); } else { skipped_raw.push(item.name.clone()); }
    }
    ParsedRustUnit { programs, skipped_non_kernel_fns: skipped_raw.into_iter().filter(|n| !inlined.contains(n)).collect() }
}

/// Parse and formally verify every kernel-subset function in a raw `.rs` source string.
#[must_use] pub fn verify_rust_functions(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> RustProofReport {
    let parsed = parse_rust_programs(src);
    let (mut proven, mut failed) = (Vec::new(), Vec::new());
    for prog in parsed.programs {
        let name = prog.name.clone();
        match verify_program(&prog, profile, cfg) { Ok(rep) => proven.push((name, rep)), Err(error) => failed.push(RustFnFailure { fn_name: name, error }) }
    }
    RustProofReport { file: file.to_string(), proven, failed, skipped_non_kernel_fns: parsed.skipped_non_kernel_fns }
}

/// Parse and verify all kernel-subset functions across a `.rs` file or crate directory.
pub fn verify_crate_functions(dir: &Path, profile: ArchProfile, cfg: RefineConfig) -> Result<Vec<RustProofReport>, VerifyError> { verify_crate_functions_skip(dir, profile, cfg, &[]) }
pub fn verify_crate_functions_skip(dir: &Path, profile: ArchProfile, cfg: RefineConfig, skip: &[String]) -> Result<Vec<RustProofReport>, VerifyError> {
    let mut files = Vec::new(); crate::lint_rs::collect_rs_files(dir, skip, &mut files)?; files.sort();
    files.into_iter().map(|p| Ok(verify_rust_functions(&p.display().to_string(), &std::fs::read_to_string(&p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?, profile, cfg))).collect()
}
