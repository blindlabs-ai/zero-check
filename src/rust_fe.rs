use std::{collections::BTreeMap, path::Path};
use crate::abstract_eval::{ArchProfile, Domain, Op, Program, VerifyError};
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

fn parse_int_lit(raw: &str) -> Option<i64> {
    let clean: String = raw.chars().filter(|&c| c != '_').collect();
    let (radix, body) = [("0x", 16), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)]
        .into_iter().find_map(|(p, r)| clean.strip_prefix(p).map(|b| (r, b))).unwrap_or((10, clean.as_str()));
    let end = body.find(|c: char| !c.is_digit(radix)).unwrap_or(body.len());
    (end > 0).then(|| i64::from_str_radix(&body[..end], radix).ok()).flatten()
}

fn tokenize_rust(src: &str) -> Vec<Tok> {
    const MULTI: &[&str] = &["..=", "<<=", ">>=", "..", "->", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "&=", "|=", "^=", "::"];
    let (b, n, mut i, mut out) = (src.as_bytes(), src.len(), 0usize, Vec::new());
    while i < n {
        if b[i].is_ascii_whitespace() { i += 1; continue; }
        let rest = &src[i..];
        if rest.starts_with("///") {
            let s = i + 3; while i < n && b[i] != b'\n' { i += 1; } out.push(Tok::Doc(src[s..i].trim().to_string()));
        } else if rest.starts_with("//") { while i < n && b[i] != b'\n' { i += 1; } }
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
        else {
            let s = match b[i] {
                b'(' => "(", b')' => ")", b'{' => "{", b'}' => "}", b'[' => "[", b']' => "]", b',' => ",", b':' => ":",
                b';' => ";", b'=' => "=", b'+' => "+", b'-' => "-", b'*' => "*", b'/' => "/", b'%' => "%", b'&' => "&",
                b'|' => "|", b'^' => "^", b'<' => "<", b'>' => ">", b'!' => "!", b'.' => ".", b'#' => "#", _ => "?",
            };
            out.push(Tok::Sym(s)); i += 1;
        }
    }
    out
}

fn scalar_type_domain(ty: &str) -> Option<Domain> {
    Some(match ty {
        "u8" => Domain::range(0, 255), "u16" => Domain::range(0, 65_535), "u32" => Domain::range(0, 4_294_967_295),
        "u64" | "usize" => Domain::range(0, i64::MAX), "i8" => Domain::range(-128, 127), "i16" => Domain::range(-32_768, 32_767),
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
        let (ms, rs) = mstr.split_once("==")?;
        let (m, r) = (parse_signed(ms)?, parse_signed(rs)?);
        (m > 0).then(|| Domain::congruent(lo, hi, m, r))
    } else { Some(Domain::range(lo, hi)) }
}

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

struct Cursor<'a> { toks: &'a [Tok], pos: usize }
impl<'a> Cursor<'a> {
    fn peek(&self) -> Option<&'a Tok> { self.toks.get(self.pos) }
    fn next(&mut self) -> Option<&'a Tok> { let t = self.toks.get(self.pos); if t.is_some() { self.pos += 1; } t }
    fn eat_if(&mut self, pred: impl FnOnce(&Tok) -> bool) -> bool { if self.peek().is_some_and(pred) { self.pos += 1; true } else { false } }
    fn eat_sym(&mut self, s: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Sym(x) if *x == s)) }
    fn eat_ident(&mut self, kw: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Ident(x) if x == kw)) }
    fn expect_ident(&mut self) -> Option<String> { if let Some(Tok::Ident(s)) = self.peek() { self.pos += 1; Some(s.clone()) } else { None } }
    fn skip_balanced(&mut self, open: &str, close: &str) {
        if !self.eat_sym(open) { return; }
        let mut d = 1usize;
        while let Some(t) = self.next() {
            if matches!(t, Tok::Sym(s) if *s == open) { d += 1; } else if matches!(t, Tok::Sym(s) if *s == close) { d -= 1; if d == 0 { break; } }
        }
    }
    fn parse_attr_into(&mut self, named: &mut BTreeMap<String, Domain>) -> Option<Domain> {
        if !self.eat_sym("#") { return None; }
        let _ = self.eat_sym("!");
        if !self.eat_sym("[") { return None; }
        let (start, mut d) = (self.pos, 1usize);
        while let Some(t) = self.next() { match t { Tok::Sym("[") => d += 1, Tok::Sym("]") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let slice = &self.toks[start..self.pos.saturating_sub(1)];
        if !matches!(slice.first(), Some(Tok::Ident(n)) if n == "zero_domain") || slice.len() < 3 { return None; }
        let mut text = String::new();
        for t in &slice[1..] { match t { Tok::Ident(s) => { text.push(' '); text.push_str(s); } Tok::Int(v) => { text.push(' '); text.push_str(&v.to_string()); } Tok::Sym(s) => text.push_str(s), Tok::Doc(_) => {} } }
        collect_domain_spec(&text, named)
    }
}

fn bin_prec(sym: &str) -> Option<u8> {
    match sym { "|" => Some(1), "^" => Some(2), "&" => Some(3), "<<" | ">>" => Some(4), "+" | "-" => Some(5), "*" | "/" | "%" => Some(6), _ => None }
}

struct LowerCtx { prog: Program, vars: BTreeMap<String, usize>, bufs: BTreeMap<String, u8>, stores: Vec<usize> }
impl LowerCtx {
    fn parse_expr(&mut self, c: &mut Cursor<'_>) -> Option<usize> { self.parse_binop(c, 1) }
    fn parse_binop(&mut self, c: &mut Cursor<'_>, min_p: u8) -> Option<usize> {
        let mut l = self.parse_cast(c)?;
        while let Some(&Tok::Sym(op)) = c.peek() {
            let Some(p) = bin_prec(op).filter(|&p| p >= min_p) else { break; };
            c.pos += 1;
            let r = self.parse_binop(c, p + 1)?;
            let node = match op {
                "|" => Op::BitOr(l, r), "^" => Op::BitXor(l, r), "&" => Op::BitAnd(l, r), "+" => Op::Add(l, r),
                "-" => Op::Sub(l, r), "*" => Op::Mul(l, r), "/" => Op::Div(l, r), "%" => Op::Rem(l, r),
                "<<" | ">>" => match (op == "<<", self.prog.nodes[r]) {
                    (true, Op::Const(v)) if (0..=255).contains(&v) => Op::Shl(l, v as u8),
                    (false, Op::Const(v)) if (0..=255).contains(&v) => Op::Shr(l, v as u8),
                    (true, _) => Op::ShlVar(l, r), (false, _) => Op::ShrVar(l, r),
                },
                _ => return None,
            };
            l = self.prog.push(node);
        }
        Some(l)
    }
    fn parse_cast(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        let mut v = self.parse_unary(c)?;
        while c.eat_ident("as") {
            v = match c.expect_ident()?.as_str() {
                "u8" => { let m = self.prog.push(Op::Const(0xFF)); self.prog.push(Op::BitAnd(v, m)) }
                "u16" => { let m = self.prog.push(Op::Const(0xFFFF)); self.prog.push(Op::BitAnd(v, m)) }
                "u32" => { let m = self.prog.push(Op::Const(0xFFFF_FFFF)); self.prog.push(Op::BitAnd(v, m)) }
                "u64" | "usize" => self.prog.push(Op::BoundsCheck { idx: v, limit: (i64::MAX as usize).saturating_add(1) }),
                "i64" | "isize" | "i32" | "i16" | "i8" => v, _ => return None,
            };
        }
        Some(v)
    }
    fn parse_unary(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        if c.eat_sym("-") {
            if let Some(&Tok::Int(v)) = c.peek() { c.pos += 1; return Some(self.prog.push(Op::Const(v.checked_neg()?))); }
            let (r, z) = (self.parse_unary(c)?, self.prog.push(Op::Const(0)));
            return Some(self.prog.push(Op::Sub(z, r)));
        }
        self.parse_postfix(c)
    }
    fn parse_postfix(&mut self, c: &mut Cursor<'_>) -> Option<usize> {
        let mut base = match c.peek()? {
            &Tok::Int(v) => { c.pos += 1; self.prog.push(Op::Const(v)) }
            Tok::Sym("(") => { c.pos += 1; let x = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } x }
            Tok::Sym("{") => self.parse_block(c)?.1?,
            Tok::Ident(nm) => {
                let nm = nm.clone(); c.pos += 1;
                if c.eat_sym("[") { let (buf, idx) = (*self.bufs.get(&nm)?, self.parse_expr(c)?); if !c.eat_sym("]") { return None; } self.prog.push(Op::Load { buf, idx }) }
                else { *self.vars.get(&nm)? }
            }
            _ => return None,
        };
        while c.eat_sym(".") {
            let m = c.expect_ident()?;
            if !c.eat_sym("(") { return None; }
            let r = self.parse_expr(c)?;
            if !c.eat_sym(")") { return None; }
            base = match m.as_str() {
                "wrapping_add" => self.prog.push(Op::WrapAdd(base, r)), "wrapping_sub" => self.prog.push(Op::WrapSub(base, r)),
                "wrapping_mul" => self.prog.push(Op::WrapMul(base, r)),
                "wrapping_shl" | "wrapping_shr" => {
                    let shl = m == "wrapping_shl";
                    if let Op::Const(v) = self.prog.nodes[r] { self.prog.push(if shl { Op::Shl(base, (v & 63) as u8) } else { Op::Shr(base, (v & 63) as u8) }) }
                    else { let m63 = self.prog.push(Op::Const(63)); let s = self.prog.push(Op::BitAnd(r, m63)); self.prog.push(if shl { Op::ShlVar(base, s) } else { Op::ShrVar(base, s) }) }
                }
                _ => return None,
            };
        }
        Some(base)
    }
    fn parse_assert(&mut self, c: &mut Cursor<'_>) -> Option<()> {
        if !c.eat_sym("!") || !c.eat_sym("(") { return None; }
        loop {
            let nm = match c.peek() { Some(Tok::Ident(s)) => Some(s.clone()), _ => None };
            let (lhs, op, rhs) = (self.parse_expr(c)?, match c.next()? { Tok::Sym(s) => *s, _ => return None }, self.parse_expr(c)?);
            if let Op::Const(lim) = self.prog.nodes[rhs] {
                if let Some(limit) = match op { "<" if lim > 0 => Some(lim as usize), "<=" if lim >= 0 => usize::try_from(lim + 1).ok(), _ => None } {
                    let bc = self.prog.push(Op::BoundsCheck { idx: lhs, limit });
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
    fn parse_block(&mut self, c: &mut Cursor<'_>) -> Option<(Vec<usize>, Option<usize>)> {
        if !c.eat_sym("{") { return None; }
        let (mut rets, mut tail) = (Vec::new(), None);
        while !c.eat_sym("}") {
            c.peek()?;
            if c.eat_ident("let") {
                let _ = c.eat_ident("mut");
                let var = c.expect_ident()?;
                if c.eat_sym(":") { let _ = c.expect_ident()?; }
                if !c.eat_sym("=") { return None; }
                let val = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                self.vars.insert(var, val);
            } else if c.eat_ident("assert") { self.parse_assert(c)?; }
            else if c.eat_ident("for") {
                let iv = c.expect_ident()?;
                if !c.eat_ident("in") { return None; }
                let lo = match c.next()? { &Tok::Int(v) => v, _ => return None };
                let inc = if c.eat_sym("..=") { true } else if c.eat_sym("..") { false } else { return None };
                let hi = match c.next()? { &Tok::Int(v) => v, _ => return None };
                let end = if inc { hi.checked_add(1)? } else { hi };
                if end < lo || (end - lo) > 16 { return None; }
                let bp = c.pos;
                if lo == end { c.skip_balanced("{", "}"); } else { for k in lo..end { c.pos = bp; let kid = self.prog.push(Op::Const(k)); self.vars.insert(iv.clone(), kid); rets.extend(self.parse_block(c)?.0); } }
            } else if c.eat_ident("return") { if !c.eat_sym(";") { self.parse_ret_values(c, &mut rets)?; let _ = c.eat_sym(";"); } }
            else if matches!(c.peek(), Some(Tok::Ident(nm)) if self.bufs.contains_key(nm)) && self.looks_like_store(c) {
                let buf = *self.bufs.get(&c.expect_ident()?)?;
                if !c.eat_sym("[") { return None; }
                let idx = self.parse_expr(c)?;
                if !c.eat_sym("]") || !c.eat_sym("=") { return None; }
                let val = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                let st = self.prog.push(Op::Store { buf, idx, val }); self.stores.push(st);
            } else if matches!(c.peek(), Some(Tok::Ident(nm)) if self.vars.contains_key(nm)) && matches!(c.toks.get(c.pos + 1), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "&=" | "|=" | "^="))) {
                let (nm, op) = (c.expect_ident()?, match c.next()? { Tok::Sym(s) => *s, _ => return None });
                let r = self.parse_expr(c)?;
                if !c.eat_sym(";") { return None; }
                let old = *self.vars.get(&nm)?;
                let nv = match op { "=" => r, "+=" => self.prog.push(Op::Add(old, r)), "-=" => self.prog.push(Op::Sub(old, r)), "*=" => self.prog.push(Op::Mul(old, r)), "&=" => self.prog.push(Op::BitAnd(old, r)), "|=" => self.prog.push(Op::BitOr(old, r)), "^=" => self.prog.push(Op::BitXor(old, r)), _ => return None };
                self.vars.insert(nm, nv);
            } else {
                let mut vals = Vec::new(); self.parse_ret_values(c, &mut vals)?;
                if c.eat_sym(";") { continue; }
                if vals.len() == 1 { tail = Some(vals[0]); }
                rets.extend(vals);
                return c.eat_sym("}").then_some((rets, tail));
            }
        }
        Some((rets, tail))
    }
}

fn parse_fn_item(c: &mut Cursor<'_>, fn_domains: &BTreeMap<String, Domain>) -> (String, Option<Program>) {
    let name = c.expect_ident().unwrap_or_else(|| "<anon>".to_string());
    if !c.eat_sym("(") { return (name, None); }
    let mut ctx = LowerCtx { prog: Program::new(&name), vars: BTreeMap::new(), bufs: BTreeMap::new(), stores: Vec::new() };
    ctx.prog.simd_lanes = 1;
    let (mut next_region, mut ok) = (1u16, true);
    while !c.eat_sym(")") {
        if c.peek().is_none() { ok = false; break; }
        let (mut pdom_named, mut pdom_anon) = (BTreeMap::new(), None);
        while matches!(c.peek(), Some(Tok::Sym("#"))) { if let Some(d) = c.parse_attr_into(&mut pdom_named) { pdom_anon = Some(d); } }
        let _ = c.eat_ident("mut");
        let Some(pname) = c.expect_ident().filter(|p| p != "self") else { ok = false; break; };
        if !c.eat_sym(":") { ok = false; break; }
        let ov = pdom_anon.or_else(|| pdom_named.get(&pname).copied()).or_else(|| fn_domains.get(&pname).copied());
        if c.eat_sym("&") {
            let mutable = c.eat_ident("mut");
            let Some(bd) = c.eat_sym("[").then(|| c.expect_ident()).flatten().and_then(|e| scalar_type_domain(&e)) else { ok = false; break; };
            if !c.eat_sym(";") { ok = false; break; }
            let Some(&Tok::Int(len_i)) = c.next() else { ok = false; break; };
            if len_i <= 0 || !c.eat_sym("]") { ok = false; break; }
            let bid = ctx.prog.add_buf(&pname, len_i as usize, mutable, next_region, 0, ov.unwrap_or(bd));
            next_region = next_region.saturating_add(1); ctx.bufs.insert(pname, bid);
        } else if let Some(bd) = c.expect_ident().and_then(|ty| scalar_type_domain(&ty)) { let pid = ctx.prog.add_param(ov.unwrap_or(bd)); ctx.vars.insert(pname, pid); }
        else { ok = false; break; }
        let _ = c.eat_sym(",");
    }
    if ok && c.eat_sym("->") {
        if c.eat_sym("(") { while !c.eat_sym(")") { if c.expect_ident().and_then(|t| scalar_type_domain(&t)).is_none() { ok = false; break; } let _ = c.eat_sym(","); } }
        else if c.expect_ident().and_then(|t| scalar_type_domain(&t)).is_none() { ok = false; }
    }
    if !ok || !matches!(c.peek(), Some(Tok::Sym("{"))) {
        while let Some(t) = c.peek() { if matches!(t, Tok::Sym("{")) { break; } c.pos += 1; }
        c.skip_balanced("{", "}"); return (name, None);
    }
    let body_start = c.pos;
    if let Some((rets, _)) = ctx.parse_block(c) {
        for r in rets { ctx.prog.add_output(r); }
        if ctx.prog.outputs.is_empty() { for s in ctx.stores { ctx.prog.add_output(s); } }
        (name, Some(ctx.prog))
    } else { c.pos = body_start; c.skip_balanced("{", "}"); (name, None) }
}
/// Parse kernel-subset Rust functions from raw `.rs` source into `Program` IR.
#[must_use]
pub fn parse_rust_programs(src: &str) -> ParsedRustUnit {
    let toks = tokenize_rust(src);
    let mut c = Cursor { toks: &toks, pos: 0 };
    let (mut programs, mut skipped_non_kernel_fns, mut pending_domains) = (Vec::new(), Vec::new(), BTreeMap::new());
    while let Some(tok) = c.peek() {
        match tok {
            Tok::Doc(line) => { if let Some(rest) = line.strip_prefix("@domain").or_else(|| line.strip_prefix("@zero_domain")) { let _ = collect_domain_spec(rest, &mut pending_domains); } c.pos += 1; }
            Tok::Sym("#") => { let _ = c.parse_attr_into(&mut pending_domains); }
            Tok::Ident(w) if w == "pub" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); } }
            Tok::Ident(w) if matches!(w.as_str(), "const" | "unsafe" | "extern") => { c.pos += 1; }
            Tok::Ident(w) if w == "fn" => {
                c.pos += 1;
                let (name, prog) = parse_fn_item(&mut c, &std::mem::take(&mut pending_domains));
                if let Some(p) = prog { programs.push(p); } else { skipped_non_kernel_fns.push(name); }
            }
            Tok::Sym("{") => { pending_domains.clear(); c.skip_balanced("{", "}"); }
            _ => { pending_domains.clear(); c.pos += 1; }
        }
    }
    ParsedRustUnit { programs, skipped_non_kernel_fns }
}

/// Parse and formally verify every kernel-subset function in a raw `.rs` source string.
#[must_use]
pub fn verify_rust_functions(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> RustProofReport {
    let parsed = parse_rust_programs(src);
    let (mut proven, mut failed) = (Vec::new(), Vec::new());
    for prog in parsed.programs {
        let name = prog.name.clone();
        match verify_program(&prog, profile, cfg) { Ok(rep) => proven.push((name, rep)), Err(error) => failed.push(RustFnFailure { fn_name: name, error }) }
    }
    RustProofReport { file: file.to_string(), proven, failed, skipped_non_kernel_fns: parsed.skipped_non_kernel_fns }
}
/// Parse and verify all kernel-subset functions across a `.rs` file or crate directory.
pub fn verify_crate_functions(dir: &Path, profile: ArchProfile, cfg: RefineConfig) -> Result<Vec<RustProofReport>, VerifyError> {
    let mut files = Vec::new();
    crate::lint_rs::collect_rs_files(dir, &mut files)?;
    files.sort();
    files.into_iter().map(|p| Ok(verify_rust_functions(&p.display().to_string(), &std::fs::read_to_string(&p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?, profile, cfg))).collect()
}
