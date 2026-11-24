use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use crate::abstract_eval::{ArchProfile, CmpKind, Domain, IrOp, Op, Program, VerifyError};
use crate::simd_fuzz::{fault_name, refine_and_fuzz, sample_counterexample, Counterexample, RefineConfig};
use crate::{verify_program, ProgramReport};
pub const MAX_SYM_SLICE_LEN: usize = 65_536;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RustFeOptions { pub skip_cfg_test: bool, pub enforce_reg_budget: bool, pub interprocedural_reachability: bool }
impl Default for RustFeOptions { fn default() -> Self { Self { skip_cfg_test: false, enforce_reg_budget: true, interprocedural_reachability: false } } }
impl RustFeOptions { #[must_use] pub const fn external_audit() -> Self { Self { skip_cfg_test: true, enforce_reg_budget: false, interprocedural_reachability: true } } }
#[derive(Clone, Debug)]
pub struct ParsedRustUnit { pub programs: Vec<Program>, pub skipped_non_kernel_fns: Vec<String> }
#[derive(Clone, Debug)]
pub struct RustFnFailure { pub fn_name: String, pub error: VerifyError, pub poc_test: Option<String>, pub entrypoint_trace: Option<Vec<String>> }
#[derive(Clone, Debug)]
pub struct RustProofReport { pub file: String, pub proven: Vec<(String, ProgramReport)>, pub failed: Vec<RustFnFailure>, pub suppressed_guarded: Vec<crate::callgraph::SuppressedHelper>, pub skipped_non_kernel_fns: Vec<String> }
impl RustProofReport { #[must_use] pub fn is_clean(&self) -> bool { self.failed.is_empty() } }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScalarTy { Bool, U8, U16, U32, U64, Usize, I8, I16, I32, I64, Isize }
impl ScalarTy {
    fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "bool" => Self::Bool, "u8" => Self::U8, "u16" => Self::U16, "u32" => Self::U32, "u64" => Self::U64, "usize" => Self::Usize,
            "i8" => Self::I8, "i16" => Self::I16, "i32" => Self::I32, "i64" => Self::I64, "isize" => Self::Isize, _ => return None,
        })
    }
    const fn as_str(self) -> &'static str { match self { Self::Bool => "bool", Self::U8 => "u8", Self::U16 => "u16", Self::U32 => "u32", Self::U64 => "u64", Self::Usize => "usize", Self::I8 => "i8", Self::I16 => "i16", Self::I32 => "i32", Self::I64 => "i64", Self::Isize => "isize" } }
    const fn is_unsigned(self) -> bool { matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64 | Self::Usize) }
    const fn is_narrow(self) -> bool { matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::I8 | Self::I16 | Self::I32) }
    const fn bits(self) -> usize { match self { Self::Bool => 1, Self::U8 | Self::I8 => 8, Self::U16 | Self::I16 => 16, Self::U32 | Self::I32 => 32, _ => 64 } }
    const fn bounds(self) -> (i64, i64) {
        match self { Self::Bool => (0, 1), Self::U8 => (0, 255), Self::U16 => (0, 65_535), Self::U32 => (0, 4_294_967_295), Self::U64 | Self::Usize => (0, i64::MAX), Self::I8 => (-128, 127), Self::I16 => (-32_768, 32_767), Self::I32 => (-2_147_483_648, 2_147_483_647), Self::I64 | Self::Isize => (i64::MIN, i64::MAX) }
    }
    fn domain(self) -> Domain { let (lo, hi) = self.bounds(); Domain::range(lo, hi) }
    const fn fits_in(self, dst: Self) -> bool { let (sl, sh) = self.bounds(); let (dl, dh) = dst.bounds(); sl >= dl && sh <= dh }
    fn assoc_const(self, name: &str) -> Option<i64> {
        match name { "BITS" => Some(self.bits() as i64), "MIN" => Some(self.bounds().0), "MAX" if !matches!(self, Self::U64 | Self::Usize) => Some(self.bounds().1), _ => None }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok { Ident(String), Int(i64, Option<ScalarTy>), Doc(String), Sym(&'static str) }
fn is_intrinsic(name: &str) -> bool { matches!(name, "zero_alloc" | "zero_free" | "zero_check_gen" | "zero_uninit_read" | "zero_uninit_write") }
fn parse_int_tok(raw: &str) -> Option<(i64, Option<ScalarTy>)> {
    let clean: String = raw.chars().filter(|&c| c != '_').collect();
    let (radix, body) = [("0x", 16), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)]
        .into_iter().find_map(|(p, r)| clean.strip_prefix(p).map(|b| (r, b))).unwrap_or((10, clean.as_str()));
    let end = body.find(|c: char| !c.is_digit(radix)).unwrap_or(body.len()); if end == 0 { return None; }
    let suf = &body[end..]; let ty = if suf.is_empty() { None } else { Some(ScalarTy::from_name(suf)?) };
    Some((i64::from_str_radix(&body[..end], radix).ok()?, ty))
}
fn parse_byte_lit(b: &[u8], i: &mut usize) -> Option<Tok> {
    if *i + 2 >= b.len() || *b.get(*i)? != b'b' || *b.get(*i + 1)? != b'\'' { return None; }
    let mut k = *i + 2;
    let val = if *b.get(k)? == b'\\' {
        k += 1; let esc = *b.get(k)?; k += 1;
        match esc {
            b'n' => b'\n', b'r' => b'\r', b't' => b'\t', b'0' => 0, b'\\' => b'\\', b'\'' => b'\'', b'"' => b'"',
            b'x' => { let h = std::str::from_utf8(b.get(k..k + 2)?).ok()?; k += 2; u8::from_str_radix(h, 16).ok()? }
            _ => return None,
        }
    } else { let c = *b.get(k)?; k += 1; c }; if *b.get(k)? != b'\'' { return None; }
    *i = k + 1; Some(Tok::Int(i64::from(val), Some(ScalarTy::U8)))
}
fn skip_quoted(b: &[u8], i: &mut usize, quote: u8) {
    let n = b.len(); *i += 1;
    while *i < n {
        let c = b.get(*i).copied().unwrap_or(0); if c == b'\\' && *i + 1 < n { *i += 2; } else if c == quote { *i += 1; break; } else { *i += 1; }
    }
}
pub(crate) fn tokenize_rust(src: &str) -> Vec<Tok> {
    const MULTI: &[&str] = &["..=", "<<=", ">>=", "..", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "::"];
    const SINGLE: &[&str] = &["(", ")", "{", "}", "[", "]", ",", ":", ";", "=", "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "!", ".", "#", "?"];
    let (b, n, mut i, mut out) = (src.as_bytes(), src.len(), 0usize, Vec::new());
    while i < n {
        let c0 = b.get(i).copied().unwrap_or(0); if c0.is_ascii_whitespace() { i += 1; continue; }
        let rest = &b[i..];
        if rest.starts_with(b"///") { let s = i + 3; while i < n && b.get(i) != Some(&b'\n') { i += 1; } out.push(Tok::Doc(src[s..i].trim().to_string())); }
        else if rest.starts_with(b"//") { while i < n && b.get(i) != Some(&b'\n') { i += 1; } }
        else if rest.starts_with(b"/*") {
            let mut d = 1usize; i += 2;
            while i < n && d > 0 { if b[i..].starts_with(b"/*") { d += 1; i += 2; } else if b[i..].starts_with(b"*/") { d -= 1; i += 2; } else { i += 1; } }
        } else if c0 == b'b' && b.get(i + 1) == Some(&b'\'') {
            if let Some(t) = parse_byte_lit(b, &mut i) { out.push(t); } else { skip_quoted(b, &mut i, b'\''); out.push(Tok::Sym("@")); }
        } else if c0 == b'b' && b.get(i + 1) == Some(&b'"') { i += 1; skip_quoted(b, &mut i, b'"'); out.push(Tok::Sym("\"")); }
        else if c0 == b'r' && matches!(b.get(i + 1), Some(&b'"' | &b'#')) {
            let (mut k, mut hashes) = (i + 1, 0usize); while b.get(k) == Some(&b'#') { hashes += 1; k += 1; }
            if b.get(k) == Some(&b'"') {
                k += 1;
                while k < n { if b.get(k) == Some(&b'"') && b.get(k + 1..k + 1 + hashes).is_some_and(|s| s.iter().all(|&x| x == b'#')) { k += 1 + hashes; break; } k += 1; }
                i = k; out.push(Tok::Sym("\""));
            } else { i += 1; out.push(Tok::Ident("r".to_string())); }
        } else if c0 == b'"' { skip_quoted(b, &mut i, b'"'); out.push(Tok::Sym("\"")); }
        else if c0 == b'\'' {
            if b.get(i + 1) == Some(&b'\\') || b.get(i + 2) == Some(&b'\'') { skip_quoted(b, &mut i, b'\''); out.push(Tok::Sym("@")); }
            else { i += 1; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; } }
        } else if c0.is_ascii_alphabetic() || c0 == b'_' {
            let s = i; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; }
            out.push(Tok::Ident(src[s..i].to_string()));
        } else if c0.is_ascii_digit() {
            let s = i; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; }
            if b.get(i) == Some(&b'.') && b.get(i + 1).is_some_and(u8::is_ascii_digit) {
                i += 1; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; } out.push(Tok::Sym("@"));
            } else { out.push(parse_int_tok(&src[s..i]).map_or(Tok::Sym("@"), |(v, ty)| Tok::Int(v, ty))); }
        } else if let Some(&s) = MULTI.iter().find(|&&m| rest.starts_with(m.as_bytes())) { out.push(Tok::Sym(s)); i += s.len(); }
        else { out.push(Tok::Sym(SINGLE.iter().copied().find(|s| s.as_bytes().first() == Some(&c0)).unwrap_or("@"))); i += 1; }
    }
    out
}
fn parse_signed(raw: &str) -> Option<i64> {
    let s = raw.trim(); if let Some(r) = s.strip_prefix('-') { parse_int_tok(r.trim()).and_then(|(v, _)| v.checked_neg()) } else { parse_int_tok(s).map(|(v, _)| v) }
}
fn parse_domain_rhs(raw: &str) -> Option<Domain> {
    let s = raw.trim(); let (rp, mp) = match s.find("mod") { Some(p) => (s[..p].trim(), Some(s[p + 3..].trim())), None => (s, None) };
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
            if !key.is_empty() && key.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_') && !key.as_bytes().first().is_some_and(u8::is_ascii_digit) {
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
    fn peek_at(&self, off: usize) -> Option<&'a Tok> { self.toks.get(self.pos + off) }
    fn next(&mut self) -> Option<&'a Tok> { let t = self.toks.get(self.pos); if t.is_some() { self.pos += 1; } t }
    fn eat_if(&mut self, pred: impl FnOnce(&Tok) -> bool) -> bool { if self.peek().is_some_and(pred) { self.pos += 1; true } else { false } }
    fn eat_sym(&mut self, s: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Sym(x) if *x == s)) }
    fn eat_ident(&mut self, kw: &str) -> bool { self.eat_if(|t| matches!(t, Tok::Ident(x) if x == kw)) }
    fn expect_ident(&mut self) -> Option<String> { if let Some(Tok::Ident(s)) = self.peek() { self.pos += 1; Some(s.clone()) } else { None } }
    fn eat_empty_generics(&mut self) -> bool { if !self.eat_sym("<") { return true; } while self.eat_sym(",") {} self.eat_sym(">") }
    fn skip_angles(&mut self) {
        if !self.eat_sym("<") { return; }
        let mut d = 1usize;
        while let Some(t) = self.next() {
            match t { Tok::Sym("<") => d += 1, Tok::Sym(">") => { d -= 1; if d == 0 { break; } } Tok::Sym(">>") => { d = d.saturating_sub(2); if d == 0 { break; } } _ => {} }
        }
    }
    fn skip_until(&mut self, s1: &str, s2: &str, angles: bool) {
        let mut d = 0usize;
        while let Some(t) = self.peek() {
            match t {
                Tok::Sym(s) if d == 0 && (*s == s1 || *s == s2) => break,
                Tok::Sym("(" | "[") => { d += 1; self.pos += 1; }
                Tok::Sym("<") if angles => { d += 1; self.pos += 1; }
                Tok::Sym(")" | "]") => { d = d.saturating_sub(1); self.pos += 1; }
                Tok::Sym(">") if angles => { d = d.saturating_sub(1); self.pos += 1; }
                Tok::Sym(">>") if angles => { d = d.saturating_sub(2); self.pos += 1; }
                _ => self.pos += 1,
            }
        }
    }
    fn skip_balanced(&mut self, open: &str, close: &str) {
        if !self.eat_sym(open) { return; }
        let mut d = 1usize;
        while let Some(t) = self.next() { if matches!(t, Tok::Sym(s) if *s == open) { d += 1; } else if matches!(t, Tok::Sym(s) if *s == close) { d -= 1; if d == 0 { break; } } }
    }
    fn skip_rest_of_braces(&mut self) {
        let mut d = 1usize; while let Some(t) = self.next() { match t { Tok::Sym("{") => d += 1, Tok::Sym("}") => { d -= 1; if d == 0 { break; } } _ => {} } }
    }
    fn skip_item_body(&mut self) { self.skip_until("{", ";", false); if matches!(self.peek(), Some(Tok::Sym("{"))) { self.skip_balanced("{", "}"); } else { let _ = self.eat_sym(";"); } }
    fn skip_doc_and_attrs(&mut self) {
        while matches!(self.peek(), Some(Tok::Doc(_))) { self.pos += 1; }
        while matches!(self.peek(), Some(Tok::Sym("#"))) { let mut dm = FnMeta::default(); let _ = self.parse_attr(&mut dm); }
    }
    fn parse_attr(&mut self, meta: &mut FnMeta) -> (Option<Domain>, bool, Option<(u16, usize)>, bool) {
        if !self.eat_sym("#") { return (None, false, None, false); }
        let inner = self.eat_sym("!"); if !self.eat_sym("[") { return (None, false, None, false); }
        let (start, mut d) = (self.pos, 1usize); while let Some(t) = self.next() { match t { Tok::Sym("[") => d += 1, Tok::Sym("]") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let slice = self.toks.get(start..self.pos.saturating_sub(1)).unwrap_or(&[]); let Some(Tok::Ident(name)) = slice.first() else { return (None, false, None, false); };
        let is_test = !inner && (name == "test" || (name == "cfg" && slice.iter().any(|t| matches!(t, Tok::Ident(w) if w == "test" || w == "kani"))));
        if name == "zero_uninit" { return (None, true, None, is_test); }
        let mut text = String::new();
        for t in slice.get(1..).unwrap_or(&[]) {
            match t { Tok::Ident(s) => { text.push(' '); text.push_str(s); } Tok::Int(v, _) => { text.push(' '); text.push_str(&v.to_string()); } Tok::Sym(s) => text.push_str(s), Tok::Doc(_) => {} }
        }
        if name == "zero_domain" && slice.len() >= 3 { (collect_domain_spec(&text, &mut meta.domains), false, None, is_test) }
        else if name == "zero_region" { (None, false, parse_pair_region(&text), is_test) } else { (None, false, None, is_test) }
    }
}
struct FnItem { name: String, sig_pos: usize, meta: FnMeta, self_ty: Option<String>, is_test: bool, is_async: bool, is_unsafe: bool }
struct StructDef { fields: Vec<(String, ScalarTy)> }
struct EnumDef { variants: BTreeMap<String, i64>, max_disc: i64 }
#[derive(Default)]
struct FileIndex {
    fns: Vec<FnItem>, consts: BTreeMap<String, (i64, Option<ScalarTy>)>,
    structs: BTreeMap<String, StructDef>, enums: BTreeMap<String, EnumDef>, type_aliases: BTreeMap<String, ScalarTy>,
}
impl FileIndex {
    fn resolve_scalar(&self, name: &str) -> Option<ScalarTy> { ScalarTy::from_name(name).or_else(|| self.type_aliases.get(name).copied()) }
    fn eval_const_atom(&self, c: &mut Cursor<'_>, self_ty: Option<&str>) -> Option<(i64, Option<ScalarTy>)> {
        if c.eat_sym("-") { let (v, ty) = self.eval_const_atom(c, self_ty)?; return Some((v.checked_neg()?, ty)); }
        if c.eat_sym("(") { let r = self.eval_const_expr(c, self_ty)?; return c.eat_sym(")").then_some(r); }
        match c.peek()? {
            &Tok::Int(v, ty) => { c.pos += 1; Some((v, ty)) }
            Tok::Ident(nm) => {
                let nm = nm.clone(); c.pos += 1;
                if c.eat_sym("::") {
                    let (sub, base) = (c.expect_ident()?, if nm == "Self" { self_ty.unwrap_or(&nm) } else { nm.as_str() });
                    if let Some(st) = self.resolve_scalar(base) { return Some((st.assoc_const(&sub)?, Some(st))); }
                    if let Some(e) = self.enums.get(base) { return Some((*e.variants.get(&sub)?, Some(ScalarTy::Usize))); }
                    return self.consts.get(&format!("{base}::{sub}")).copied();
                }
                self.consts.get(&nm).copied()
            }
            _ => None,
        }
    }
    fn eval_const_expr(&self, c: &mut Cursor<'_>, self_ty: Option<&str>) -> Option<(i64, Option<ScalarTy>)> {
        let (mut v, mut ty) = self.eval_const_atom(c, self_ty)?;
        while let Some(&Tok::Sym(op)) = c.peek() {
            if !matches!(op, "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | "|" | "&" | "^") { break; }
            c.pos += 1; let (r, rty) = self.eval_const_atom(c, self_ty)?; ty = ty.or(rty);
            v = match op {
                "+" => v.checked_add(r)?, "-" => v.checked_sub(r)?, "*" => v.checked_mul(r)?, "/" => v.checked_div(r)?, "%" => v.checked_rem(r)?, "|" => v | r, "&" => v & r, "^" => v ^ r,
                "<<" if (0..64).contains(&r) => v.checked_shl(r as u32)?, ">>" if (0..64).contains(&r) => v.checked_shr(r as u32)?, _ => return None,
            };
        }
        if c.eat_ident("as") { let dt = self.resolve_scalar(&c.expect_ident()?)?; let (lo, hi) = dt.bounds(); if v < lo || v > hi { return None; } ty = Some(dt); }
        Some((v, ty))
    }
}
fn scan_const_item(c: &mut Cursor<'_>, idx: &mut FileIndex, prefix: Option<&str>) {
    let Some(name) = c.expect_ident() else { return; };
    if c.eat_sym(":") {
        let ty = c.expect_ident().and_then(|s| idx.resolve_scalar(&s));
        if let (Some(t), true) = (ty, c.eat_sym("=")) {
            if let Some((v, _)) = idx.eval_const_expr(c, prefix) { idx.consts.insert(prefix.map_or_else(|| name.clone(), |p| format!("{p}::{name}")), (v, Some(t))); }
        }
    }
    while let Some(t) = c.next() { match t { Tok::Sym(";") => break, Tok::Sym("{") => { c.pos -= 1; c.skip_balanced("{", "}"); } Tok::Sym("[") => { c.pos -= 1; c.skip_balanced("[", "]"); } _ => {} } }
}
fn scan_aggregate_item(c: &mut Cursor<'_>, idx: &mut FileIndex, is_enum: bool) {
    let Some(name) = c.expect_ident() else { return; }; if matches!(c.peek(), Some(Tok::Sym("<"))) || !c.eat_sym("{") { c.skip_item_body(); return; }
    if is_enum {
        let (mut variants, mut next_val, mut max_disc, mut ok) = (BTreeMap::new(), 0i64, 0i64, true);
        while !c.eat_sym("}") {
            c.skip_doc_and_attrs(); let Some(vname) = c.expect_ident() else { ok = false; break; }; if matches!(c.peek(), Some(Tok::Sym("(" | "{"))) { ok = false; break; }
            let v = if c.eat_sym("=") { if let Some((ev, _)) = idx.eval_const_expr(c, None) { ev } else { ok = false; break; } } else { next_val };
            variants.insert(vname, v); max_disc = max_disc.max(v); next_val = v.saturating_add(1); let _ = c.eat_sym(",");
        }
        if !ok { c.skip_rest_of_braces(); return; }
        if !variants.is_empty() && variants.values().all(|&v| v >= 0) { idx.enums.insert(name, EnumDef { variants, max_disc }); }
    } else {
        let (mut fields, mut ok) = (Vec::new(), true);
        while !c.eat_sym("}") {
            c.skip_doc_and_attrs(); if c.eat_ident("pub") && matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); }
            let Some(fname) = c.expect_ident() else { ok = false; break; }; if !c.eat_sym(":") { ok = false; break; }
            let Some(ty) = c.expect_ident().and_then(|s| idx.resolve_scalar(&s)) else { ok = false; break; }; fields.push((fname, ty)); let _ = c.eat_sym(",");
        }
        if !ok { c.skip_rest_of_braces(); return; }
        if !fields.is_empty() && fields.len() <= 8 { idx.structs.insert(name, StructDef { fields }); }
    }
}
fn scan_fn_decl(c: &mut Cursor<'_>, idx: &mut FileIndex, self_ty: Option<String>, meta: FnMeta, (is_test, is_async, is_unsafe): (bool, bool, bool)) {
    let raw = c.expect_ident().unwrap_or_else(|| "<anon>".to_string()); let (sig_pos, name) = (c.pos, self_ty.as_ref().map_or_else(|| raw.clone(), |t| format!("{t}::{raw}")));
    c.skip_until("{", ";", false);
    if matches!(c.peek(), Some(Tok::Sym("{"))) { c.skip_balanced("{", "}"); idx.fns.push(FnItem { name, sig_pos, meta, self_ty, is_test, is_async, is_unsafe }); } else { let _ = c.eat_sym(";"); }
}
fn scan_impl_block(c: &mut Cursor<'_>, idx: &mut FileIndex, impl_test: bool) {
    if !c.eat_empty_generics() { c.skip_item_body(); return; }
    let Some(ty_name) = c.expect_ident() else { c.skip_item_body(); return; }; if !c.eat_empty_generics() || !c.eat_sym("{") { c.skip_item_body(); return; }
    let (mut pending, mut fn_test, mut fn_async, mut fn_unsafe) = (FnMeta::default(), false, false, false);
    while !c.eat_sym("}") {
        match c.peek() {
            None => break,
            Some(Tok::Doc(line)) => { parse_doc_meta(line, &mut pending); c.pos += 1; }
            Some(Tok::Sym("#")) => { let (_, _, _, t) = c.parse_attr(&mut pending); fn_test |= t; }
            Some(Tok::Ident(w)) if w == "pub" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); } }
            Some(Tok::Ident(w)) if w == "const" => {
                c.pos += 1; if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe" | "async" | "extern")) { continue; }
                scan_const_item(c, idx, Some(&ty_name)); (pending, fn_test, fn_async, fn_unsafe) = (FnMeta::default(), false, false, false);
            }
            Some(Tok::Ident(w)) if w == "unsafe" => {
                c.pos += 1;
                if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "async" | "extern")) { fn_unsafe = true; }
                else { c.skip_item_body(); (pending, fn_test, fn_async, fn_unsafe) = (FnMeta::default(), false, false, false); }
            }
            Some(Tok::Ident(w)) if w == "extern" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("\""))) { c.pos += 1; } }
            Some(Tok::Ident(w)) if w == "async" => {
                c.pos += 1;
                if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe")) { fn_async = true; }
                else { c.skip_item_body(); (pending, fn_test, fn_async, fn_unsafe) = (FnMeta::default(), false, false, false); }
            }
            Some(Tok::Ident(w)) if w == "fn" => {
                c.pos += 1; let flags = (impl_test || std::mem::take(&mut fn_test), std::mem::take(&mut fn_async), std::mem::take(&mut fn_unsafe));
                scan_fn_decl(c, idx, Some(ty_name.clone()), std::mem::take(&mut pending), flags);
            }
            Some(Tok::Sym("{")) => { (pending, fn_test, fn_async, fn_unsafe) = (FnMeta::default(), false, false, false); c.skip_balanced("{", "}"); }
            _ => { (pending, fn_test, fn_async, fn_unsafe) = (FnMeta::default(), false, false, false); c.pos += 1; }
        }
    }
}
fn scan_file(toks: &[Tok]) -> FileIndex {
    let (mut c, mut idx, mut pending, mut is_test, mut is_async, mut is_unsafe) = (Cursor { toks, pos: 0 }, FileIndex::default(), FnMeta::default(), false, false, false);
    while let Some(tok) = c.peek() {
        match tok {
            Tok::Doc(line) => { parse_doc_meta(line, &mut pending); c.pos += 1; }
            Tok::Sym("#") => { let (_, _, _, t) = c.parse_attr(&mut pending); is_test |= t; }
            Tok::Ident(w) if w == "pub" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); } }
            Tok::Ident(w) if w == "unsafe" => {
                c.pos += 1;
                if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "async" | "extern")) { is_unsafe = true; }
                else { c.skip_item_body(); (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); }
            }
            Tok::Ident(w) if w == "extern" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Sym("\""))) { c.pos += 1; } }
            Tok::Ident(w) if w == "const" => {
                c.pos += 1; if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe" | "async" | "extern")) { continue; }
                scan_const_item(&mut c, &mut idx, None); (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false);
            }
            Tok::Ident(w) if w == "type" => {
                c.pos += 1;
                if let Some(nm) = c.expect_ident() { if c.eat_sym("=") { if let Some(ty) = c.expect_ident().and_then(|s| idx.resolve_scalar(&s)) { idx.type_aliases.insert(nm, ty); } } }
                while let Some(t) = c.next() { if matches!(t, Tok::Sym(";")) { break; } }
                (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false);
            }
            Tok::Ident(w) if w == "struct" || w == "enum" => { let ie = w == "enum"; c.pos += 1; scan_aggregate_item(&mut c, &mut idx, ie); (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); }
            Tok::Ident(w) if w == "impl" => { c.pos += 1; let it = std::mem::take(&mut is_test); (pending, is_async, is_unsafe) = (FnMeta::default(), false, false); scan_impl_block(&mut c, &mut idx, it); }
            Tok::Ident(w) if matches!(w.as_str(), "mod" | "trait") => { c.pos += 1; c.skip_item_body(); (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); }
            Tok::Ident(w) if w == "async" => {
                c.pos += 1;
                if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe")) { is_async = true; }
                else { c.skip_item_body(); (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); }
            }
            Tok::Ident(w) if w == "fn" => {
                c.pos += 1; let flags = (std::mem::take(&mut is_test), std::mem::take(&mut is_async), std::mem::take(&mut is_unsafe));
                scan_fn_decl(&mut c, &mut idx, None, std::mem::take(&mut pending), flags);
            }
            Tok::Sym("{") => { (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); c.skip_balanced("{", "}"); }
            _ => { (pending, is_test, is_async, is_unsafe) = (FnMeta::default(), false, false, false); c.pos += 1; }
        }
    }
    idx
}
#[derive(Clone, Copy, Debug)]
struct BufBind {
    id: u8, base_const: usize, base_node: Option<usize>, len_const: usize, len_node: Option<usize>,
    root_len: Option<usize>, mutable: bool, elem_ty: ScalarTy,
}
#[derive(Clone, Debug)]
enum Val { Scalar(usize, Option<ScalarTy>), Opt { is_some: usize, payload: Box<Val> }, Tuple(Vec<Val>), Struct(String, Vec<(String, Val)>), Buf(BufBind), Opaque }
type TypedVal = (usize, Option<ScalarTy>);
type RangeOrIdx = Result<TypedVal, (Option<TypedVal>, Option<TypedVal>, bool)>;
type PatMatch = (Option<usize>, Option<(String, Val)>);
type StructFields = Vec<(String, ScalarTy, usize)>;
type MutTarget = Option<(String, Option<String>)>;
pub(crate) struct LoweredFn { pub(crate) prog: Program, pub(crate) params: Vec<PocParam>, is_async: bool, has_opaque: bool }
type ParsedPocEntries = (FileIndex, Vec<LoweredFn>, Vec<String>);
#[derive(Clone, Debug)]
pub(crate) enum PocParam {
    Scalar { name: String, ty: ScalarTy, pidx: usize, by_ref: bool, mutable: bool }, Array { name: String, ety: ScalarTy, len: usize, by_ref: bool, mutable: bool },
    Slice { name: String, ety: ScalarTy, pidx: usize, mutable: bool }, Opt { name: String, ty: ScalarTy, is_some: usize, val: usize },
    Struct { name: String, ty: String, fields: StructFields, by_ref: bool, mutable: bool }, Enum { name: String, ty: String, pidx: usize, by_ref: bool },
}
fn scalar_id(v: &Val) -> Option<(usize, Option<ScalarTy>)> { if let &Val::Scalar(id, ty) = v { Some((id, ty)) } else { None } }
fn bin_prec(sym: &str) -> Option<u8> {
    match sym { "||" => Some(1), "&&" => Some(2), "==" | "!=" | "<" | "<=" | ">" | ">=" => Some(3), "|" => Some(4), "^" => Some(5), "&" => Some(6), "<<" | ">>" => Some(7), "+" | "-" => Some(8), "*" | "/" | "%" => Some(9), _ => None }
}
struct LowerCtx<'a> {
    prog: Program, poc_params: Vec<PocParam>, vars: BTreeMap<String, Val>, mut_refs: BTreeSet<String>, stores: Vec<usize>, cur_guard: Option<(usize, bool)>,
    early_rets: Vec<(usize, Val)>, file: &'a FileIndex, toks: &'a [Tok], depth: u8, inlined_fns: &'a mut BTreeSet<String>,
    next_region: u16, self_ty: Option<String>, no_struct_lit: bool, returns_opt: bool, is_async: bool, has_opaque: bool,
}
impl<'a> LowerCtx<'a> {
    fn push_g(&mut self, op: IrOp) -> usize { self.prog.push_guarded(op, self.cur_guard) }
    fn mk_bool(&mut self, c: usize, pol: bool) -> usize { if pol { c } else { let z = self.prog.push(Op::Const(0)); self.prog.push(Op::Cmp(CmpKind::Eq, c, z)) } }
    fn and_guard(&mut self, old: Option<(usize, bool)>, add: (usize, bool)) -> Option<(usize, bool)> {
        let Some((g0, p0)) = old else { return Some(add); }; let (b0, b1, z) = (self.mk_bool(g0, p0), self.mk_bool(add.0, add.1), self.prog.push(Op::Const(0)));
        Some((self.prog.push(Op::Select { cond: b0, t_val: b1, f_val: z }), true))
    }
    fn alloc_region(&mut self) -> u16 { let r = self.next_region; self.next_region = self.next_region.saturating_add(1); r }
    fn resolve_ty<'b>(&'b self, raw: &'b str) -> &'b str { if raw == "Self" { self.self_ty.as_deref().unwrap_or(raw) } else { raw } }
    fn const_of(&self, id: usize) -> Option<i64> { if let Some(&Op::Const(v)) = self.prog.nodes.get(id) { Some(v) } else { None } }
    fn buf_len_node(&mut self, bb: BufBind) -> usize { bb.len_node.unwrap_or_else(|| self.prog.push(Op::Const(bb.len_const as i64))) }
    fn mk_none(&mut self) -> Val { let z = self.prog.push(Op::Const(0)); Val::Opt { is_some: z, payload: Box::new(Val::Scalar(z, None)) } }
    fn is_const_zero_opt(&self, v: &Val) -> bool { matches!(v, Val::Opt { is_some, .. } if self.const_of(*is_some) == Some(0)) }
    fn in_bounds(&mut self, v: usize, lo: i64, hi: i64, inc: bool) -> usize {
        let (klo, khi, z) = (self.prog.push(Op::Const(lo)), self.prog.push(Op::Const(hi)), self.prog.push(Op::Const(0)));
        let (ge, le) = (self.push_g(Op::Cmp(CmpKind::Ge, v, klo)), self.push_g(Op::Cmp(if inc { CmpKind::Le } else { CmpKind::Lt }, v, khi)));
        self.push_g(Op::Select { cond: ge, t_val: le, f_val: z })
    }
    fn store_guarded(&mut self, buf: u8, idx: usize, val: usize, lo: usize, hi: usize) {
        let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let (ge, lt) = (self.push_g(Op::Cmp(CmpKind::Ge, idx, lo)), self.push_g(Op::Cmp(CmpKind::Lt, idx, hi)));
        let ok = self.push_g(Op::Select { cond: ge, t_val: lt, f_val: z }); self.cur_guard = self.and_guard(old_g, (ok, true));
        let st = self.push_g(Op::Store { buf, idx, val }); self.stores.push(st); self.cur_guard = old_g;
    }
    fn zero_like(&mut self, v: &Val) -> Val {
        match v {
            Val::Scalar(_, ty) => Val::Scalar(self.prog.push(Op::Const(0)), *ty),
            Val::Opt { payload, .. } => { let z = self.prog.push(Op::Const(0)); Val::Opt { is_some: z, payload: Box::new(self.zero_like(payload)) } }
            Val::Tuple(xs) => Val::Tuple(xs.iter().map(|x| self.zero_like(x)).collect()),
            Val::Struct(n, fs) => Val::Struct(n.clone(), fs.iter().map(|(k, x)| (k.clone(), self.zero_like(x))).collect()),
            Val::Buf(b) => Val::Buf(*b), Val::Opaque => Val::Opaque,
        }
    }
    fn merge_opt_node(&mut self, cond: usize, a: Option<usize>, b: Option<usize>, guard: Option<(usize, bool)>) -> Option<Option<usize>> {
        match (a, b) {
            (Some(x), Some(y)) => Some(Some(if x == y { x } else { self.prog.push_guarded(Op::Select { cond, t_val: x, f_val: y }, guard) })),
            (None, None) => Some(None), _ => None,
        }
    }
    fn merge_val(&mut self, cond: usize, tv: Val, fv: Val, guard: Option<(usize, bool)>) -> Option<Val> {
        match (tv, fv) {
            (Val::Scalar(a, ta), Val::Scalar(b, tb)) => Some(Val::Scalar(if a == b { a } else { self.prog.push_guarded(Op::Select { cond, t_val: a, f_val: b }, guard) }, ta.or(tb))),
            (Val::Opt { is_some: sa, payload: pa }, Val::Opt { is_some: sb, payload: pb }) => {
                let is_some = if sa == sb { sa } else { self.prog.push_guarded(Op::Select { cond, t_val: sa, f_val: sb }, guard) };
                let payload = if self.const_of(sa) == Some(0) { *pb } else if self.const_of(sb) == Some(0) { *pa } else { self.merge_val(cond, *pa, *pb, guard)? };
                Some(Val::Opt { is_some, payload: Box::new(payload) })
            }
            (Val::Tuple(va), Val::Tuple(vb)) if va.len() == vb.len() => Some(Val::Tuple(va.into_iter().zip(vb).map(|(a, b)| self.merge_val(cond, a, b, guard)).collect::<Option<Vec<_>>>()?)),
            (Val::Struct(na, fa), Val::Struct(nb, fb)) if na == nb && fa.len() == fb.len() => {
                Some(Val::Struct(na, fa.into_iter().zip(fb).map(|((ka, va), (_, vb))| Some((ka, self.merge_val(cond, va, vb, guard)?))).collect::<Option<Vec<_>>>()?))
            }
            (Val::Buf(a), Val::Buf(b)) if a.id == b.id && a.mutable == b.mutable && a.elem_ty == b.elem_ty && a.base_const == b.base_const && a.len_const == b.len_const && a.root_len == b.root_len => {
                Some(Val::Buf(BufBind { base_node: self.merge_opt_node(cond, a.base_node, b.base_node, guard)?, len_node: self.merge_opt_node(cond, a.len_node, b.len_node, guard)?, ..a }))
            }
            (Val::Opaque, Val::Opaque) => Some(Val::Opaque), _ => None,
        }
    }
    fn flatten_val(v: &Val, out: &mut Vec<usize>) {
        match v {
            Val::Scalar(id, _) => out.push(*id), Val::Opt { is_some, payload } => { out.push(*is_some); Self::flatten_val(payload, out); }
            Val::Tuple(xs) => for x in xs { Self::flatten_val(x, out); }, Val::Struct(_, fs) => for (_, x) in fs { Self::flatten_val(x, out); }, Val::Buf(_) | Val::Opaque => {}
        }
    }
    fn emit_range_check(&mut self, val: usize, ty: ScalarTy) {
        if !ty.is_narrow() { return; }
        let (lo, hi) = ty.bounds(); if !ty.is_unsigned() { let lok = self.prog.push(Op::Const(lo)); let ge = self.push_g(Op::Cmp(CmpKind::Ge, val, lok)); self.push_g(Op::PanicIfZero(ge, 4)); }
        let hik = self.prog.push(Op::Const(hi)); let le = self.push_g(Op::Cmp(CmpKind::Le, val, hik)); self.push_g(Op::PanicIfZero(le, 4));
    }
    fn emit_nonneg_check(&mut self, val: usize, ty: Option<ScalarTy>) {
        if ty.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { return; }
        let z = self.prog.push(Op::Const(0)); let ge = self.push_g(Op::Cmp(CmpKind::Ge, val, z)); self.push_g(Op::PanicIfZero(ge, 2));
    }
    fn buf_index(&mut self, bb: BufBind, idx: usize) -> usize {
        let checked = if let Some(ln) = bb.len_node { self.push_g(Op::DynBoundsCheck(idx, ln)) }
            else if bb.base_const == 0 && bb.base_node.is_none() && self.prog.bufs.get(usize::from(bb.id)).is_some_and(|b| b.len == bb.len_const) { return idx; }
            else { self.push_g(Op::BoundsCheck { idx, limit: bb.len_const }) };
        let ri = if let Some(bn) = bb.base_node { self.push_g(Op::Add(bn, checked)) }
            else if bb.base_const > 0 { let off = self.prog.push(Op::Const(bb.base_const as i64)); self.push_g(Op::Add(checked, off)) } else { checked };
        if let Some(rl) = bb.root_len { if bb.len_node != Some(rl) { return self.push_g(Op::DynBoundsCheck(ri, rl)); } }
        ri
    }
    fn make_subslice(&mut self, bb: BufBind, lo: Option<(usize, Option<ScalarTy>)>, hi: Option<(usize, Option<ScalarTy>)>, inc: bool, checked_opt: bool, mutable: bool) -> Option<(Option<usize>, BufBind)> {
        if mutable && !bb.mutable { return None; }
        let (len_n, (a_id, a_ty)) = (self.buf_len_node(bb), lo.unwrap_or_else(|| (self.prog.push(Op::Const(0)), Some(ScalarTy::Usize))));
        let b_id = match hi { Some((h, _)) if inc => { let one = self.prog.push(Op::Const(1)); self.push_g(Op::Add(h, one)) } Some((h, _)) => h, None => len_n };
        let ok_opt = if checked_opt {
            let (le1, le2, z) = (self.push_g(Op::Cmp(CmpKind::Le, a_id, b_id)), self.push_g(Op::Cmp(CmpKind::Le, b_id, len_n)), self.prog.push(Op::Const(0)));
            let mut ok = self.push_g(Op::Select { cond: le1, t_val: le2, f_val: z });
            if !a_ty.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { let ge0 = self.push_g(Op::Cmp(CmpKind::Ge, a_id, z)); ok = self.push_g(Op::Select { cond: ge0, t_val: ok, f_val: z }); }
            Some(ok)
        } else {
            self.emit_nonneg_check(a_id, a_ty); let (le1, le2) = (self.push_g(Op::Cmp(CmpKind::Le, a_id, b_id)), self.push_g(Op::Cmp(CmpKind::Le, b_id, len_n)));
            self.push_g(Op::PanicIfZero(le1, 2)); self.push_g(Op::PanicIfZero(le2, 2)); None
        }; let old_g = self.cur_guard; if let Some(ok) = ok_opt { self.cur_guard = self.and_guard(old_g, (ok, true)); }
        let (sub_bc, sub_bn, sub_lc, sub_ln) = match (self.const_of(a_id), self.const_of(b_id), bb.base_node, bb.len_node) {
            (Some(ac), Some(bc), None, None) if ac >= 0 && bc >= ac => (bb.base_const + ac as usize, None, (bc - ac) as usize, None),
            _ => {
                let bn = match (bb.base_node, bb.base_const, self.const_of(a_id)) {
                    (Some(b0), _, Some(0)) => Some(b0), (Some(b0), _, _) => Some(self.push_g(Op::Add(b0, a_id))), (None, 0, Some(0)) => None, (None, 0, _) => Some(a_id),
                    (None, bc, _) => { let k = self.prog.push(Op::Const(bc as i64)); Some(self.push_g(Op::Add(k, a_id))) }
                };
                (0, bn, bb.len_const, Some(self.push_g(Op::Sub(b_id, a_id))))
            }
        }; self.cur_guard = old_g;
        Some((ok_opt, BufBind { id: bb.id, base_const: sub_bc, base_node: sub_bn, len_const: sub_lc, len_node: sub_ln, root_len: bb.root_len.or(bb.len_node), mutable, elem_ty: bb.elem_ty }))
    }
    fn apply_binop(&mut self, op: &str, l: usize, lt: Option<ScalarTy>, r: usize, rt: Option<ScalarTy>) -> Option<Val> {
        let ty = lt.or(rt);
        match op {
            "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                let k = match op { "==" => CmpKind::Eq, "!=" => CmpKind::Ne, "<" => CmpKind::Lt, "<=" => CmpKind::Le, ">" => CmpKind::Gt, _ => CmpKind::Ge };
                Some(Val::Scalar(self.push_g(Op::Cmp(k, l, r)), Some(ScalarTy::Bool)))
            }
            "|" | "^" | "&" => Some(Val::Scalar(self.push_g(match op { "|" => Op::BitOr(l, r), "^" => Op::BitXor(l, r), _ => Op::BitAnd(l, r) }), ty)),
            "+" | "*" => {
                let res = self.push_g(if op == "+" { Op::Add(l, r) } else { Op::Mul(l, r) });
                if let Some(t) = ty.filter(|t| t.is_narrow()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty))
            }
            "-" => {
                if matches!(ty, Some(ScalarTy::U64 | ScalarTy::Usize)) && self.const_of(r) == Some(1) {
                    match self.prog.nodes.get(l).copied() {
                        Some(Op::Shl(a, s)) if self.const_of(a) == Some(1) && s < 64 => { let mx = self.prog.push(Op::Const(i64::MAX)); return Some(Val::Scalar(self.push_g(Op::Shr(mx, 63 - s)), ty)); }
                        Some(Op::ShlVar(a, s)) if self.const_of(a) == Some(1) => { let (c63, mx) = (self.prog.push(Op::Const(63)), self.prog.push(Op::Const(i64::MAX))); let inv = self.push_g(Op::Sub(c63, s)); return Some(Val::Scalar(self.push_g(Op::ShrVar(mx, inv)), ty)); }
                        _ => {}
                    }
                }
                if ty.is_some_and(ScalarTy::is_unsigned) { let ge = self.push_g(Op::Cmp(CmpKind::Ge, l, r)); self.push_g(Op::PanicIfZero(ge, 4)); }
                let res = self.push_g(Op::Sub(l, r));
                if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty))
            }
            "/" | "%" => {
                let res = self.push_g(if op == "/" { Op::Div(l, r) } else { Op::Rem(l, r) });
                if op == "/" { if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); } } Some(Val::Scalar(res, ty))
            }
            "<<" | ">>" => {
                let (shl, bits) = (op == "<<", lt.map_or(64, ScalarTy::bits)); let r_use = if bits < 64 { self.push_g(Op::BoundsCheck { idx: r, limit: bits }) } else { r };
                let mut res = match self.const_of(r) {
                    Some(v) if (0..bits as i64).contains(&v) || (bits == 64 && (0..=255).contains(&v)) => self.push_g(if shl { Op::Shl(l, v as u8) } else { Op::Shr(l, v as u8) }),
                    _ => self.push_g(if shl { Op::ShlVar(l, r_use) } else { Op::ShrVar(l, r_use) }),
                }; if shl { if let Some(t) = lt.filter(|t| t.is_narrow() && t.is_unsigned()) { let m = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, m)); } }
                Some(Val::Scalar(res, lt))
            }
            _ => None,
        }
    }
    fn parse_expr_head(&mut self, c: &mut Cursor<'_>) -> Option<Val> { let p = self.no_struct_lit; self.no_struct_lit = true; let r = self.parse_expr(c); self.no_struct_lit = p; r }
    fn parse_expr(&mut self, c: &mut Cursor<'_>) -> Option<Val> { self.parse_binop(c, 1) }
    fn parse_binop(&mut self, c: &mut Cursor<'_>, min_p: u8) -> Option<Val> {
        let mut lv = self.parse_cast(c)?;
        while let Some(&Tok::Sym(op)) = c.peek() {
            let Some(p) = bin_prec(op).filter(|&p| p >= min_p) else { break; }; let (l, lt) = scalar_id(&lv)?; c.pos += 1;
            if op == "&&" || op == "||" {
                let old_g = self.cur_guard; self.cur_guard = self.and_guard(old_g, (l, op == "&&")); let rv = self.parse_binop(c, p + 1)?; let (r, _) = scalar_id(&rv)?; self.cur_guard = old_g;
                let k = self.prog.push(Op::Const(i64::from(op == "||")));
                let id = self.prog.push_guarded(if op == "&&" { Op::Select { cond: l, t_val: r, f_val: k } } else { Op::Select { cond: l, t_val: k, f_val: r } }, old_g);
                lv = Val::Scalar(id, Some(ScalarTy::Bool)); continue;
            }
            let rv = self.parse_binop(c, p + 1)?; let (r, rt) = scalar_id(&rv)?; lv = self.apply_binop(op, l, lt, r, rt)?;
        }
        Some(lv)
    }
    fn parse_cast(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        let mut val = self.parse_unary(c)?;
        while c.eat_ident("as") {
            let ((v, src_ty), dst) = (scalar_id(&val)?, self.file.resolve_scalar(&c.expect_ident()?)?);
            let nv = match dst {
                ScalarTy::U8 | ScalarTy::U16 | ScalarTy::U32 => { let m = self.prog.push(Op::Const(dst.bounds().1)); self.push_g(Op::BitAnd(v, m)) }
                ScalarTy::U64 => v,
                ScalarTy::Usize => if src_ty.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { v } else { self.push_g(Op::BoundsCheck { idx: v, limit: (i64::MAX as usize).saturating_add(1) }) },
                ScalarTy::I8 | ScalarTy::I16 | ScalarTy::I32 => if src_ty.is_some_and(|st| st.fits_in(dst)) { v } else { let s = (64 - dst.bits()) as u8; let sh = self.push_g(Op::Shl(v, s)); self.push_g(Op::Shr(sh, s)) },
                ScalarTy::I64 | ScalarTy::Isize | ScalarTy::Bool => v,
            }; val = Val::Scalar(nv, Some(dst));
        }
        Some(val)
    }
    fn parse_unary(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        if c.eat_sym("-") {
            if let Some(&Tok::Int(v, ty)) = c.peek() { c.pos += 1; return Some(Val::Scalar(self.prog.push(Op::Const(v.checked_neg()?)), ty)); }
            let rv = self.parse_unary(c)?; let ((r, rty), z) = (scalar_id(&rv)?, self.prog.push(Op::Const(0))); let res = self.push_g(Op::Sub(z, r));
            if let Some(t) = rty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); }
            return Some(Val::Scalar(res, rty));
        }
        if c.eat_sym("!") {
            let rv = self.parse_unary(c)?; let (r, rty) = scalar_id(&rv)?;
            if rty == Some(ScalarTy::Bool) || matches!(self.prog.nodes.get(r), Some(Op::Cmp(..))) {
                let z = self.prog.push(Op::Const(0)); return Some(Val::Scalar(self.push_g(Op::Cmp(CmpKind::Eq, r, z)), Some(ScalarTy::Bool)));
            }
            let mk = self.prog.push(Op::Const(rty.filter(|t| t.is_narrow() && t.is_unsigned()).map_or(-1, |t| t.bounds().1))); return Some(Val::Scalar(self.push_g(Op::BitXor(r, mk)), rty));
        }
        if c.eat_sym("*") { return self.parse_unary(c); }
        if c.eat_sym("&") {
            let is_mut = c.eat_ident("mut");
            return match self.parse_unary(c)? { Val::Buf(bb) => (!is_mut || bb.mutable).then_some(Val::Buf(BufBind { mutable: is_mut, ..bb })), other => Some(other) };
        }
        self.parse_postfix(c)
    }
    fn parse_array_lit(&mut self, c: &mut Cursor<'_>, elem_hint: Option<ScalarTy>) -> Option<Val> {
        let first = self.parse_expr(c)?;
        let (elems, ety) = if c.eat_sym(";") {
            let (v, vty) = scalar_id(&first)?; let len_v = self.parse_expr(c)?; let len = usize::try_from(self.const_of(scalar_id(&len_v)?.0)?).ok()?;
            if len == 0 || len > 64 || !c.eat_sym("]") { return None; }
            (vec![v; len], elem_hint.or(vty).unwrap_or(ScalarTy::I64))
        } else {
            let mut xs = vec![scalar_id(&first)?]; let mut closed = c.eat_sym("]");
            while !closed && c.eat_sym(",") { if c.eat_sym("]") { closed = true; break; } let ev = self.parse_expr(c)?; xs.push(scalar_id(&ev)?); if xs.len() > 64 { return None; } }
            if !closed && !c.eat_sym("]") { return None; }
            let ety = elem_hint.or_else(|| xs.iter().find_map(|(_, t)| *t)).unwrap_or(ScalarTy::I64);
            (xs.into_iter().map(|(id, _)| id).collect(), ety)
        }; let reg = self.alloc_region(); let all_same = elems.first().and_then(|&id| self.const_of(id)).filter(|&cv| elems.iter().all(|&id| self.const_of(id) == Some(cv)));
        let bid = if let Some(cv) = all_same { self.prog.add_buf(format!("__arr_{reg}"), elems.len(), true, reg, 0, Domain::exact(cv)) } else {
            let id = self.prog.add_buf(format!("__arr_{reg}"), elems.len(), true, reg, 0, ety.domain());
            for (k, &val) in elems.iter().enumerate() { let ki = self.prog.push(Op::Const(k as i64)); let st = self.push_g(Op::Store { buf: id, idx: ki, val }); self.stores.push(st); } id
        };
        Some(Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: elems.len(), len_node: None, root_len: None, mutable: true, elem_ty: ety }))
    }
    fn parse_struct_lit(&mut self, name: &str, c: &mut Cursor<'_>) -> Option<Val> {
        let (def, mut map, mut base_fs) = (self.file.structs.get(name)?, BTreeMap::new(), None);
        while !c.eat_sym("}") {
            if c.eat_sym("..") {
                let Val::Struct(bn, bfs) = self.parse_expr(c)? else { return None; };
                if bn != name { return None; } base_fs = Some(bfs); let _ = c.eat_sym(","); if !c.eat_sym("}") { return None; } break;
            }
            let fname = c.expect_ident()?; let val = if c.eat_sym(":") { self.parse_expr(c)? } else { self.vars.get(&fname)?.clone() }; map.insert(fname, val); let _ = c.eat_sym(",");
        }
        let mut ordered = Vec::with_capacity(def.fields.len());
        for (fname, fty) in &def.fields {
            let v = map.remove(fname).or_else(|| base_fs.as_ref()?.iter().find(|(k, _)| k == fname).map(|(_, v)| v.clone()))?;
            ordered.push((fname.clone(), Val::Scalar(scalar_id(&v)?.0, Some(*fty))));
        }
        Some(Val::Struct(name.to_string(), ordered))
    }
    fn parse_range_or_idx(&mut self, c: &mut Cursor<'_>, end_sym: &str) -> Option<RangeOrIdx> {
        if c.eat_sym("..=") { let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((None, Some(scalar_id(&hv)?), true))); }
        if c.eat_sym("..") { if c.eat_sym(end_sym) { return Some(Err((None, None, false))); } let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((None, Some(scalar_id(&hv)?), false))); }
        let fv = self.parse_expr(c)?; let first = scalar_id(&fv)?;
        if c.eat_sym("..=") { let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((Some(first), Some(scalar_id(&hv)?), true))); }
        if c.eat_sym("..") { if c.eat_sym(end_sym) { return Some(Err((Some(first), None, false))); } let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((Some(first), Some(scalar_id(&hv)?), false))); }
        c.eat_sym(end_sym).then_some(Ok(first))
    }
    fn parse_path_expr(&mut self, first: String, c: &mut Cursor<'_>) -> Option<Val> {
        let (mut base_owned, mut sub) = (self.resolve_ty(&first).to_string(), c.expect_ident()?);
        while c.eat_sym("::") {
            if self.is_async && matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); break; }
            base_owned.push_str("::"); base_owned.push_str(&sub); sub = c.expect_ident()?;
        }
        let (is_opt, is_res) = (base_owned == "Option" || base_owned.ends_with("::Option"), base_owned == "Result" || base_owned.ends_with("::Result"));
        if c.eat_sym("(") {
            if let Some(st) = self.file.resolve_scalar(&base_owned) {
                if sub == "from" { let arg = self.parse_expr(c)?; return c.eat_sym(")").then_some(Val::Scalar(scalar_id(&arg)?.0, Some(st))); }
                if matches!(sub.as_str(), "from_le_bytes" | "from_be_bytes") && matches!(st, ScalarTy::U16 | ScalarTy::U32) {
                    let arg = self.parse_expr(c)?; if !c.eat_sym(")") { return None; }
                    let Val::Buf(bb) = arg else { return None; }; let (nbytes, be, mut acc) = (st.bits() / 8, sub == "from_be_bytes", None);
                    if bb.len_node.is_some() || bb.len_const != nbytes || bb.elem_ty != ScalarTy::U8 { return None; }
                    for k in 0..nbytes {
                        let ki = self.prog.push(Op::Const(k as i64)); let ri = self.buf_index(bb, ki); let b = self.push_g(Op::Load { buf: bb.id, idx: ri });
                        let sh = if be { ((nbytes - 1 - k) * 8) as u8 } else { (k * 8) as u8 }; let term = if sh == 0 { b } else { self.push_g(Op::Shl(b, sh)) };
                        acc = Some(match acc { Some(a) => self.push_g(Op::BitOr(a, term)), None => term });
                    }
                    return Some(Val::Scalar(acc?, Some(st)));
                }
                return None;
            }
            if (is_opt && sub == "Some") || (is_res && sub == "Ok") { let v = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } return Some(Val::Opt { is_some: self.prog.push(Op::Const(1)), payload: Box::new(v) }); }
            if is_res && sub == "Err" { return self.parse_err_ctor(c); }
            return self.parse_call(&format!("{base_owned}::{sub}"), None, None, c);
        }
        if let Some(st) = self.file.resolve_scalar(&base_owned) { return Some(Val::Scalar(self.prog.push(Op::Const(st.assoc_const(&sub)?)), Some(st))); }
        if let Some(e) = self.file.enums.get(&base_owned) { return Some(Val::Scalar(self.prog.push(Op::Const(*e.variants.get(&sub)?)), Some(ScalarTy::Usize))); }
        if is_opt && sub == "None" { return Some(self.mk_none()); }
        let (cv, cty) = *self.file.consts.get(&format!("{base_owned}::{sub}"))?;
        Some(Val::Scalar(self.prog.push(Op::Const(cv)), cty))
    }
    fn parse_err_ctor(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        let (start, mut d) = (c.pos, 1usize); while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let body = c.toks.get(start..c.pos.saturating_sub(1)).unwrap_or(&[]);
        if body.iter().any(|t| matches!(t, Tok::Sym("/" | "%" | "[" | "<<" | ">>" | "+" | "-" | "*")) || matches!(t, Tok::Ident(w) if w == "unwrap" || w == "expect")) {
            let end = c.pos; c.pos = start; let _ = self.parse_expr(c)?; if c.pos + 1 != end { return None; } c.pos = end;
        }
        Some(self.mk_none())
    }
    fn parse_scalar_method(&mut self, base: usize, ty: Option<ScalarTy>, m: &str, c: &mut Cursor<'_>) -> Option<Val> {
        let mut args = Vec::new(); while !c.eat_sym(")") { args.push(self.parse_expr(c)?); let _ = c.eat_sym(","); }
        match m {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" => {
                let (r, rt) = scalar_id(args.first()?)?; let eff = ty.or(rt);
                let mut res = self.push_g(match m { "wrapping_add" => Op::WrapAdd(base, r), "wrapping_sub" => Op::WrapSub(base, r), _ => Op::WrapMul(base, r) });
                if let Some(t) = eff.filter(|t| t.is_narrow() && t.is_unsigned()) { let mk = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, mk)); }
                Some(Val::Scalar(res, eff))
            }
            "wrapping_shl" | "wrapping_shr" => {
                let ((r, _), shl, mask_v) = (scalar_id(args.first()?)?, m == "wrapping_shl", (ty.map_or(64, ScalarTy::bits) - 1) as i64);
                let mut res = if let Some(v) = self.const_of(r) { self.push_g(if shl { Op::Shl(base, (v & mask_v) as u8) } else { Op::Shr(base, (v & mask_v) as u8) }) }
                    else { let mk = self.prog.push(Op::Const(mask_v)); let s = self.push_g(Op::BitAnd(r, mk)); self.push_g(if shl { Op::ShlVar(base, s) } else { Op::ShrVar(base, s) }) };
                if shl { if let Some(t) = ty.filter(|t| t.is_narrow() && t.is_unsigned()) { let mk = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, mk)); } }
                Some(Val::Scalar(res, ty))
            }
            "min" | "max" => {
                let (r, rt) = scalar_id(args.first()?)?; let cmp = self.push_g(Op::Cmp(if m == "min" { CmpKind::Lt } else { CmpKind::Gt }, base, r));
                Some(Val::Scalar(self.push_g(Op::Select { cond: cmp, t_val: base, f_val: r }), ty.or(rt)))
            }
            "saturating_sub" | "saturating_add" => {
                let ((r, rt), is_add) = (scalar_id(args.first()?)?, m == "saturating_add"); let eff = ty.or(rt)?;
                if eff.is_narrow() {
                    let ((lo, hi), raw) = (eff.bounds(), self.push_g(if is_add { Op::Add(base, r) } else { Op::Sub(base, r) }));
                    let (lok, hik) = (self.prog.push(Op::Const(lo)), self.prog.push(Op::Const(hi)));
                    let c1 = self.push_g(Op::Cmp(CmpKind::Lt, raw, lok)); let s1 = self.push_g(Op::Select { cond: c1, t_val: lok, f_val: raw });
                    let c2 = self.push_g(Op::Cmp(CmpKind::Gt, s1, hik)); return Some(Val::Scalar(self.push_g(Op::Select { cond: c2, t_val: hik, f_val: s1 }), Some(eff)));
                }
                if !eff.is_unsigned() { return None; }
                let old_g = self.cur_guard;
                if is_add {
                    let mx = self.prog.push(Op::Const(i64::MAX)); let room = self.push_g(Op::Sub(mx, base));
                    let ok = self.push_g(Op::Cmp(CmpKind::Le, r, room)); self.cur_guard = self.and_guard(old_g, (ok, true));
                    let raw = self.push_g(Op::WrapAdd(base, r)); let s = self.push_g(Op::BitAnd(raw, mx)); self.cur_guard = old_g; Some(Val::Scalar(self.push_g(Op::Select { cond: ok, t_val: s, f_val: mx }), Some(eff)))
                } else {
                    let ge = self.push_g(Op::Cmp(CmpKind::Ge, base, r)); self.cur_guard = self.and_guard(old_g, (ge, true));
                    let d = self.push_g(Op::Sub(base, r)); self.cur_guard = old_g; let z = self.prog.push(Op::Const(0));
                    Some(Val::Scalar(self.push_g(Op::Select { cond: ge, t_val: d, f_val: z }), Some(eff)))
                }
            }
            "checked_add" | "checked_sub" | "checked_mul" | "checked_div" | "checked_rem" => {
                let (r, rt) = scalar_id(args.first()?)?; let eff = ty.or(rt)?; let ((lo, hi), old_g) = (eff.bounds(), self.cur_guard);
                let (ok, val) = match m {
                    "checked_add" if eff.is_narrow() => { let s = self.push_g(Op::Add(base, r)); (self.in_bounds(s, lo, hi, true), s) }
                    "checked_add" if eff.is_unsigned() => { let mx = self.prog.push(Op::Const(i64::MAX)); let room = self.push_g(Op::Sub(mx, base)); let ok = self.push_g(Op::Cmp(CmpKind::Le, r, room)); self.cur_guard = self.and_guard(old_g, (ok, true)); let raw = self.push_g(Op::WrapAdd(base, r)); let s = self.push_g(Op::BitAnd(raw, mx)); self.cur_guard = old_g; (ok, s) }
                    "checked_sub" if eff.is_unsigned() => { let ok = self.push_g(Op::Cmp(CmpKind::Ge, base, r)); self.cur_guard = self.and_guard(old_g, (ok, true)); let d = self.push_g(Op::Sub(base, r)); self.cur_guard = old_g; (ok, d) }
                    "checked_sub" if eff.is_narrow() => { let d = self.push_g(Op::Sub(base, r)); (self.in_bounds(d, lo, hi, true), d) }
                    "checked_mul" if matches!(eff, ScalarTy::U8 | ScalarTy::U16 | ScalarTy::I8 | ScalarTy::I16 | ScalarTy::I32) => { let p = self.push_g(Op::Mul(base, r)); (self.in_bounds(p, lo, hi, true), p) }
                    "checked_div" | "checked_rem" if eff.is_unsigned() => { let z = self.prog.push(Op::Const(0)); let ok = self.push_g(Op::Cmp(CmpKind::Ne, r, z)); self.cur_guard = self.and_guard(old_g, (ok, true)); let q = self.push_g(if m == "checked_div" { Op::Div(base, r) } else { Op::Rem(base, r) }); self.cur_guard = old_g; (ok, q) }
                    _ => return None,
                };
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(val, Some(eff))) })
            }
            "abs" | "unsigned_abs" if args.is_empty() => {
                let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let lt = self.push_g(Op::Cmp(CmpKind::Lt, base, z));
                self.cur_guard = self.and_guard(old_g, (lt, true)); let neg = self.push_g(Op::Sub(z, base));
                if m == "abs" { if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(neg, t); } }
                self.cur_guard = old_g;
                let rty = if m == "unsigned_abs" { match ty { Some(ScalarTy::I8) => Some(ScalarTy::U8), Some(ScalarTy::I16) => Some(ScalarTy::U16), Some(ScalarTy::I32) => Some(ScalarTy::U32), Some(ScalarTy::I64) => Some(ScalarTy::U64), _ => Some(ScalarTy::Usize) } } else { ty };
                Some(Val::Scalar(self.push_g(Op::Select { cond: lt, t_val: neg, f_val: base }), rty))
            }
            "is_multiple_of" => {
                let ((r, _), z, old_g) = (scalar_id(args.first()?)?, self.prog.push(Op::Const(0)), self.cur_guard);
                let nz = self.push_g(Op::Cmp(CmpKind::Ne, r, z)); self.cur_guard = self.and_guard(old_g, (nz, true));
                let rem = self.push_g(Op::Rem(base, r)); let eq0 = self.push_g(Op::Cmp(CmpKind::Eq, rem, z)); self.cur_guard = old_g; let base0 = self.push_g(Op::Cmp(CmpKind::Eq, base, z));
                Some(Val::Scalar(self.push_g(Op::Select { cond: nz, t_val: eq0, f_val: base0 }), Some(ScalarTy::Bool)))
            }
            "div_ceil" if ty.is_some_and(ScalarTy::is_unsigned) => {
                let ((r, _), z, one, mx, old_g) = (scalar_id(args.first()?)?, self.prog.push(Op::Const(0)), self.prog.push(Op::Const(1)), self.prog.push(Op::Const(i64::MAX)), self.cur_guard);
                let (q, rem) = (self.push_g(Op::Div(base, r)), self.push_g(Op::Rem(base, r)));
                let has_rem = self.push_g(Op::Cmp(CmpKind::Ne, rem, z)); self.cur_guard = self.and_guard(old_g, (has_rem, true));
                let raw_qp1 = self.push_g(Op::WrapAdd(q, one)); let qp1 = self.push_g(Op::BitAnd(raw_qp1, mx)); self.cur_guard = old_g;
                let res = self.push_g(Op::Select { cond: has_rem, t_val: qp1, f_val: q });
                if let Some(t) = ty.filter(|t| t.is_narrow()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty))
            }
            "rem_euclid" => {
                let (r, _) = scalar_id(args.first()?)?; let rem = self.push_g(Op::Rem(base, r)); if ty.is_some_and(ScalarTy::is_unsigned) { return Some(Val::Scalar(rem, ty)); }
                let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let (neg_r, r_neg) = (self.push_g(Op::Cmp(CmpKind::Lt, rem, z)), self.push_g(Op::Cmp(CmpKind::Lt, r, z)));
                let g_neg = self.and_guard(old_g, (neg_r, true)); self.cur_guard = self.and_guard(g_neg, (r_neg, true)); let sub_v = self.push_g(Op::Sub(rem, r));
                self.cur_guard = self.and_guard(g_neg, (r_neg, false)); let add_v = self.push_g(Op::Add(rem, r));
                self.cur_guard = g_neg; let adj = self.push_g(Op::Select { cond: r_neg, t_val: sub_v, f_val: add_v });
                self.cur_guard = old_g; Some(Val::Scalar(self.push_g(Op::Select { cond: neg_r, t_val: adj, f_val: rem }), ty))
            }
            "is_ascii_digit" | "is_ascii_alphabetic" | "is_ascii_alphanumeric" | "is_ascii_whitespace" if args.is_empty() && ty == Some(ScalarTy::U8) => {
                let rs: &[(i64, i64)] = match m { "is_ascii_digit" => &[(48, 57)], "is_ascii_alphabetic" => &[(65, 90), (97, 122)], "is_ascii_alphanumeric" => &[(48, 57), (65, 90), (97, 122)], _ => &[(9, 10), (12, 13), (32, 32)] };
                let (one, mut acc) = (self.prog.push(Op::Const(1)), None);
                for &(lo, hi) in rs { let in_r = self.in_bounds(base, lo, hi, true); acc = Some(match acc { Some(a) => self.push_g(Op::Select { cond: a, t_val: one, f_val: in_r }), None => in_r }); }
                Some(Val::Scalar(acc?, Some(ScalarTy::Bool)))
            }
            _ if ty == Some(ScalarTy::Usize) => {
                let st = self.self_ty.as_deref().filter(|s| self.file.enums.contains_key(*s))?;
                let mut all = vec![Val::Scalar(base, ty)]; all.extend(args); self.inline_call(&format!("{st}::{m}"), &all, &[])
            }
            _ => None,
        }
    }
    fn parse_buf_method(&mut self, bb: BufBind, m: &str, c: &mut Cursor<'_>) -> Option<Val> {
        match m {
            "len" => c.eat_sym(")").then(|| Val::Scalar(self.buf_len_node(bb), Some(ScalarTy::Usize))),
            "is_empty" => { if !c.eat_sym(")") { return None; } let (ln, z) = (self.buf_len_node(bb), self.prog.push(Op::Const(0))); Some(Val::Scalar(self.push_g(Op::Cmp(CmpKind::Eq, ln, z)), Some(ScalarTy::Bool))) }
            "first" | "last" => {
                if !c.eat_sym(")") { return None; }
                let (ln, z, old_g) = (self.buf_len_node(bb), self.prog.push(Op::Const(0)), self.cur_guard);
                let ok = self.push_g(Op::Cmp(CmpKind::Gt, ln, z)); self.cur_guard = self.and_guard(old_g, (ok, true));
                let idx = if m == "first" { z } else { let one = self.prog.push(Op::Const(1)); self.push_g(Op::Sub(ln, one)) };
                let ri = self.buf_index(bb, idx); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri }); self.cur_guard = old_g;
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(ld, Some(bb.elem_ty))) })
            }
            "get" | "get_mut" => {
                let mut_req = m == "get_mut"; if mut_req && !bb.mutable { return None; }
                match self.parse_range_or_idx(c, ")")? {
                    Ok((idx, ity)) => {
                        let ln = self.buf_len_node(bb); let mut ok = self.push_g(Op::Cmp(CmpKind::Lt, idx, ln));
                        if !ity.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { let z = self.prog.push(Op::Const(0)); let ge0 = self.push_g(Op::Cmp(CmpKind::Ge, idx, z)); ok = self.push_g(Op::Select { cond: ge0, t_val: ok, f_val: z }); }
                        let old_g = self.cur_guard; self.cur_guard = self.and_guard(old_g, (ok, true));
                        let ri = self.buf_index(bb, idx); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri }); self.cur_guard = old_g;
                        Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(ld, Some(bb.elem_ty))) })
                    }
                    Err((lo, hi, inc)) => { let (ok, sub) = self.make_subslice(bb, lo, hi, inc, true, mut_req)?; Some(Val::Opt { is_some: ok?, payload: Box::new(Val::Buf(sub)) }) }
                }
            }
            "split_at" | "split_at_mut" => {
                let mut_req = m == "split_at_mut"; let mv = self.parse_expr(c)?; let mid = scalar_id(&mv)?; if !c.eat_sym(")") { return None; }
                let ((_, left), (_, right)) = (self.make_subslice(bb, None, Some(mid), false, false, mut_req)?, self.make_subslice(bb, Some(mid), None, false, false, mut_req)?);
                Some(Val::Tuple(vec![Val::Buf(left), Val::Buf(right)]))
            }
            "split_first" => {
                if !c.eat_sym(")") { return None; }
                let (ln, z, one, old_g) = (self.buf_len_node(bb), self.prog.push(Op::Const(0)), self.prog.push(Op::Const(1)), self.cur_guard);
                let ok = self.push_g(Op::Cmp(CmpKind::Gt, ln, z)); self.cur_guard = self.and_guard(old_g, (ok, true));
                let ri = self.buf_index(bb, z); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri });
                let (_, rest) = self.make_subslice(bb, Some((one, Some(ScalarTy::Usize))), None, false, false, false)?; self.cur_guard = old_g;
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Tuple(vec![Val::Scalar(ld, Some(bb.elem_ty)), Val::Buf(rest)])) })
            }
            "as_slice" => c.eat_sym(")").then_some(Val::Buf(bb)), _ => None,
        }
    }
    fn parse_opt_method(&mut self, is_some: usize, payload: Val, m: &str, c: &mut Cursor<'_>) -> Option<Val> {
        match m {
            "is_some" | "is_ok" => c.eat_sym(")").then_some(Val::Scalar(is_some, Some(ScalarTy::Bool))),
            "is_none" | "is_err" => { if !c.eat_sym(")") { return None; } let z = self.prog.push(Op::Const(0)); Some(Val::Scalar(self.push_g(Op::Cmp(CmpKind::Eq, is_some, z)), Some(ScalarTy::Bool))) }
            "copied" | "cloned" => c.eat_sym(")").then_some(Val::Opt { is_some, payload: Box::new(payload) }),
            "unwrap" | "expect" => { let mut d = 1usize; while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } } self.push_g(Op::PanicIfZero(is_some, 1)); Some(payload) }
            "unwrap_or" => { let def = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } self.merge_val(is_some, payload, def, self.cur_guard) }
            "unwrap_or_default" => { if !c.eat_sym(")") { return None; } let def = self.zero_like(&payload); self.merge_val(is_some, payload, def, self.cur_guard) }
            "ok_or" => { let _ = self.parse_err_ctor(c)?; Some(Val::Opt { is_some, payload: Box::new(payload) }) } _ => None,
        }
    }
    fn is_await_next(c: &Cursor<'_>) -> bool { matches!(c.peek(), Some(Tok::Sym("."))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if w == "await") }
    fn peek_mut_target(&self, c: &Cursor<'_>) -> MutTarget {
        if matches!(c.peek(), Some(Tok::Sym("&"))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if w == "mut") {
            let off = 2 + usize::from(matches!(c.peek_at(2), Some(Tok::Sym("*"))));
            if let Some(Tok::Ident(nm)) = c.peek_at(off) {
                if matches!(c.peek_at(off + 1), Some(Tok::Sym("," | ")"))) { return Some((nm.clone(), None)); }
                if matches!(c.peek_at(off + 1), Some(Tok::Sym("."))) { if let (Some(Tok::Ident(f)), Some(Tok::Sym("," | ")"))) = (c.peek_at(off + 2), c.peek_at(off + 3)) { return Some((nm.clone(), Some(f.clone()))); } }
            }
        } else if let Some(Tok::Ident(nm)) = c.peek() { if self.mut_refs.contains(nm) && matches!(c.peek_at(1), Some(Tok::Sym("," | ")"))) { return Some((nm.clone(), None)); } }
        None
    }
    fn write_mut_target(&mut self, vname: &str, fld: Option<&str>, new_val: Val) {
        if let Some(f) = fld {
            if let Some(Val::Struct(sn, mut fs)) = self.vars.get(vname).cloned() { if let Some((_, fv)) = fs.iter_mut().find(|(k, _)| k == f) { *fv = new_val; } self.vars.insert(vname.to_string(), Val::Struct(sn, fs)); }
        } else { self.vars.insert(vname.to_string(), new_val); }
    }
    fn havoc_buf(&mut self, bb: BufBind) {
        let hv = self.prog.add_named_param("__havoc_buf", bb.elem_ty.domain());
        if bb.len_node.is_none() && bb.len_const <= 64 {
            for k in 0..bb.len_const { let ki = self.prog.push(Op::Const(k as i64)); let ri = self.buf_index(bb, ki); let st = self.push_g(Op::Store { buf: bb.id, idx: ri, val: hv }); self.stores.push(st); }
            return;
        }
        if let (Some(ln), Some(rlen)) = (bb.len_node, self.prog.bufs.get(usize::from(bb.id)).map(|b| b.len).filter(|&l| l <= 64)) {
            let lo = bb.base_node.unwrap_or_else(|| self.prog.push(Op::Const(bb.base_const as i64))); let hi = self.push_g(Op::Add(lo, ln));
            for k in 0..rlen { let ki = self.prog.push(Op::Const(k as i64)); self.store_guarded(bb.id, ki, hv, lo, hi); }
            return;
        }
        let mut seen = Vec::new();
        for &op in &self.prog.nodes { if let Op::Store { buf, idx, .. } = op { if buf == bb.id && !seen.contains(&idx) { seen.push(idx); if seen.len() >= 8 { break; } } } }
        let (rln, z) = (bb.root_len.or(bb.len_node).unwrap_or_else(|| self.prog.push(Op::Const(bb.len_const as i64))), self.prog.push(Op::Const(0)));
        for idx in seen { self.store_guarded(bb.id, idx, hv, z, rln); }
    }
    fn havoc_val(&mut self, v: &Val) -> Val {
        match v {
            Val::Scalar(_, ty) => Val::Scalar(self.prog.add_named_param("__havoc", ty.map_or_else(Domain::top, ScalarTy::domain)), *ty),
            Val::Struct(sn, fs) => Val::Struct(sn.clone(), fs.iter().map(|(k, fv)| (k.clone(), self.havoc_val(fv))).collect()),
            Val::Opt { payload, .. } => Val::Opt { is_some: self.prog.add_named_param("__havoc_ok", Domain::range(0, 1)), payload: Box::new(self.havoc_val(payload)) },
            Val::Tuple(xs) => Val::Tuple(xs.iter().map(|x| self.havoc_val(x)).collect()),
            Val::Buf(bb) => { if bb.mutable { self.havoc_buf(*bb); } Val::Buf(*bb) } Val::Opaque => Val::Opaque,
        }
    }
    fn havoc_mut_args(&mut self, targets: &[MutTarget], args: &[Val]) {
        let mut done_bufs = BTreeSet::new();
        for (tgt, arg) in targets.iter().zip(args) {
            if let Some((vname, fld)) = tgt {
                if let Some(cur) = self.vars.get(vname).cloned() {
                    if let Some(f) = fld {
                        if let Val::Struct(sn, mut fs) = cur { if let Some((_, fv)) = fs.iter_mut().find(|(k, _)| k == f) { *fv = self.havoc_val(fv); } self.vars.insert(vname.clone(), Val::Struct(sn, fs)); }
                    } else { if let Val::Buf(bb) = cur { done_bufs.insert(bb.id); } let hv = self.havoc_val(&cur); self.vars.insert(vname.clone(), hv); }
                    continue;
                }
            }
            if let Val::Buf(bb) = arg { if bb.mutable && done_bufs.insert(bb.id) { self.havoc_buf(*bb); } }
        }
    }
    fn parse_postfix(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        let mut base_var: Option<String> = None;
        let mut base = match c.peek()? {
            &Tok::Int(v, ty) => { c.pos += 1; Val::Scalar(self.prog.push(Op::Const(v)), ty) }
            Tok::Sym("\"") if self.is_async => { c.pos += 1; Val::Opaque }
            Tok::Sym("(") => {
                c.pos += 1;
                if c.eat_sym(")") { Val::Tuple(Vec::new()) } else {
                    let first = self.parse_expr(c)?;
                    if c.eat_sym(",") { let mut xs = vec![first]; while !c.eat_sym(")") { xs.push(self.parse_expr(c)?); let _ = c.eat_sym(","); } Val::Tuple(xs) }
                    else { if !c.eat_sym(")") { return None; } first }
                }
            }
            Tok::Sym("[") => { c.pos += 1; self.parse_array_lit(c, None)? }
            Tok::Sym("{") => self.parse_block(c)?.1?,
            Tok::Ident(kw) if kw == "true" || kw == "false" => { let v = i64::from(kw == "true"); c.pos += 1; Val::Scalar(self.prog.push(Op::Const(v)), Some(ScalarTy::Bool)) }
            Tok::Ident(kw) if kw == "None" => { c.pos += 1; self.mk_none() }
            Tok::Ident(kw) if kw == "Some" || kw == "Ok" => { c.pos += 1; if !c.eat_sym("(") { return None; } let v = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } Val::Opt { is_some: self.prog.push(Op::Const(1)), payload: Box::new(v) } }
            Tok::Ident(kw) if kw == "Err" => { c.pos += 1; if !c.eat_sym("(") { return None; } self.parse_err_ctor(c)? }
            Tok::Ident(kw) if kw == "if" => { c.pos += 1; self.parse_if(c)?.0? }
            Tok::Ident(kw) if kw == "match" => { c.pos += 1; self.parse_match(c)?.0? }
            Tok::Ident(kw) if kw == "matches" && matches!(c.peek_at(1), Some(Tok::Sym("!"))) => {
                c.pos += 2; if !c.eat_sym("(") { return None; } let scrut = self.parse_expr(c)?; if !c.eat_sym(",") { return None; }
                let (pc, _) = self.parse_match_pat(&scrut, c)?; let _ = c.eat_sym(","); if !c.eat_sym(")") { return None; }
                Val::Scalar(pc.unwrap_or_else(|| self.prog.push(Op::Const(1))), Some(ScalarTy::Bool))
            }
            Tok::Ident(kw) if matches!(kw.as_str(), "panic" | "unreachable" | "todo" | "unimplemented") && matches!(c.peek_at(1), Some(Tok::Sym("!"))) => {
                c.pos += 2;
                match c.peek() { Some(Tok::Sym("(")) => c.skip_balanced("(", ")"), Some(Tok::Sym("[")) => c.skip_balanced("[", "]"), Some(Tok::Sym("{")) => c.skip_balanced("{", "}"), _ => return None }
                let z = self.prog.push(Op::Const(0)); self.push_g(Op::PanicIfZero(z, 1)); Val::Scalar(z, None)
            }
            Tok::Ident(nm) => {
                let nm = nm.clone(); c.pos += 1;
                if c.eat_sym("::") { self.parse_path_expr(nm, c)? }
                else if !self.no_struct_lit && matches!(c.peek(), Some(Tok::Sym("{"))) && self.file.structs.contains_key(self.resolve_ty(&nm)) { c.pos += 1; let rn = self.resolve_ty(&nm).to_string(); self.parse_struct_lit(&rn, c)? }
                else if !self.no_struct_lit && self.is_async && matches!(c.peek(), Some(Tok::Sym("{"))) { let p0 = c.pos; c.skip_balanced("{", "}"); if Self::is_await_next(c) { Val::Opaque } else { c.pos = p0; return None; } }
                else if c.eat_sym("(") { self.parse_call(&nm, None, None, c)? }
                else if let Some(v) = self.vars.get(&nm) { base_var = Some(nm); v.clone() }
                else if let Some(&(cv, cty)) = self.file.consts.get(&nm) { Val::Scalar(self.prog.push(Op::Const(cv)), cty) } else { return None; }
            }
            _ => return None,
        };
        loop {
            if c.eat_sym("[") {
                base_var = None; let Val::Buf(bb) = base else { return None; };
                base = match self.parse_range_or_idx(c, "]")? {
                    Ok((idx, _)) => { let ri = self.buf_index(bb, idx); Val::Scalar(self.push_g(Op::Load { buf: bb.id, idx: ri }), Some(bb.elem_ty)) }
                    Err((lo, hi, inc)) => Val::Buf(self.make_subslice(bb, lo, hi, inc, false, bb.mutable)?.1),
                };
            } else if c.eat_sym(".") {
                if let Some(&Tok::Int(ti, None)) = c.peek() { c.pos += 1; base_var = None; let Val::Tuple(ref xs) = base else { return None; }; base = xs.get(usize::try_from(ti).ok()?)?.clone(); continue; }
                if c.eat_ident("await") {
                    if !self.is_async { return None; } base_var = None;
                    if matches!(base, Val::Opaque) {
                        let opt_next = matches!(c.peek(), Some(Tok::Sym("?"))) || (matches!(c.peek(), Some(Tok::Sym("."))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if matches!(w.as_str(), "unwrap" | "expect" | "unwrap_or" | "unwrap_or_default" | "is_ok" | "is_err" | "is_some" | "is_none" | "ok_or" | "copied" | "cloned")));
                        base = if opt_next { Val::Opt { is_some: self.prog.add_named_param("__await_ok", Domain::range(0, 1)), payload: Box::new(Val::Scalar(self.prog.add_named_param("__await_val", Domain::range(0, MAX_SYM_SLICE_LEN as i64)), None)) } }
                            else { Val::Scalar(self.prog.add_named_param("__await_val", Domain::top()), None) };
                    }
                    continue;
                }
                let m = c.expect_ident()?;
                if c.eat_sym("(") {
                    let (arg_pos, recv_t, saved) = (c.pos, base_var.take().map(|n| (n, None)), self.is_async.then(|| (self.prog.clone(), self.stores.len(), self.next_region, self.inlined_fns.clone())));
                    let known = match base.clone() {
                        Val::Scalar(id, ty) => self.parse_scalar_method(id, ty, &m, c), Val::Buf(bb) => self.parse_buf_method(bb, &m, c),
                        Val::Opt { is_some, payload } => self.parse_opt_method(is_some, *payload, &m, c),
                        Val::Struct(ref sn, _) => self.parse_call(&format!("{sn}::{m}"), Some(base.clone()), recv_t.clone(), c),
                        Val::Opaque => self.parse_call(&m, Some(Val::Opaque), None, c), Val::Tuple(_) => None,
                    };
                    base = match known {
                        Some(v) => v,
                        None if self.is_async && !matches!(base, Val::Opaque | Val::Struct(..)) => {
                            if let Some((sp, sl, nr, inf)) = saved { (self.prog, self.next_region, *self.inlined_fns) = (sp, nr, inf); self.stores.truncate(sl); }
                            c.pos = arg_pos; self.parse_call(&m, Some(base), recv_t, c)?
                        }
                        None => return None,
                    };
                } else { base_var = None; base = match base { Val::Struct(_, ref fs) => fs.iter().find(|(k, _)| k == &m)?.1.clone(), Val::Opaque => Val::Opaque, _ => return None }; }
            } else if c.eat_sym("?") {
                base_var = None; if !self.returns_opt { return None; } let Val::Opt { is_some, payload } = base else { return None; }; let not_some = self.mk_bool(is_some, false);
                let gfail = match self.cur_guard { Some((g, p)) => { let (gb, z) = (self.mk_bool(g, p), self.prog.push(Op::Const(0))); self.prog.push(Op::Select { cond: gb, t_val: not_some, f_val: z }) } None => not_some };
                let none_v = self.mk_none(); self.early_rets.push((gfail, none_v)); self.cur_guard = self.and_guard(self.cur_guard, (is_some, true)); base = *payload;
            } else { break; }
        }
        Some(base)
    }
    fn parse_call(&mut self, name: &str, receiver: Option<Val>, recv_target: MutTarget, c: &mut Cursor<'_>) -> Option<Val> {
        let (recv_opaque, mut args, mut targets) = (matches!(receiver, Some(Val::Opaque)), Vec::new(), Vec::new()); if let Some(rv) = receiver { args.push(rv); targets.push(recv_target); }
        while !c.eat_sym(")") { targets.push(self.peek_mut_target(c)); args.push(self.parse_expr(c)?); let _ = c.eat_sym(","); }
        match name {
            "zero_alloc" => { let (Val::Buf(bb), Val::Scalar(ln, _)) = (args.first()?, args.get(1)?) else { return None; }; let n = self.push_g(Op::Alloc { buf: bb.id, len: usize::try_from(self.const_of(*ln)?).ok()? }); self.stores.push(n); Some(Val::Scalar(n, None)) }
            "zero_free" => { let Val::Buf(bb) = args.first()? else { return None; }; let n = self.push_g(Op::Free(bb.id)); self.stores.push(n); Some(Val::Scalar(n, None)) }
            "zero_check_gen" => { let (Val::Buf(bb), Val::Scalar(tok, _)) = (args.first()?, args.get(1)?) else { return None; }; let n = self.push_g(Op::CheckGen { buf: bb.id, expected: *tok }); self.stores.push(n); Some(Val::Scalar(n, None)) }
            "zero_uninit_write" => { let (Val::Buf(bb), Val::Scalar(idx, _), Val::Scalar(val, _)) = (args.first()?, args.get(1)?, args.get(2)?) else { return None; }; let ri = self.buf_index(*bb, *idx); let n = self.push_g(Op::Store { buf: bb.id, idx: ri, val: *val }); self.stores.push(n); Some(Val::Scalar(n, None)) }
            "zero_uninit_read" => { let (Val::Buf(bb), Val::Scalar(idx, _)) = (args.first()?, args.get(1)?) else { return None; }; let ri = self.buf_index(*bb, *idx); Some(Val::Scalar(self.push_g(Op::Load { buf: bb.id, idx: ri }), Some(bb.elem_ty))) }
            _ => {
                let saved = self.is_async.then(|| (self.prog.clone(), self.stores.len(), self.next_region, self.inlined_fns.clone()));
                if let Some(v) = self.inline_call(name, &args, &targets) { return Some(v); }
                if self.is_async && (recv_opaque || Self::is_await_next(c)) {
                    if let Some((sp, sl, nr, inf)) = saved { (self.prog, self.next_region, *self.inlined_fns) = (sp, nr, inf); self.stores.truncate(sl); }
                    self.havoc_mut_args(&targets, &args); return Some(Val::Opaque);
                }
                None
            }
        }
    }
    fn inline_call(&mut self, name: &str, args: &[Val], mut_targets: &[MutTarget]) -> Option<Val> {
        if self.depth >= 4 { return None; }
        let item = self.file.fns.iter().find(|f| f.name == name)?; if item.is_unsafe { return None; }
        let bufs: Vec<BufBind> = args.iter().filter_map(|a| if let Val::Buf(b) = a { Some(*b) } else { None }).collect();
        for (i, a) in bufs.iter().enumerate() {
            for b in bufs.get(i + 1..).unwrap_or(&[]) {
                if a.id == b.id && (a.mutable || b.mutable) && a.base_node.is_none() && b.base_node.is_none() && a.base_const < b.base_const + b.len_const && b.base_const < a.base_const + a.len_const {
                    if let Some(r) = self.prog.bufs.get(usize::from(a.id)).cloned() { self.prog.add_buf(format!("__alias_{name}"), b.len_const.max(1), true, r.region, r.offset + b.base_const, r.elem_domain); }
                }
            }
        }
        let mut cc = Cursor { toks: self.toks, pos: item.sig_pos }; let gpos = cc.pos; if !cc.eat_empty_generics() { if !item.is_async { return None; } cc.pos = gpos; cc.skip_angles(); }
        if !cc.eat_sym("(") { return None; }
        let (mut nv, mut ai, mut dm, mut mut_params, mut cmr) = (BTreeMap::new(), 0usize, FnMeta::default(), Vec::new(), BTreeSet::new());
        while !cc.eat_sym(")") {
            while let Some(Tok::Doc(l)) = cc.peek() { parse_doc_meta(l, &mut dm); cc.pos += 1; }
            while matches!(cc.peek(), Some(Tok::Sym("#"))) { let _ = cc.parse_attr(&mut dm); }
            let (is_ref_self, is_mut_self) = (cc.eat_sym("&"), cc.eat_ident("mut"));
            if cc.eat_ident("self") {
                if is_ref_self && is_mut_self { if !(self.is_async || item.is_async) { return None; } mut_params.push((ai, "self".to_string())); cmr.insert("self".to_string()); }
                nv.insert("self".to_string(), args.get(ai)?.clone()); ai += 1; let _ = cc.eat_sym(","); continue;
            }
            if is_ref_self { return None; }
            let pname = cc.expect_ident()?; if !cc.eat_sym(":") { return None; }
            if matches!(cc.peek(), Some(Tok::Sym("&"))) && matches!(cc.peek_at(1), Some(Tok::Ident(w)) if w == "mut") {
                cmr.insert(pname.clone()); if !matches!(cc.peek_at(2), Some(Tok::Sym("["))) { mut_params.push((ai, pname.clone())); }
            }
            cc.skip_until(",", ")", true); nv.insert(pname, args.get(ai)?.clone()); ai += 1; let _ = cc.eat_sym(",");
        }
        if ai != args.len() { return None; }
        let mut callee_ret_opt = false;
        if cc.eat_sym("->") {
            let (mut d, mut last_id) = (0usize, "");
            while let Some(t) = cc.peek() {
                match t {
                    Tok::Sym("{") if d == 0 => break, Tok::Ident(w) if d == 0 => { last_id = w.as_str(); cc.pos += 1; }
                    Tok::Sym("<") => { if d == 0 && (last_id == "Option" || last_id == "Result") { callee_ret_opt = true; } d += 1; cc.pos += 1; }
                    Tok::Sym("(" | "[") => { d += 1; cc.pos += 1; } Tok::Sym(")" | "]" | ">") => { d = d.saturating_sub(1); cc.pos += 1; }
                    Tok::Sym(">>") => { d = d.saturating_sub(2); cc.pos += 1; } _ => cc.pos += 1,
                }
            }
        } else if cc.eat_ident("where") { cc.skip_until("{", ";", false); }
        let (sv, se, sg, sst, sro, sa, smr) = (
            std::mem::replace(&mut self.vars, nv), std::mem::take(&mut self.early_rets), self.cur_guard,
            std::mem::replace(&mut self.self_ty, item.self_ty.clone()), std::mem::replace(&mut self.returns_opt, callee_ret_opt),
            std::mem::replace(&mut self.is_async, item.is_async), std::mem::replace(&mut self.mut_refs, cmr),
        ); self.depth += 1; let res = self.parse_block(&mut cc); self.depth -= 1;
        let (callee_vars, callee_early) = (std::mem::replace(&mut self.vars, sv), std::mem::replace(&mut self.early_rets, se));
        (self.cur_guard, self.self_ty, self.returns_opt, self.is_async, self.mut_refs) = (sg, sst, sro, sa, smr); let (rets, tail, _) = res?;
        if !mut_params.is_empty() {
            if !callee_early.is_empty() { return None; }
            for (arg_idx, pname) in mut_params {
                let Some(Some((vname, fld))) = mut_targets.get(arg_idx) else { return None; };
                if let Some(nv) = callee_vars.get(&pname) { self.write_mut_target(vname, fld.as_deref(), nv.clone()); }
            }
        }
        self.inlined_fns.insert(name.to_string()); let mut val = tail.or_else(|| rets.into_iter().next()).unwrap_or_else(|| Val::Scalar(self.prog.push(Op::Const(0)), None));
        for (cond, ev) in callee_early.into_iter().rev() { val = self.merge_val(cond, ev, val, self.cur_guard)?; }
        Some(val)
    }
    fn bind_pat(&mut self, c: &mut Cursor<'_>, val: Val) -> Option<()> {
        if c.eat_sym("(") {
            let Val::Tuple(xs) = val else { return None; }; let mut i = 0usize;
            while !c.eat_sym(")") { let _ = c.eat_ident("mut"); let v = xs.get(i)?.clone(); i += 1; self.bind_pat(c, v)?; let _ = c.eat_sym(","); }
            return (i == xs.len()).then_some(());
        }
        let _ = c.eat_ident("mut"); let name = c.expect_ident()?;
        if name != "_" { self.vars.insert(name, val); } Some(())
    }
    fn match_opt_inner(&mut self, is_some: usize, payload: &Val, c: &mut Cursor<'_>) -> Option<(usize, Option<(String, Val)>)> {
        let _ = c.eat_ident("mut"); let (inner_c, inner_b) = self.parse_match_pat(payload, c)?; if !c.eat_sym(")") { return None; }
        let cond = match inner_c { Some(ic) => { let z = self.prog.push(Op::Const(0)); self.push_g(Op::Select { cond: is_some, t_val: ic, f_val: z }) } None => is_some };
        Some((cond, inner_b))
    }
    fn parse_if(&mut self, c: &mut Cursor<'_>) -> Option<(Option<Val>, bool)> {
        let (old_g, vars0) = (self.cur_guard, self.vars.clone());
        let (cond, opt_bind, opt_var) = if c.eat_ident("let") {
            let tag = c.expect_ident()?; if !matches!(tag.as_str(), "Some" | "Ok") || !c.eat_sym("(") { return None; }
            let (pat_pos, mut d) = (c.pos, 1usize); while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } }
            if !c.eat_sym("=") { return None; }
            let Val::Opt { is_some, payload } = (match self.parse_expr_head(c)? {
                Val::Scalar(id, None) if self.is_async => Val::Opt { is_some: self.prog.add_named_param("__await_ok", Domain::range(0, 1)), payload: Box::new(Val::Scalar(id, None)) },
                v => v,
            }) else { return None; };
            if matches!(self.toks.get(pat_pos), Some(Tok::Sym("("))) { (is_some, Some((pat_pos, *payload)), None) }
            else { let mut pc = Cursor { toks: self.toks, pos: pat_pos }; let (mc, mb) = self.match_opt_inner(is_some, &payload, &mut pc)?; (mc, None, mb) }
        } else { let cv = self.parse_expr_head(c)?; (scalar_id(&cv)?.0, None, None) }; self.cur_guard = self.and_guard(old_g, (cond, true));
        if let Some((pat_pos, payload)) = opt_bind { let mut pc = Cursor { toks: self.toks, pos: pat_pos }; self.bind_pat(&mut pc, payload)?; }
        if let Some((k, v)) = opt_var { self.vars.insert(k, v); }
        let (_, t_tail, t_ret) = self.parse_block(c)?; let vars_t = std::mem::replace(&mut self.vars, vars0.clone());
        let (f_tail, f_ret, vars_f) = if c.eat_ident("else") {
            self.cur_guard = self.and_guard(old_g, (cond, false)); let res = if c.eat_ident("if") { self.parse_if(c)? } else { let (_, t, r) = self.parse_block(c)?; (t, r) };
            (res.0, res.1, std::mem::replace(&mut self.vars, vars0.clone()))
        } else { (None, false, vars0.clone()) }; self.cur_guard = old_g;
        for (k, v0) in vars0 {
            let (vt, vf) = (vars_t.get(&k).cloned().unwrap_or_else(|| v0.clone()), vars_f.get(&k).cloned().unwrap_or(v0));
            let mv = if t_ret && !f_ret { vf } else if f_ret && !t_ret { vt } else { self.merge_val(cond, vt, vf, old_g)? }; self.vars.insert(k, mv);
        }
        if t_ret ^ f_ret { self.cur_guard = self.and_guard(old_g, (cond, f_ret)); }
        let val = match (t_tail, f_tail, t_ret, f_ret) {
            (Some(tt), Some(ft), false, false) => Some(self.merge_val(cond, tt, ft, old_g)?),
            (Some(tt), _, false, true) => Some(tt), (_, Some(ft), true, false) => Some(ft), _ => None,
        };
        Some((val, t_ret && f_ret))
    }
    fn parse_match_pat(&mut self, scrut: &Val, c: &mut Cursor<'_>) -> Option<PatMatch> {
        let (mut cond, mut bind, mut unconditional): (Option<usize>, Option<(String, Val)>, bool) = (None, None, false);
        loop {
            let piece = match c.peek()? {
                Tok::Ident(s) if s == "_" => { c.pos += 1; unconditional = true; None }
                Tok::Ident(s) if s == "true" || s == "false" => { let (sv, _) = scalar_id(scrut)?; let k = self.prog.push(Op::Const(i64::from(s == "true"))); c.pos += 1; Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                Tok::Ident(s) if s == "None" => { let Val::Opt { is_some, .. } = scrut else { return None; }; c.pos += 1; let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                Tok::Ident(s) if s == "Some" || s == "Ok" => {
                    let Val::Opt { is_some, payload } = scrut else { return None; }; c.pos += 1; if !c.eat_sym("(") { return None; }
                    let (mc, mb) = self.match_opt_inner(*is_some, payload, c)?; if let Some(b) = mb { bind = Some(b); } Some(mc)
                }
                Tok::Ident(s) if s == "Err" => { let Val::Opt { is_some, .. } = scrut else { return None; }; c.pos += 1; c.skip_balanced("(", ")"); let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                Tok::Ident(s) => {
                    let nm = s.clone(); c.pos += 1;
                    if c.eat_sym("::") {
                        let (sub, base) = (c.expect_ident()?, self.resolve_ty(&nm).to_string());
                        if base == "Option" && sub == "None" { let Val::Opt { is_some, .. } = scrut else { return None; }; let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                        else {
                            let (sv, _) = scalar_id(scrut)?;
                            let cv = self.file.enums.get(&base).and_then(|e| e.variants.get(&sub).copied()).or_else(|| self.file.consts.get(&format!("{base}::{sub}")).map(|(v, _)| *v))?;
                            let k = self.prog.push(Op::Const(cv)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k)))
                        }
                    } else if let Some(&(cv, _)) = self.file.consts.get(&nm) { let (sv, _) = scalar_id(scrut)?; let k = self.prog.push(Op::Const(cv)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                    else { bind = Some((nm, scrut.clone())); unconditional = true; None }
                }
                Tok::Sym("-") | Tok::Int(_, _) => {
                    let (sv, _) = scalar_id(scrut)?; let lo = self.file.eval_const_atom(c, self.self_ty.as_deref())?.0;
                    if c.eat_sym("..=") || c.eat_sym("..") {
                        let inc = matches!(c.toks.get(c.pos.saturating_sub(1)), Some(Tok::Sym("..=")));
                        Some(self.in_bounds(sv, lo, self.file.eval_const_atom(c, self.self_ty.as_deref())?.0, inc))
                    } else { let k = self.prog.push(Op::Const(lo)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                }
                _ => return None,
            };
            cond = if unconditional { None } else { match (cond, piece) { (None, p) => p, (c0, None) => c0, (Some(a), Some(b)) => { let one = self.prog.push(Op::Const(1)); Some(self.push_g(Op::Select { cond: a, t_val: one, f_val: b })) } } };
            if !c.eat_sym("|") { break; }
        }
        if c.eat_ident("if") {
            let (gc, _) = scalar_id(&self.parse_expr_head(c)?)?;
            cond = Some(match cond { Some(a) => { let z = self.prog.push(Op::Const(0)); self.push_g(Op::Select { cond: a, t_val: gc, f_val: z }) } None => gc });
        }
        Some((cond, bind))
    }
    fn parse_match(&mut self, c: &mut Cursor<'_>) -> Option<(Option<Val>, bool)> {
        let mut scrut = self.parse_expr_head(c)?; if !c.eat_sym("{") { return None; }
        if let Val::Scalar(id, None) = scrut { if self.is_async && matches!(c.peek(), Some(Tok::Ident(w)) if matches!(w.as_str(), "Some" | "Ok" | "None" | "Err")) { scrut = Val::Opt { is_some: self.prog.add_named_param("__await_ok", Domain::range(0, 1)), payload: Box::new(Val::Scalar(id, None)) }; } }
        let (old_g, mut rem_g, vars0) = (self.cur_guard, self.cur_guard, self.vars.clone());
        let (mut unmatched, mut acc_vars, mut acc_val): (Option<usize>, Option<BTreeMap<String, Val>>, Option<Val>) = (None, None, None);
        while !c.eat_sym("}") {
            self.cur_guard = rem_g; let (pat_c, bind) = self.parse_match_pat(&scrut, c)?; if !c.eat_sym("=>") { return None; }
            self.cur_guard = match pat_c { Some(pc) => self.and_guard(rem_g, (pc, true)), None => rem_g }; self.vars = vars0.clone(); if let Some((k, v)) = bind { self.vars.insert(k, v); }
            let (val, arm_ret) = if matches!(c.peek(), Some(Tok::Sym("{"))) { let (_, t, r) = self.parse_block(c)?; (t, r) }
                else if c.eat_ident("return") { if !matches!(c.peek(), Some(Tok::Sym("," | "}"))) { let rv = self.parse_expr(c)?; self.record_return(rv); } (None, true) }
                else { (Some(self.parse_expr(c)?), false) };
            let arm_vars = std::mem::replace(&mut self.vars, vars0.clone()); let _ = c.eat_sym(",");
            if !arm_ret {
                if let Some(mut prev_vars) = acc_vars.take() {
                    let take = match (unmatched, pat_c) {
                        (Some(u), Some(pc)) => { let z = self.prog.push(Op::Const(0)); self.prog.push_guarded(Op::Select { cond: u, t_val: pc, f_val: z }, old_g) }
                        (Some(u), None) => u, (None, Some(pc)) => pc, (None, None) => self.prog.push(Op::Const(0)),
                    };
                    for (k, v0) in &vars0 { let mv = self.merge_val(take, arm_vars.get(k).cloned().unwrap_or_else(|| v0.clone()), prev_vars.remove(k).unwrap_or_else(|| v0.clone()), old_g)?; prev_vars.insert(k.clone(), mv); }
                    acc_vars = Some(prev_vars); acc_val = match (val, acc_val) { (Some(v), Some(a)) => Some(self.merge_val(take, v, a, old_g)?), (v, a) => a.or(v) };
                } else { acc_vars = Some(arm_vars); acc_val = val; }
            }
            if let Some(pc) = pat_c {
                rem_g = self.and_guard(rem_g, (pc, false)); let npc = self.mk_bool(pc, false);
                unmatched = Some(match unmatched { None => npc, Some(u) => { let z = self.prog.push(Op::Const(0)); self.prog.push_guarded(Op::Select { cond: u, t_val: npc, f_val: z }, old_g) } });
            } else { let z = self.prog.push(Op::Const(0)); rem_g = self.and_guard(rem_g, (z, true)); unmatched = Some(z); }
        }
        self.cur_guard = old_g; let Some(final_vars) = acc_vars else { return Some((None, true)); };
        for (k, v0) in vars0 { self.vars.insert(k.clone(), final_vars.get(&k).cloned().unwrap_or(v0)); }
        Some((acc_val, false))
    }
    fn record_return(&mut self, val: Val) { if let Some((g, p)) = self.cur_guard { let gb = self.mk_bool(g, p); self.early_rets.push((gb, val)); } }
    fn parse_assert(&mut self, kind: &str, c: &mut Cursor<'_>) -> Option<()> {
        if !c.eat_sym("!") || !c.eat_sym("(") { return None; }
        let cond = match kind {
            "assert_eq" | "debug_assert_eq" | "assert_ne" | "debug_assert_ne" => {
                let av = self.parse_expr(c)?; if !c.eat_sym(",") { return None; } let bv = self.parse_expr(c)?;
                self.push_g(Op::Cmp(if kind.ends_with("eq") { CmpKind::Eq } else { CmpKind::Ne }, scalar_id(&av)?.0, scalar_id(&bv)?.0))
            }
            _ => scalar_id(&self.parse_expr(c)?)?.0,
        }; let mut d = 1usize; while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let _ = c.eat_sym(";"); self.push_g(Op::PanicIfZero(cond, 3)); self.cur_guard = self.and_guard(self.cur_guard, (cond, true)); Some(())
    }
    fn looks_like_store(&self, c: &Cursor<'_>) -> bool {
        let mut k = c.pos + 1; if !matches!(c.toks.get(k), Some(Tok::Sym("["))) { return false; }
        let mut d = 1usize; k += 1; while k < c.toks.len() && d > 0 { match c.toks.get(k) { Some(Tok::Sym("[")) => d += 1, Some(Tok::Sym("]")) => d -= 1, _ => {} } k += 1; }
        matches!(c.toks.get(k), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=")))
    }
    fn looks_like_assign(&self, c: &Cursor<'_>) -> bool {
        let off = usize::from(matches!(c.peek(), Some(Tok::Sym("*"))));
        matches!(c.peek_at(off), Some(Tok::Ident(nm)) if self.vars.contains_key(nm))
            && matches!(c.peek_at(off + 1), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=")))
    }
    fn parse_let_type_hint(&self, c: &mut Cursor<'_>) -> Option<Option<ScalarTy>> {
        if !c.eat_sym(":") { return Some(None); }
        let in_br = c.eat_sym("["); let hint = if let Some(Tok::Ident(s)) = c.peek() { self.file.resolve_scalar(s) } else { None };
        if in_br { c.skip_until("]", "]", true); let _ = c.eat_sym("]"); } else { c.skip_until("=", ";", true); }
        Some(hint)
    }
    fn parse_for_loop(&mut self, c: &mut Cursor<'_>) -> Option<()> {
        let _ = c.eat_ident("mut"); let iv = c.expect_ident()?; if !c.eat_ident("in") { return None; }
        let rev_wrap = c.eat_sym("("); let lo_v = self.parse_expr_head(c)?; let lo = self.const_of(scalar_id(&lo_v)?.0)?;
        let inc = if c.eat_sym("..=") { true } else if c.eat_sym("..") { false } else { return None };
        let hi_v = self.parse_expr_head(c)?; let end = self.const_of(scalar_id(&hi_v)?.0)?.checked_add(i64::from(inc))?;
        let rev = rev_wrap && { if !c.eat_sym(")") { return None; } c.eat_sym(".") && c.eat_ident("rev") && c.eat_sym("(") && c.eat_sym(")") }; if end < lo || (end - lo) > 32 { return None; }
        let bp = c.pos; if lo == end { c.skip_balanced("{", "}"); return Some(()); }
        let iv_ty = Some(if lo >= 0 { ScalarTy::Usize } else { ScalarTy::I64 }); let ks: Vec<i64> = if rev { (lo..end).rev().collect() } else { (lo..end).collect() };
        for k in ks {
            c.pos = bp; let kid = self.prog.push(Op::Const(k)); if iv != "_" { self.vars.insert(iv.clone(), Val::Scalar(kid, iv_ty)); }
            if self.parse_block(c)?.2 { return None; }
        }
        Some(())
    }
    fn parse_compound_rhs(&mut self, op: &str, old: usize, old_ty: Option<ScalarTy>, r: usize, r_ty: Option<ScalarTy>) -> Option<Val> {
        if op == "=" { Some(Val::Scalar(r, old_ty.or(r_ty))) } else { self.apply_binop(op.strip_suffix('=')?, old, old_ty, r, r_ty) }
    }
    fn parse_block(&mut self, c: &mut Cursor<'_>) -> Option<(Vec<Val>, Option<Val>, bool)> {
        if !c.eat_sym("{") { return None; }
        let (mut rets, mut tail, mut returned) = (Vec::new(), None, false);
        while !c.eat_sym("}") {
            c.peek()?;
            if c.eat_ident("let") {
                let (pat_pos, mut d) = (c.pos, 0usize);
                while let Some(t) = c.peek() { match t { Tok::Sym(":" | "=") if d == 0 => break, Tok::Sym("(" | "[" | "{") => { d += 1; c.pos += 1; } Tok::Sym(")" | "]" | "}") => { d = d.saturating_sub(1); c.pos += 1; } _ => c.pos += 1 } }
                let hint = self.parse_let_type_hint(c)?; if !c.eat_sym("=") { return None; }
                let mut val = if matches!(c.peek(), Some(Tok::Sym("["))) { c.pos += 1; self.parse_array_lit(c, hint)? } else { self.parse_expr(c)? };
                if let (Val::Scalar(id, None), Some(ht)) = (&val, hint) {
                    if self.is_async { if let Some(&Op::Param(p)) = self.prog.nodes.get(*id) { if let Some(s) = self.prog.param_domains.get_mut(usize::from(p)) { *s = ht.domain(); } } }
                    val = Val::Scalar(*id, Some(ht));
                }
                if !c.eat_sym(";") { return None; }
                let mut pc = Cursor { toks: self.toks, pos: pat_pos }; self.bind_pat(&mut pc, val)?;
            } else if matches!(c.peek(), Some(Tok::Ident(w)) if matches!(w.as_str(), "assert" | "debug_assert" | "assert_eq" | "debug_assert_eq" | "assert_ne" | "debug_assert_ne")) {
                let kw = c.expect_ident()?; self.parse_assert(&kw, c)?;
            } else if c.eat_ident("if") || c.eat_ident("match") {
                let is_if = matches!(c.toks.get(c.pos.saturating_sub(1)), Some(Tok::Ident(w)) if w == "if"); let (val, all_ret) = if is_if { self.parse_if(c)? } else { self.parse_match(c)? };
                if all_ret { returned = true; }
                if !c.eat_sym(";") && matches!(c.peek(), Some(Tok::Sym("}"))) { if let Some(v) = val { tail = Some(v.clone()); rets.push(v); } }
            } else if c.eat_ident("for") { self.parse_for_loop(c)?; }
            else if c.eat_ident("return") {
                returned = true; if !c.eat_sym(";") { let rv = self.parse_expr(c)?; let _ = c.eat_sym(";"); self.record_return(rv.clone()); rets.push(rv); }
            } else if matches!(c.peek(), Some(Tok::Ident(nm)) if matches!(self.vars.get(nm), Some(Val::Buf(_)))) && self.looks_like_store(c) {
                let nm = c.expect_ident()?; let Some(&Val::Buf(bb)) = self.vars.get(&nm) else { return None; }; if !bb.mutable || !c.eat_sym("[") { return None; }
                let (idx, _) = scalar_id(&self.parse_expr(c)?)?; if !c.eat_sym("]") { return None; }
                let op = match c.next()? { Tok::Sym(s) => *s, _ => return None }; let (r, rt) = scalar_id(&self.parse_expr(c)?)?; if !c.eat_sym(";") { return None; }
                let ri = self.buf_index(bb, idx);
                let nv = if op == "=" { r } else { let cur = self.push_g(Op::Load { buf: bb.id, idx: ri }); scalar_id(&self.parse_compound_rhs(op, cur, Some(bb.elem_ty), r, rt)?)?.0 };
                let st = self.push_g(Op::Store { buf: bb.id, idx: ri, val: nv }); self.stores.push(st);
            } else if matches!(c.peek(), Some(Tok::Ident(nm)) if matches!(self.vars.get(nm), Some(Val::Struct(..)))) && matches!(c.peek_at(1), Some(Tok::Sym(".")))
                && matches!(c.peek_at(2), Some(Tok::Ident(_))) && matches!(c.peek_at(3), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=")))
            {
                let (nm, _, fld, op) = (c.expect_ident()?, c.next()?, c.expect_ident()?, match c.next()? { Tok::Sym(s) => *s, _ => return None });
                let (r, rt) = scalar_id(&self.parse_expr(c)?)?; if !c.eat_sym(";") { return None; }
                let Some(Val::Struct(sn, mut fs)) = self.vars.get(&nm).cloned() else { return None; }; let (_, fv) = fs.iter_mut().find(|(k, _)| k == &fld)?; let (old, ot) = scalar_id(fv)?;
                *fv = self.parse_compound_rhs(op, old, ot, r, rt)?; self.vars.insert(nm, Val::Struct(sn, fs));
            } else if self.looks_like_assign(c) {
                let (deref, nm, op) = (c.eat_sym("*"), c.expect_ident()?, match c.next()? { Tok::Sym(s) => *s, _ => return None });
                let rhs = self.parse_expr(c)?; if !c.eat_sym(";") { return None; }
                let nv = if op == "=" { match (self.vars.get(&nm), rhs) { (Some(Val::Scalar(_, ot)), Val::Scalar(r, rt)) => Val::Scalar(r, ot.or(rt)), (_, v) => v } }
                    else { let (old, ot) = scalar_id(self.vars.get(&nm)?)?; let (r, rt) = scalar_id(&rhs)?; self.parse_compound_rhs(op, old, ot, r, rt)? };
                if deref { Self::flatten_val(&nv, &mut self.stores); }
                self.vars.insert(nm, nv);
            } else {
                let v = self.parse_expr(c)?; if c.eat_sym(";") { continue; }
                tail = Some(v.clone()); rets.push(v); return c.eat_sym("}").then_some((rets, tail, returned));
            }
        }
        Some((rets, tail, returned))
    }
}
fn add_struct_params(ctx: &mut LowerCtx<'_>, prefix: &str, tname: &str) -> Option<(Val, StructFields)> {
    let def = ctx.file.structs.get(tname)?; let (mut fs, mut pfs) = (Vec::with_capacity(def.fields.len()), Vec::with_capacity(def.fields.len()));
    for (fname, fty) in &def.fields {
        let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(format!("{prefix}_{fname}"), fty.domain());
        fs.push((fname.clone(), Val::Scalar(pid, Some(*fty)))); pfs.push((fname.clone(), *fty, pidx));
    }
    Some((Val::Struct(tname.to_string(), fs), pfs))
}
fn push_scalar_param(ctx: &mut LowerCtx<'_>, pname: String, poc_name: String, st: ScalarTy, dom: Domain, by_ref: bool, mutable: bool) -> Option<()> {
    let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(&pname, dom); if by_ref && mutable { ctx.mut_refs.insert(pname.clone()); }
    ctx.poc_params.push(PocParam::Scalar { name: poc_name, ty: st, pidx, by_ref, mutable });
    ctx.vars.insert(pname, Val::Scalar(pid, Some(st))); Some(())
}
type ParamNames = (String, String, bool);
type ParamMeta = (Option<Domain>, bool, Option<(u16, usize)>);
fn lower_concrete_param(ctx: &mut LowerCtx<'_>, c: &mut Cursor<'_>, item: &FnItem, (pname, poc_name, bind_mut): ParamNames, (ov, is_uninit, reg_ov): ParamMeta) -> Option<()> {
    if c.eat_sym("&") {
        let mutable = c.eat_ident("mut");
        if c.eat_sym("[") {
            let (ety, (region, offset)) = (c.expect_ident().and_then(|e| ctx.file.resolve_scalar(&e))?, reg_ov.unwrap_or_else(|| (ctx.alloc_region(), 0)));
            if c.eat_sym(";") {
                let len_i = ctx.file.eval_const_expr(c, item.self_ty.as_deref())?.0; if len_i <= 0 || !c.eat_sym("]") { return None; }
                let len = len_i as usize;
                let bid = if is_uninit { ctx.prog.add_uninit_buf(&pname, len, mutable, region, offset, ov.unwrap_or_else(|| ety.domain())) } else { ctx.prog.add_buf(&pname, len, mutable, region, offset, ov.unwrap_or_else(|| ety.domain())) };
                if mutable { ctx.mut_refs.insert(pname.clone()); }
                ctx.poc_params.push(PocParam::Array { name: poc_name, ety, len, by_ref: true, mutable });
                ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: len, len_node: None, root_len: None, mutable, elem_ty: ety })); return Some(());
            }
            if !c.eat_sym("]") { return None; }
            let spec = if mutable { format!("mut_slice_len:{pname}:{}", ety.as_str()) } else { format!("slice_len:{pname}:{}", ety.as_str()) };
            let pidx = ctx.prog.param_domains.len(); let len_pid = ctx.prog.add_named_param(spec, ov.unwrap_or_else(|| Domain::range(0, MAX_SYM_SLICE_LEN as i64)));
            let bid = if is_uninit { ctx.prog.add_uninit_buf(&pname, MAX_SYM_SLICE_LEN, mutable, region, offset, ety.domain()) } else { ctx.prog.add_buf(&pname, MAX_SYM_SLICE_LEN, mutable, region, offset, ety.domain()) };
            if mutable { ctx.mut_refs.insert(pname.clone()); }
            ctx.poc_params.push(PocParam::Slice { name: poc_name, ety, pidx, mutable });
            ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: MAX_SYM_SLICE_LEN, len_node: Some(len_pid), root_len: Some(len_pid), mutable, elem_ty: ety })); return Some(());
        }
        let tname = ctx.resolve_ty(&c.expect_ident()?).to_string();
        if let Some(st) = ctx.file.resolve_scalar(&tname) { return push_scalar_param(ctx, pname, poc_name, st, ov.unwrap_or_else(|| st.domain()), true, mutable); }
        if !mutable || item.is_async {
            if let Some((sv, fields)) = add_struct_params(ctx, &pname, &tname) {
                if mutable { ctx.mut_refs.insert(pname.clone()); }
                ctx.poc_params.push(PocParam::Struct { name: poc_name, ty: tname, fields, by_ref: true, mutable }); ctx.vars.insert(pname, sv); return Some(());
            }
        }
        return None;
    }
    if c.eat_sym("[") {
        let ety = c.expect_ident().and_then(|e| ctx.file.resolve_scalar(&e))?; if !c.eat_sym(";") { return None; }
        let len_i = ctx.file.eval_const_expr(c, item.self_ty.as_deref())?.0; if len_i <= 0 || len_i > 64 || !c.eat_sym("]") { return None; }
        let (region, offset) = reg_ov.unwrap_or_else(|| (ctx.alloc_region(), 0)); let bid = ctx.prog.add_buf(&pname, len_i as usize, bind_mut, region, offset, ov.unwrap_or_else(|| ety.domain()));
        ctx.poc_params.push(PocParam::Array { name: poc_name, ety, len: len_i as usize, by_ref: false, mutable: false });
        ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: len_i as usize, len_node: None, root_len: None, mutable: bind_mut, elem_ty: ety })); return Some(());
    }
    let raw = c.expect_ident()?;
    if raw == "Option" && c.eat_sym("<") {
        let it = ctx.file.resolve_scalar(&c.expect_ident()?)?; if !c.eat_sym(">") { return None; }
        let (is_some_idx, is_some) = (ctx.prog.param_domains.len(), ctx.prog.add_named_param(format!("{pname}_is_some"), Domain::range(0, 1)));
        let (val_idx, val) = (ctx.prog.param_domains.len(), ctx.prog.add_named_param(format!("{pname}_val"), ov.unwrap_or_else(|| it.domain())));
        ctx.poc_params.push(PocParam::Opt { name: poc_name, ty: it, is_some: is_some_idx, val: val_idx });
        ctx.vars.insert(pname, Val::Opt { is_some, payload: Box::new(Val::Scalar(val, Some(it))) }); return Some(());
    }
    let tname = ctx.resolve_ty(&raw).to_string();
    if let Some(st) = ctx.file.resolve_scalar(&tname) { return push_scalar_param(ctx, pname, poc_name, st, ov.unwrap_or_else(|| st.domain()), false, false); }
    if let Some((sv, fields)) = add_struct_params(ctx, &pname, &tname) { ctx.poc_params.push(PocParam::Struct { name: poc_name, ty: tname, fields, by_ref: false, mutable: false }); ctx.vars.insert(pname, sv); return Some(()); }
    if let Some(ed) = ctx.file.enums.get(&tname) {
        let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(&pname, Domain::range(0, ed.max_disc));
        ctx.poc_params.push(PocParam::Enum { name: poc_name, ty: tname, pidx, by_ref: false }); ctx.vars.insert(pname, Val::Scalar(pid, Some(ScalarTy::Usize))); return Some(());
    }
    None
}
fn lower_param(ctx: &mut LowerCtx<'_>, c: &mut Cursor<'_>, item: &FnItem) -> Option<()> {
    let (mut pm, mut pd, mut pu, mut pr) = (FnMeta::default(), None, false, None);
    loop {
        match c.peek() { Some(Tok::Doc(l)) => { parse_doc_meta(l, &mut pm); c.pos += 1; } Some(Tok::Sym("#")) => { let (d, u, r, _) = c.parse_attr(&mut pm); pd = pd.or(d); pu |= u; pr = pr.or(r); } _ => break }
    }
    let (is_ref_self, is_mut_self) = (c.eat_sym("&"), c.eat_ident("mut"));
    if c.eat_ident("self") {
        let st_name = item.self_ty.as_deref()?;
        if let Some((sv, fields)) = add_struct_params(ctx, "self", st_name) {
            if is_ref_self && is_mut_self { ctx.mut_refs.insert("self".to_string()); }
            ctx.poc_params.push(PocParam::Struct { name: "self_val".to_string(), ty: st_name.to_string(), fields, by_ref: is_ref_self, mutable: is_ref_self && is_mut_self });
            ctx.vars.insert("self".to_string(), sv); return Some(());
        }
        if let Some(ed) = ctx.file.enums.get(st_name) {
            if is_ref_self && is_mut_self { return None; }
            let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param("self", Domain::range(0, ed.max_disc));
            ctx.poc_params.push(PocParam::Enum { name: "self_val".to_string(), ty: st_name.to_string(), pidx, by_ref: is_ref_self });
            ctx.vars.insert("self".to_string(), Val::Scalar(pid, Some(ScalarTy::Usize))); return Some(());
        }
        if item.is_async { ctx.has_opaque = true; ctx.vars.insert("self".to_string(), Val::Opaque); return Some(()); }
        return None;
    }
    if is_ref_self { return None; }
    let (bind_mut, pname) = (is_mut_self, c.expect_ident()?); if !c.eat_sym(":") { return None; }
    let (ty_pos, poc_name) = (c.pos, if pname == "_" { format!("p{}", ctx.poc_params.len()) } else { pname.clone() });
    let ov = pd.or_else(|| pm.domains.get(&pname).copied()).or_else(|| item.meta.domains.get(&pname).copied());
    let is_uninit = pu || pm.uninit.contains(&pname) || item.meta.uninit.contains(&pname);
    let reg_ov = pr.or_else(|| pm.regions.get(&pname).copied()).or_else(|| item.meta.regions.get(&pname).copied());
    if lower_concrete_param(ctx, c, item, (pname.clone(), poc_name, bind_mut), (ov, is_uninit, reg_ov)).is_some() { return Some(()); }
    if item.is_async { c.pos = ty_pos; c.skip_until(",", ")", true); ctx.has_opaque = true; if pname != "_" { ctx.vars.insert(pname, Val::Opaque); } return Some(()); }
    None
}
fn eat_bracket_ret(c: &mut Cursor<'_>, idx: &FileIndex, self_ty: Option<&str>) -> Option<()> {
    idx.resolve_scalar(&c.expect_ident()?)?; if c.eat_sym(";") { let _ = idx.eval_const_expr(c, self_ty)?; } c.eat_sym("]").then_some(())
}
fn validate_ret_ty(c: &mut Cursor<'_>, idx: &FileIndex, self_ty: Option<&str>) -> Option<bool> {
    let ret_opt = if !c.eat_sym("->") { false } else if c.eat_sym("(") {
        while !c.eat_sym(")") {
            let _ = c.eat_sym("&"); let _ = c.eat_ident("mut");
            if c.eat_sym("[") { eat_bracket_ret(c, idx, self_ty)?; }
            else { let nm = c.expect_ident()?; let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) && !idx.enums.contains_key(rn) { return None; } }
            let _ = c.eat_sym(",");
        }
        false
    } else if c.eat_sym("&") {
        let _ = c.eat_ident("mut");
        if c.eat_sym("[") { eat_bracket_ret(c, idx, self_ty)?; }
        else { let nm = c.expect_ident()?; let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) { return None; } }
        false
    } else if c.eat_sym("[") {
        idx.resolve_scalar(&c.expect_ident()?)?; if !c.eat_sym(";") { return None; }
        let len = idx.eval_const_expr(c, self_ty)?.0; if len <= 0 || len > 64 || !c.eat_sym("]") { return None; } false
    } else {
        let mut nm = c.expect_ident()?; while c.eat_sym("::") { nm = c.expect_ident()?; }
        if (nm == "Option" || nm == "Result") && matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); true }
        else { let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) && !idx.enums.contains_key(rn) { return None; } false }
    }; if c.eat_ident("where") { c.skip_until("{", ";", false); }
    matches!(c.peek(), Some(Tok::Sym("{"))).then_some(ret_opt)
}
fn lower_fn_item(item: &FnItem, file: &FileIndex, toks: &[Tok], inlined: &mut BTreeSet<String>, opts: RustFeOptions) -> Option<LoweredFn> {
    if item.is_unsafe { return None; }
    let (mut c, mut has_opaque) = (Cursor { toks, pos: item.sig_pos }, false);
    if !c.eat_empty_generics() { if !item.is_async { return None; } c.pos = item.sig_pos; c.skip_angles(); has_opaque = true; }
    if !c.eat_sym("(") { return None; }
    let mut prog = Program::new(&item.name); prog.simd_lanes = 1; prog.check_reg_budget = opts.enforce_reg_budget;
    let mut ctx = LowerCtx {
        prog, poc_params: Vec::new(), vars: BTreeMap::new(), mut_refs: BTreeSet::new(), stores: Vec::new(), cur_guard: None, early_rets: Vec::new(), file, toks,
        depth: 0, inlined_fns: inlined, next_region: 1, self_ty: item.self_ty.clone(), no_struct_lit: false, returns_opt: false, is_async: item.is_async, has_opaque,
    }; while !c.eat_sym(")") { lower_param(&mut ctx, &mut c, item)?; let _ = c.eat_sym(","); }
    ctx.returns_opt = validate_ret_ty(&mut c, file, item.self_ty.as_deref())?; let (rets, tail, _) = ctx.parse_block(&mut c)?; let mut final_val = tail.or_else(|| rets.into_iter().next());
    for (cond, ev) in std::mem::take(&mut ctx.early_rets).into_iter().rev() {
        final_val = Some(match final_val {
            Some(cur) if ctx.is_const_zero_opt(&cur) && matches!(ev, Val::Opt { .. }) => { let nc = ctx.mk_bool(cond, false); ctx.merge_val(nc, cur, ev, None)? }
            Some(cur) => ctx.merge_val(cond, ev, cur, None)?, None => ev,
        });
    }
    if let Some(fv) = final_val { let mut flat = Vec::new(); LowerCtx::flatten_val(&fv, &mut flat); for r in flat { ctx.prog.add_output(r); } }
    for s in ctx.stores { if !ctx.prog.outputs.contains(&s) { ctx.prog.add_output(s); } }
    Some(LoweredFn { prog: ctx.prog, params: ctx.poc_params, is_async: ctx.is_async, has_opaque: ctx.has_opaque })
}
fn fmt_scalar(ty: ScalarTy, v: i64) -> String { if ty == ScalarTy::Bool { if v != 0 { "true" } else { "false" }.to_string() } else { v.to_string() } }
fn ref_arg(name: &str, by_ref: bool, mutable: bool) -> (&'static str, String) { if !by_ref { ("let", name.to_string()) } else if mutable { ("let mut", format!("&mut {name}")) } else { ("let", format!("&{name}")) } }
fn render_poc_test(lf: &LoweredFn, file: &FileIndex, ce: &Counterexample) -> String {
    let clean: String = lf.prog.name.split(|c: char| !c.is_ascii_alphanumeric() && c != '_').filter(|s| !s.is_empty()).collect::<Vec<_>>().join("_");
    let tid = match clean.trim_matches('_') { "" => "witness", s => s };
    let mut out = format!("#[test]\nfn poc_{tid}() {{\n    // zero-check witness: node {} fault {} inputs={:?}\n", ce.node, fault_name(ce.fault), ce.inputs);
    let mut args = Vec::with_capacity(lf.params.len());
    for p in &lf.params {
        let (line, arg) = match p {
            PocParam::Scalar { name, ty, pidx, by_ref, mutable } => { let (kw, a) = ref_arg(name, *by_ref, *mutable); (format!("    {kw} {name}: {} = {};\n", ty.as_str(), fmt_scalar(*ty, ce.inputs.get(*pidx).copied().unwrap_or(0))), a) }
            PocParam::Array { name, ety, len, by_ref, mutable } => { let (kw, a) = ref_arg(name, *by_ref, *mutable); (format!("    {kw} {name}: [{}; {len}] = [Default::default(); {len}];\n", ety.as_str()), a) }
            PocParam::Slice { name, ety, pidx, mutable } => { let len = usize::try_from(ce.inputs.get(*pidx).copied().unwrap_or(0)).map_or(0, |n| n.min(MAX_SYM_SLICE_LEN)); let (kw, a) = ref_arg(name, true, *mutable); (format!("    {kw} {name}: Vec<{}> = vec![Default::default(); {len}];\n", ety.as_str()), a) }
            PocParam::Opt { name, ty, is_some, val } => { let rhs = if ce.inputs.get(*is_some).copied().unwrap_or(0) != 0 { format!("Some({})", fmt_scalar(*ty, ce.inputs.get(*val).copied().unwrap_or(0))) } else { "None".to_string() }; (format!("    let {name}: Option<{}> = {rhs};\n", ty.as_str()), name.clone()) }
            PocParam::Struct { name, ty, fields, by_ref, mutable } => { let (kw, a) = ref_arg(name, *by_ref, *mutable); let fs: Vec<String> = fields.iter().map(|(f, ft, idx)| format!("{f}: {}", fmt_scalar(*ft, ce.inputs.get(*idx).copied().unwrap_or(0)))).collect(); (format!("    {kw} {name} = {ty} {{ {} }};\n", fs.join(", ")), a) }
            PocParam::Enum { name, ty, pidx, by_ref } => { let v = ce.inputs.get(*pidx).copied().unwrap_or(0); let vn = file.enums.get(ty).and_then(|e| e.variants.iter().find(|(_, &d)| d == v).or_else(|| e.variants.iter().next())).map_or("_", |(k, _)| k.as_str()); let (kw, a) = ref_arg(name, *by_ref, false); (format!("    {kw} {name} = {ty}::{vn};\n"), a) }
        }; out.push_str(&line); args.push(arg);
    }
    let call = format!("{}({})", lf.prog.name, args.join(", "));
    if lf.is_async { out.push_str(&format!("    let mut cx = std::task::Context::from_waker(std::task::Waker::noop());\n    let mut fut = std::pin::pin!({call});\n    for _ in 0..8 {{ if std::future::Future::poll(fut.as_mut(), &mut cx).is_ready() {{ break; }} }}\n}}\n")); }
    else { out.push_str(&format!("    let _ = {call};\n}}\n")); }
    out
}
fn extract_poc(lf: &LoweredFn, file: &FileIndex, error: &VerifyError, cfg: RefineConfig) -> Option<String> {
    if lf.has_opaque { return None; }
    let ce = match error {
        VerifyError::CounterexampleFound { node, fault, inputs } => Counterexample { inputs: inputs.clone(), node: *node, fault: *fault },
        VerifyError::DivByZero { .. } | VerifyError::OutOfBounds { .. } | VerifyError::ExplicitPanic { .. } | VerifyError::ShiftOverflow { .. } | VerifyError::IntOverflow { .. } | VerifyError::UseAfterFree { .. } | VerifyError::DoubleFree { .. } | VerifyError::UninitializedRead { .. } =>
            sample_counterexample(&lf.prog, cfg.seed).or_else(|| refine_and_fuzz(&lf.prog, RefineConfig { max_epochs: 1, fuzz_ticks_per_box: 1, ..cfg }).counterexamples.into_iter().next())?,
        _ => return None,
    };
    Some(render_poc_test(lf, file, &ce))
}
fn parse_rust_with_poc_params(src: &str, opts: RustFeOptions) -> ParsedPocEntries {
    let (toks, mut entries, mut skipped_raw, mut inlined) = (tokenize_rust(src), Vec::new(), Vec::new(), BTreeSet::new()); let file = scan_file(&toks);
    for item in &file.fns {
        if is_intrinsic(&item.name) || (opts.skip_cfg_test && item.is_test) { continue; }
        if let Some(p) = lower_fn_item(item, &file, &toks, &mut inlined, opts) { entries.push(p); } else { skipped_raw.push(item.name.clone()); }
    }
    (file, entries, skipped_raw.into_iter().filter(|n| !inlined.contains(n)).collect())
}
/// Parse Safe-Rust functions from raw `.rs` source into `Program` IR using explicit `RustFeOptions`.
#[must_use] pub fn parse_rust_programs_with_opts(src: &str, opts: RustFeOptions) -> ParsedRustUnit {
    let (_, entries, skipped_non_kernel_fns) = parse_rust_with_poc_params(src, opts); ParsedRustUnit { programs: entries.into_iter().map(|lf| lf.prog).collect(), skipped_non_kernel_fns }
}
/// Parse Safe-Rust functions from raw `.rs` source into `Program` IR with default kernel options.
#[must_use] pub fn parse_rust_programs(src: &str) -> ParsedRustUnit { parse_rust_programs_with_opts(src, RustFeOptions::default()) }
fn verify_rust_unit(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig, opts: RustFeOptions) -> (RustProofReport, Vec<(usize, LoweredFn)>) {
    let (fidx, entries, skipped_non_kernel_fns) = parse_rust_with_poc_params(src, opts); let (mut proven, mut failed, mut failed_lf) = (Vec::new(), Vec::new(), Vec::new());
    for lf in entries {
        let name = lf.prog.name.clone();
        match verify_program(&lf.prog, profile, cfg) {
            Ok(rep) => proven.push((name, rep)),
            Err(error) => {
                let poc_test = extract_poc(&lf, &fidx, &error, cfg); failed_lf.push((failed.len(), lf)); failed.push(RustFnFailure { fn_name: name, error, poc_test, entrypoint_trace: None });
            }
        }
    }
    (RustProofReport { file: file.to_string(), proven, failed, suppressed_guarded: Vec::new(), skipped_non_kernel_fns }, failed_lf)
}
/// Parse and formally verify every supported function in a raw `.rs` source string using explicit `RustFeOptions`.
#[must_use] pub fn verify_rust_functions_with_opts(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig, opts: RustFeOptions) -> RustProofReport {
    let (mut rep, fl) = verify_rust_unit(file, src, profile, cfg, opts);
    if opts.interprocedural_reachability && !fl.is_empty() {
        let fl_all: Vec<(usize, usize, LoweredFn)> = fl.into_iter().map(|(fi, lf)| (0, fi, lf)).collect();
        crate::callgraph::apply_interprocedural_reachability(None, &[], &[src.to_string()], std::slice::from_mut(&mut rep), &fl_all, &[], (opts.skip_cfg_test, profile, cfg));
    }
    rep
}
/// Parse and formally verify every supported function in a raw `.rs` source string.
#[must_use] pub fn verify_rust_functions(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> RustProofReport { verify_rust_functions_with_opts(file, src, profile, cfg, RustFeOptions::default()) }
/// Parse and verify all supported functions across a `.rs` file or crate directory using explicit `RustFeOptions`.
pub fn verify_crate_functions_with_opts(dir: &Path, profile: ArchProfile, cfg: RefineConfig, skip: &[String], opts: RustFeOptions) -> Result<Vec<RustProofReport>, VerifyError> {
    let mut files = Vec::new(); crate::lint_rs::collect_rs_files_opts(dir, skip, opts.skip_cfg_test, &mut files)?; files.sort();
    let (mut srcs, mut reports, mut fl_all) = (Vec::with_capacity(files.len()), Vec::with_capacity(files.len()), Vec::new());
    for (ridx, p) in files.iter().enumerate() {
        let src = std::fs::read_to_string(p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?; let (rep, fl) = verify_rust_unit(&p.display().to_string(), &src, profile, cfg, opts);
        fl_all.extend(fl.into_iter().map(|(fi, lf)| (ridx, fi, lf))); srcs.push(src); reports.push(rep);
    }
    if opts.interprocedural_reachability && !fl_all.is_empty() {
        crate::callgraph::apply_interprocedural_reachability(Some(dir), &files, &srcs, &mut reports, &fl_all, skip, (opts.skip_cfg_test, profile, cfg));
    }
    Ok(reports)
}
/// Parse and verify all supported functions across a `.rs` file or crate directory.
pub fn verify_crate_functions(dir: &Path, profile: ArchProfile, cfg: RefineConfig) -> Result<Vec<RustProofReport>, VerifyError> { verify_crate_functions_skip(dir, profile, cfg, &[]) }
/// Parse and verify all supported functions across a `.rs` file or crate directory, skipping named entries.
pub fn verify_crate_functions_skip(dir: &Path, profile: ArchProfile, cfg: RefineConfig, skip: &[String]) -> Result<Vec<RustProofReport>, VerifyError> { verify_crate_functions_with_opts(dir, profile, cfg, skip, RustFeOptions::default()) }
