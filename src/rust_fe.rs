use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use crate::abstract_eval::{ArchProfile, CmpKind, Domain, IrOp, Op, Program, VerifyError};
use crate::simd_fuzz::{fault_name, refine_and_fuzz, sample_counterexample, Counterexample, RefineConfig};
use crate::{verify_program, ProgramReport};
pub const MAX_SYM_SLICE_LEN: usize = 65_536;
type LoopMutKey = (String, Option<String>);
type LoopMutMap = BTreeMap<LoopMutKey, u8>;
type LoopPreMap = BTreeMap<LoopMutKey, (usize, Option<ScalarTy>)>;
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
        }) }
    const fn as_str(self) -> &'static str { match self { Self::Bool => "bool", Self::U8 => "u8", Self::U16 => "u16", Self::U32 => "u32", Self::U64 => "u64", Self::Usize => "usize", Self::I8 => "i8", Self::I16 => "i16", Self::I32 => "i32", Self::I64 => "i64", Self::Isize => "isize" } }
    const fn is_unsigned(self) -> bool { matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64 | Self::Usize) }
    const fn is_narrow(self) -> bool { matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::I8 | Self::I16 | Self::I32) }
    const fn bits(self) -> usize { match self { Self::Bool => 1, Self::U8 | Self::I8 => 8, Self::U16 | Self::I16 => 16, Self::U32 | Self::I32 => 32, _ => 64 } }
    const fn bounds(self) -> (i64, i64) {
        match self { Self::Bool => (0, 1), Self::U8 => (0, 255), Self::U16 => (0, 65_535), Self::U32 => (0, 4_294_967_295), Self::U64 | Self::Usize => (0, i64::MAX), Self::I8 => (-128, 127), Self::I16 => (-32_768, 32_767), Self::I32 => (-2_147_483_648, 2_147_483_647), Self::I64 | Self::Isize => (i64::MIN, i64::MAX) }
    }
    fn domain(self) -> Domain { let (lo, hi) = self.bounds(); Domain::range(lo, hi) }
    const fn fits_in(self, dst: Self) -> bool { let (sl, sh) = self.bounds(); let (dl, dh) = dst.bounds(); sl >= dl && sh <= dh }
    fn assoc_const(self, name: &str) -> Option<i64> { match name { "BITS" => Some(self.bits() as i64), "MIN" => Some(self.bounds().0), "MAX" if !matches!(self, Self::U64 | Self::Usize) => Some(self.bounds().1), _ => None } } }
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok { Ident(String), Int(i64, Option<ScalarTy>), Str(usize, bool), Doc(String), Sym(&'static str) }
fn is_intrinsic(name: &str) -> bool { matches!(name, "zero_alloc" | "zero_free" | "zero_check_gen" | "zero_uninit_read" | "zero_uninit_write") }
fn parse_int_tok(raw: &str) -> Option<(i64, Option<ScalarTy>)> {
    let clean: String = raw.chars().filter(|&c| c != '_').collect();
    let (radix, body) = [("0x", 16), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)]
        .into_iter().find_map(|(p, r)| clean.strip_prefix(p).map(|b| (r, b))).unwrap_or((10, clean.as_str()));
    let end = body.find(|c: char| !c.is_digit(radix)).unwrap_or(body.len()); if end == 0 { return None; }
    let suf = &body[end..]; let ty = if suf.is_empty() { None } else { Some(ScalarTy::from_name(suf)?) };
    Some((i64::from_str_radix(&body[..end], radix).ok()?, ty)) }
fn parse_byte_lit(b: &[u8], i: &mut usize) -> Option<Tok> {
    if *i + 2 >= b.len() || *b.get(*i)? != b'b' || *b.get(*i + 1)? != b'\'' { return None; }
    let mut k = *i + 2;
    let val = if *b.get(k)? == b'\\' {
        k += 1; let esc = *b.get(k)?; k += 1;
        match esc {
            b'n' => b'\n', b'r' => b'\r', b't' => b'\t', b'0' => 0, b'\\' => b'\\', b'\'' => b'\'', b'"' => b'"',
            b'x' => { let h = std::str::from_utf8(b.get(k..k + 2)?).ok()?; k += 2; u8::from_str_radix(h, 16).ok()? }
            _ => return None, }
    } else { let c = *b.get(k)?; k += 1; c }; if *b.get(k)? != b'\'' { return None; }
    *i = k + 1; Some(Tok::Int(i64::from(val), Some(ScalarTy::U8))) }
fn scan_quoted_str(b: &[u8], i: &mut usize) -> (usize, bool) {
    let (n, mut len, mut ascii) = (b.len(), 0usize, true); *i += 1;
    while *i < n {
        let c = b.get(*i).copied().unwrap_or(0);
        if c == b'\\' && *i + 1 < n {
            let e = b.get(*i + 1).copied().unwrap_or(0);
            if e == b'u' { ascii = false; }
            len += 1; *i += 2;
        } else if c == b'"' { *i += 1; break; }
        else { if c >= 0x80 { ascii = false; } len += 1; *i += 1; } }
    (len, ascii) }
fn skip_quoted(b: &[u8], i: &mut usize, quote: u8) {
    let n = b.len(); *i += 1;
    while *i < n { let c = b.get(*i).copied().unwrap_or(0); if c == b'\\' && *i + 1 < n { *i += 2; } else if c == quote { *i += 1; break; } else { *i += 1; } } }
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
        } else if c0 == b'b' && b.get(i + 1) == Some(&b'"') { i += 1; let (l, a) = scan_quoted_str(b, &mut i); out.push(Tok::Str(l, a)); }
        else if c0 == b'r' && matches!(b.get(i + 1), Some(&b'"' | &b'#')) {
            let (mut k, mut hashes) = (i + 1, 0usize); while b.get(k) == Some(&b'#') { hashes += 1; k += 1; }
            if b.get(k) == Some(&b'"') {
                k += 1; let s0 = k;
                while k < n { if b.get(k) == Some(&b'"') && b.get(k + 1..k + 1 + hashes).is_some_and(|s| s.iter().all(|&x| x == b'#')) { let raw = &b[s0..k]; i = k + 1 + hashes; out.push(Tok::Str(raw.len(), raw.is_ascii())); break; } k += 1; }
                if i < k { i = k; out.push(Tok::Str(0, false)); }
            } else { i += 1; out.push(Tok::Ident("r".to_string())); }
        } else if c0 == b'"' { let (l, a) = scan_quoted_str(b, &mut i); out.push(Tok::Str(l, a)); }
        else if c0 == b'\'' {
            if b.get(i + 1) == Some(&b'\\') {
                let ascii = match b.get(i + 2) {
                    Some(b'n' | b'r' | b't' | b'0' | b'\\' | b'\'' | b'"') => b.get(i + 3) == Some(&b'\''),
                    Some(b'x') => b.get(i + 5) == Some(&b'\'') && b.get(i + 3..i + 5).and_then(|h| std::str::from_utf8(h).ok()).and_then(|h| u8::from_str_radix(h, 16).ok()).is_some_and(|v| v < 128),
                    _ => false, };
                skip_quoted(b, &mut i, b'\''); out.push(Tok::Sym(if ascii { "@c" } else { "@" }));
            } else if b.get(i + 2) == Some(&b'\'') {
                let ascii = b.get(i + 1).is_some_and(|&c| c < 0x80); i += 3; out.push(Tok::Sym(if ascii { "@c" } else { "@" }));
            } else if b.get(i + 1).is_some_and(|&c| c >= 0x80) && b.get(i + 1..n.min(i + 6)).is_some_and(|s| s.contains(&b'\'')) {
                skip_quoted(b, &mut i, b'\''); out.push(Tok::Sym("@"));
            } else { i += 1; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; } }
        } else if c0.is_ascii_alphabetic() || c0 == b'_' {
            let s = i; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; }
            out.push(Tok::Ident(src[s..i].to_string()));
        } else if c0.is_ascii_digit() {
            let s = i; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; }
            if b.get(i) == Some(&b'.') && b.get(i + 1).is_some_and(u8::is_ascii_digit) {
                i += 1; while i < n && b.get(i).is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') { i += 1; } out.push(Tok::Sym("@"));
            } else { out.push(parse_int_tok(&src[s..i]).map_or(Tok::Sym("@"), |(v, ty)| Tok::Int(v, ty))); }
        } else if let Some(&s) = MULTI.iter().find(|&&m| rest.starts_with(m.as_bytes())) { out.push(Tok::Sym(s)); i += s.len(); }
        else { out.push(Tok::Sym(SINGLE.iter().copied().find(|s| s.as_bytes().first() == Some(&c0)).unwrap_or("@"))); i += 1; } }
    out }
fn parse_signed(raw: &str) -> Option<i64> { let s = raw.trim(); if let Some(r) = s.strip_prefix('-') { parse_int_tok(r.trim()).and_then(|(v, _)| v.checked_neg()) } else { parse_int_tok(s).map(|(v, _)| v) } }
fn parse_domain_rhs(raw: &str) -> Option<Domain> {
    let s = raw.trim(); let (rp, mp) = match s.find("mod") { Some(p) => (s[..p].trim(), Some(s[p + 3..].trim())), None => (s, None) };
    let (lo, hi) = if let Some((a, b)) = rp.split_once("..=") { (parse_signed(a)?, parse_signed(b)?) }
        else if let Some((a, b)) = rp.split_once("..") { (parse_signed(a)?, parse_signed(b)?.checked_sub(1)?) }
        else { let v = parse_signed(rp)?; (v, v) };
    if let Some(mstr) = mp {
        let (ms, rs) = mstr.split_once("==")?; let (m, r) = (parse_signed(ms)?, parse_signed(rs)?);
        (m > 0).then(|| Domain::congruent(lo, hi, m, r))
    } else { Some(Domain::range(lo, hi)) } }
#[derive(Clone, Default)]
struct FnMeta { domains: BTreeMap<String, Domain>, uninit: BTreeSet<String>, regions: BTreeMap<String, (u16, usize)> }
fn collect_domain_spec(spec: &str, named: &mut BTreeMap<String, Domain>) -> Option<Domain> {
    let mut anon = None;
    for part in spec.trim().trim_start_matches('(').trim_end_matches(')').trim().split(',').map(str::trim).filter(|p| !p.is_empty()) {
        if let Some((k, v)) = part.split_once(':').or_else(|| part.split_once('=')) {
            let key = k.trim();
            if !key.is_empty() && key.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_') && !key.as_bytes().first().is_some_and(u8::is_ascii_digit) { if let Some(d) = parse_domain_rhs(v) { named.insert(key.to_string(), d); continue; } } }
        if let Some(d) = parse_domain_rhs(part) { anon = Some(d); } }
    anon }
fn parse_pair_region(s: &str) -> Option<(u16, usize)> {
    let (a, b) = s.trim().trim_start_matches('(').trim_end_matches(')').split_once(',')?;
    Some((a.trim().parse().ok()?, b.trim().parse().ok()?)) }
fn parse_doc_meta(line: &str, meta: &mut FnMeta) {
    if let Some(rest) = line.strip_prefix("@domain").or_else(|| line.strip_prefix("@zero_domain")) { let _ = collect_domain_spec(rest, &mut meta.domains); }
    else if let Some(rest) = line.strip_prefix("@uninit") { for p in rest.split([',', ' ', '\t']).map(str::trim).filter(|s| !s.is_empty()) { meta.uninit.insert(p.to_string()); } }
    else if let Some(rest) = line.strip_prefix("@region") { if let Some((k, v)) = rest.split_once(':') { if let Some(p) = parse_pair_region(v) { meta.regions.insert(k.trim().to_string(), p); } } } }
pub(crate) fn skip_bal(toks: &[Tok], mut i: usize, end: usize, open: &str, close: &str) -> usize {
    if !matches!(toks.get(i), Some(Tok::Sym(s)) if *s == open) { return i; }
    let (mut d, is_ang) = (1usize, close == ">"); i = i.saturating_add(1);
    while i < end && d > 0 {
        match toks.get(i) {
            Some(Tok::Sym(s)) if *s == open => d = d.saturating_add(1),
            Some(Tok::Sym(s)) if *s == close => d = d.saturating_sub(1),
            Some(Tok::Sym(">>")) if is_ang => d = d.saturating_sub(2), _ => {} }
        i = i.saturating_add(1); }
    i }
pub(crate) fn split_top_commas(sl: &[Tok], angles: bool) -> Vec<&[Tok]> {
    let (mut parts, mut s, mut d) = (Vec::new(), 0usize, 0usize);
    for (i, t) in sl.iter().enumerate() {
        match t {
            Tok::Sym("(" | "[" | "{") => d = d.saturating_add(1), Tok::Sym("<") if angles => d = d.saturating_add(1),
            Tok::Sym(")" | "]" | "}") => d = d.saturating_sub(1), Tok::Sym(">") if angles => d = d.saturating_sub(1),
            Tok::Sym(">>") if angles => d = d.saturating_sub(2),
            Tok::Sym(",") if d == 0 => { parts.push(sl.get(s..i).unwrap_or(&[])); s = i.saturating_add(1); } _ => {} } }
    if s <= sl.len() && (!sl.is_empty() || !parts.is_empty()) { parts.push(sl.get(s..).unwrap_or(&[])); }
    parts }
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
    fn skip_angles(&mut self) { self.pos = skip_bal(self.toks, self.pos, self.toks.len(), "<", ">"); }
    fn skip_until(&mut self, s1: &str, s2: &str, angles: bool) {
        let mut d = 0usize;
        while let Some(t) = self.peek() {
            match t {
                Tok::Sym(s) if d == 0 && (*s == s1 || *s == s2) => break,
                Tok::Sym("(" | "[") => { d += 1; self.pos += 1; } Tok::Sym("<") if angles => { d += 1; self.pos += 1; }
                Tok::Sym(")" | "]") => { d = d.saturating_sub(1); self.pos += 1; } Tok::Sym(">") if angles => { d = d.saturating_sub(1); self.pos += 1; }
                Tok::Sym(">>") if angles => { d = d.saturating_sub(2); self.pos += 1; } _ => self.pos += 1, }
        } }
    fn skip_balanced(&mut self, open: &str, close: &str) { self.pos = skip_bal(self.toks, self.pos, self.toks.len(), open, close); }
    fn skip_rest_of_braces(&mut self) { let mut d = 1usize; while let Some(t) = self.next() { match t { Tok::Sym("{") => d += 1, Tok::Sym("}") => { d -= 1; if d == 0 { break; } } _ => {} } } }
    fn skip_item_body(&mut self) { self.skip_until("{", ";", false); if matches!(self.peek(), Some(Tok::Sym("{"))) { self.skip_balanced("{", "}"); } else { let _ = self.eat_sym(";"); } }
    fn skip_doc_and_attrs(&mut self) {
        while matches!(self.peek(), Some(Tok::Doc(_))) { self.pos += 1; }
        while matches!(self.peek(), Some(Tok::Sym("#"))) { let mut dm = FnMeta::default(); let _ = self.parse_attr(&mut dm); }
    }
    fn parse_attr(&mut self, meta: &mut FnMeta) -> (Option<Domain>, bool, Option<(u16, usize)>, bool) {
        if !self.eat_sym("#") { return (None, false, None, false); }
        let inner = self.eat_sym("!"); if !matches!(self.peek(), Some(Tok::Sym("["))) { return (None, false, None, false); }
        let start = self.pos + 1; self.skip_balanced("[", "]");
        let slice = self.toks.get(start..self.pos.saturating_sub(1)).unwrap_or(&[]); let Some(Tok::Ident(name)) = slice.first() else { return (None, false, None, false); };
        let is_test = !inner && (name == "test" || (name == "cfg" && slice.iter().any(|t| matches!(t, Tok::Ident(w) if w == "test" || w == "kani"))));
        if name == "zero_uninit" { return (None, true, None, is_test); }
        let mut text = String::new();
        for t in slice.get(1..).unwrap_or(&[]) {
            match t { Tok::Ident(s) => { text.push(' '); text.push_str(s); } Tok::Int(v, _) => { text.push(' '); text.push_str(&v.to_string()); } Tok::Sym(s) => text.push_str(s), Tok::Doc(_) | Tok::Str(_, _) => {} } }
        if name == "zero_domain" && slice.len() >= 3 { (collect_domain_spec(&text, &mut meta.domains), false, None, is_test) }
        else if name == "zero_region" { (None, false, parse_pair_region(&text), is_test) } else { (None, false, None, is_test) } } }
pub(crate) struct FnItem { pub(crate) name: String, pub(crate) short_name: String, sig_pos: usize, pub(crate) body: (usize, usize), meta: FnMeta, pub(crate) self_ty: Option<String>, pub(crate) is_test: bool, is_async: bool, is_unsafe: bool, pub(crate) vis: u8, in_generic_impl: bool, pub(crate) in_mod: bool }
#[derive(Clone, Copy, Debug)]
enum FieldTy { Scalar(ScalarTy), Slice(ScalarTy, bool), Str, Opaque }
struct StructDef { fields: Vec<(String, FieldTy)> }
struct EnumDef { variants: BTreeMap<String, i64>, max_disc: i64 }
#[derive(Default)]
pub(crate) struct FileIndex {
    pub(crate) fns: Vec<FnItem>, consts: BTreeMap<String, (i64, Option<ScalarTy>)>, str_consts: BTreeMap<String, (usize, bool)>,
    structs: BTreeMap<String, StructDef>, enums: BTreeMap<String, EnumDef>, type_aliases: BTreeMap<String, ScalarTy>, }
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
                    return self.consts.get(&format!("{base}::{sub}")).copied(); }
                self.consts.get(&nm).copied() }
            _ => None, } }
    fn eval_const_expr(&self, c: &mut Cursor<'_>, self_ty: Option<&str>) -> Option<(i64, Option<ScalarTy>)> {
        let (mut v, mut ty) = self.eval_const_atom(c, self_ty)?;
        while let Some(&Tok::Sym(op)) = c.peek() {
            if !matches!(op, "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | "|" | "&" | "^") { break; }
            c.pos += 1; let (r, rty) = self.eval_const_atom(c, self_ty)?; ty = ty.or(rty);
            v = match op {
                "+" => v.checked_add(r)?, "-" => v.checked_sub(r)?, "*" => v.checked_mul(r)?, "/" => v.checked_div(r)?, "%" => v.checked_rem(r)?, "|" => v | r, "&" => v & r, "^" => v ^ r,
                "<<" if (0..64).contains(&r) => v.checked_shl(r as u32)?, ">>" if (0..64).contains(&r) => v.checked_shr(r as u32)?, _ => return None,
            }; }
        if c.eat_ident("as") { let dt = self.resolve_scalar(&c.expect_ident()?)?; let (lo, hi) = dt.bounds(); if v < lo || v > hi { return None; } ty = Some(dt); }
        Some((v, ty)) } }
fn scan_const_item(c: &mut Cursor<'_>, idx: &mut FileIndex, prefix: Option<&str>) {
    let Some(name) = c.expect_ident() else { return; };
    if c.eat_sym(":") {
        let key = prefix.map_or_else(|| name.clone(), |p| format!("{p}::{name}"));
        if c.eat_sym("&") && c.eat_ident("str") && c.eat_sym("=") {
            if let Some(&Tok::Str(l, a)) = c.peek() { idx.str_consts.insert(key, (l, a)); c.pos += 1; }
        } else if let (Some(t), true) = (c.expect_ident().and_then(|s| idx.resolve_scalar(&s)), c.eat_sym("=")) { if let Some((v, _)) = idx.eval_const_expr(c, prefix) { idx.consts.insert(key, (v, Some(t))); } } }
    while let Some(t) = c.next() { match t { Tok::Sym(";") => break, Tok::Sym("{") => { c.pos -= 1; c.skip_balanced("{", "}"); } Tok::Sym("[") => { c.pos -= 1; c.skip_balanced("[", "]"); } _ => {} } } }
fn classify_field_ty(sl: &[Tok], idx: &FileIndex) -> FieldTy {
    match sl {
        [Tok::Ident(s)] => idx.resolve_scalar(s).map_or_else(|| if s == "String" { FieldTy::Str } else { FieldTy::Opaque }, FieldTy::Scalar),
        [Tok::Sym("&"), Tok::Ident(s)] if s == "str" || s == "String" => FieldTy::Str,
        [Tok::Sym("&"), Tok::Ident(m), Tok::Ident(s)] if m == "mut" && s == "str" => FieldTy::Str,
        [Tok::Sym("&"), Tok::Sym("["), Tok::Ident(e), Tok::Sym("]")] => idx.resolve_scalar(e).map_or(FieldTy::Opaque, |t| FieldTy::Slice(t, false)),
        [Tok::Sym("&"), Tok::Ident(m), Tok::Sym("["), Tok::Ident(e), Tok::Sym("]")] if m == "mut" => idx.resolve_scalar(e).map_or(FieldTy::Opaque, |t| FieldTy::Slice(t, true)),
        _ => FieldTy::Opaque, } }
fn scan_aggregate_item(c: &mut Cursor<'_>, idx: &mut FileIndex, is_enum: bool) {
    let Some(name) = c.expect_ident() else { return; };
    if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); }
    if c.eat_ident("where") { c.skip_until("{", ";", false); }
    if !c.eat_sym("{") { c.skip_item_body(); return; }
    if is_enum {
        let (mut variants, mut next_val, mut max_disc, mut ok) = (BTreeMap::new(), 0i64, 0i64, true);
        while !c.eat_sym("}") {
            c.skip_doc_and_attrs(); let Some(vname) = c.expect_ident() else { ok = false; break; }; if matches!(c.peek(), Some(Tok::Sym("(" | "{"))) { ok = false; break; }
            let v = if c.eat_sym("=") { if let Some((ev, _)) = idx.eval_const_expr(c, None) { ev } else { ok = false; break; } } else { next_val };
            variants.insert(vname, v); max_disc = max_disc.max(v); next_val = v.saturating_add(1); let _ = c.eat_sym(","); }
        if !ok { c.skip_rest_of_braces(); return; }
        if !variants.is_empty() && variants.values().all(|&v| v >= 0) { idx.enums.insert(name, EnumDef { variants, max_disc }); }
    } else {
        let (mut fields, mut ok) = (Vec::new(), true);
        while !c.eat_sym("}") {
            c.skip_doc_and_attrs(); if c.eat_ident("pub") && matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); }
            let Some(fname) = c.expect_ident() else { ok = false; break; }; if !c.eat_sym(":") { ok = false; break; }
            let (ts, mut d) = (c.pos, 0usize);
            while let Some(t) = c.peek() {
                match t {
                    Tok::Sym("," | "}") if d == 0 => break,
                    Tok::Sym("(" | "[" | "<" | "{") => { d += 1; c.pos += 1; }
                    Tok::Sym(")" | "]" | ">" | "}") => { d = d.saturating_sub(1); c.pos += 1; }
                    Tok::Sym(">>") => { d = d.saturating_sub(2); c.pos += 1; }
                    _ => c.pos += 1, } }
            let fty = classify_field_ty(c.toks.get(ts..c.pos).unwrap_or(&[]), idx); fields.push((fname, fty)); let _ = c.eat_sym(","); }
        if !ok { c.skip_rest_of_braces(); return; }
        let has_known = fields.iter().any(|(_, t)| !matches!(t, FieldTy::Opaque));
        if has_known && fields.len() <= 16 { idx.structs.insert(name, StructDef { fields }); } } }
fn scan_fn_decl(c: &mut Cursor<'_>, idx: &mut FileIndex, self_ty: Option<String>, meta: FnMeta, (is_test, is_async, is_unsafe, vis, in_generic_impl, in_mod): (bool, bool, bool, u8, bool, bool)) {
    let raw = c.expect_ident().unwrap_or_else(|| "<anon>".to_string()); let (sig_pos, name) = (c.pos, self_ty.as_ref().map_or_else(|| raw.clone(), |t| format!("{t}::{raw}")));
    c.skip_until("{", ";", false);
    if matches!(c.peek(), Some(Tok::Sym("{"))) {
        let bs = c.pos; c.skip_balanced("{", "}");
        idx.fns.push(FnItem { name, short_name: raw, sig_pos, body: (bs + 1, c.pos.saturating_sub(1)), meta, self_ty, is_test, is_async, is_unsafe, vis, in_generic_impl, in_mod });
    } else { let _ = c.eat_sym(";"); } }
fn scan_items(c: &mut Cursor<'_>, idx: &mut FileIndex, self_ty: Option<&str>, impl_test: bool, in_generic_impl: bool, in_mod: bool) {
    let (mut pending, mut is_test, mut is_async, mut is_unsafe, mut vis) = (FnMeta::default(), false, false, false, 0u8);
    while let Some(tok) = c.peek() {
        if (self_ty.is_some() || in_mod) && matches!(tok, Tok::Sym("}")) { c.pos += 1; break; }
        let mut reset = false;
        match tok {
            Tok::Doc(line) => { parse_doc_meta(line, &mut pending); c.pos += 1; }
            Tok::Sym("#") => { is_test |= c.parse_attr(&mut pending).3; }
            Tok::Ident(w) if w == "pub" => { c.pos += 1; vis = if matches!(c.peek(), Some(Tok::Sym("("))) { c.skip_balanced("(", ")"); 1 } else { 2 }; }
            Tok::Ident(w) if w == "extern" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Str(_, _))) { c.pos += 1; } }
            Tok::Ident(w) if w == "unsafe" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "async" | "extern")) { is_unsafe = true; } else { c.skip_item_body(); reset = true; } }
            Tok::Ident(w) if w == "async" => { c.pos += 1; if matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe")) { is_async = true; } else { c.skip_item_body(); reset = true; } }
            Tok::Ident(w) if w == "const" => { c.pos += 1; if !matches!(c.peek(), Some(Tok::Ident(n)) if matches!(n.as_str(), "fn" | "unsafe" | "async" | "extern")) { if !in_mod { scan_const_item(c, idx, self_ty); } else { c.skip_until(";", ";", false); let _ = c.eat_sym(";"); } reset = true; } }
            Tok::Ident(w) if w == "type" && self_ty.is_none() => {
                c.pos += 1; if !in_mod { if let Some(nm) = c.expect_ident() { if c.eat_sym("=") { if let Some(ty) = c.expect_ident().and_then(|s| idx.resolve_scalar(&s)) { idx.type_aliases.insert(nm, ty); } } } }
                while let Some(t) = c.next() { if matches!(t, Tok::Sym(";")) { break; } } reset = true; }
            Tok::Ident(w) if (w == "struct" || w == "enum") && self_ty.is_none() => { let ie = w == "enum"; c.pos += 1; if !in_mod { scan_aggregate_item(c, idx, ie); } else { c.skip_item_body(); } reset = true; }
            Tok::Ident(w) if w == "impl" && self_ty.is_none() => {
                c.pos += 1; let it = std::mem::take(&mut is_test); (pending, is_async, is_unsafe, vis) = (FnMeta::default(), false, false, 0);
                let gpos = c.pos; let ig = !c.eat_empty_generics(); if ig { c.pos = gpos; c.skip_angles(); }
                let (mut ty_name, mut after_for) = (None, false);
                while let Some(t) = c.peek() {
                    match t {
                        Tok::Sym("{" | ";") => break, Tok::Ident(k) if k == "for" => { after_for = true; ty_name = None; c.pos += 1; }
                        Tok::Ident(k) if k == "where" => { c.skip_until("{", ";", false); break; }
                        Tok::Ident(k) if !matches!(k.as_str(), "dyn" | "mut" | "const") => { if ty_name.is_none() || after_for { ty_name = Some(k.clone()); } c.pos += 1; }
                        Tok::Sym("<") => c.skip_angles(), Tok::Sym("(") => c.skip_balanced("(", ")"), _ => c.pos += 1, } }
                if let (Some(tn), true) = (ty_name, c.eat_sym("{")) { scan_items(c, idx, Some(&tn), impl_test || it, ig, in_mod); } else { c.skip_item_body(); } }
            Tok::Ident(w) if w == "mod" && self_ty.is_none() => {
                c.pos += 1; let mt = std::mem::take(&mut is_test); c.skip_until("{", ";", false);
                if c.eat_sym("{") { scan_items(c, idx, None, impl_test || mt, false, true); } else { let _ = c.eat_sym(";"); }
                reset = true; }
            Tok::Ident(w) if w == "trait" && self_ty.is_none() => { c.pos += 1; c.skip_item_body(); reset = true; }
            Tok::Ident(w) if w == "fn" => {
                c.pos += 1; let flags = (impl_test || std::mem::take(&mut is_test), std::mem::take(&mut is_async), std::mem::take(&mut is_unsafe), std::mem::take(&mut vis), in_generic_impl, in_mod);
                scan_fn_decl(c, idx, self_ty.map(str::to_string), std::mem::take(&mut pending), flags); }
            Tok::Sym("{") => { c.skip_balanced("{", "}"); reset = true; }
            _ => { c.pos += 1; reset = true; } }
        if reset { (pending, is_test, is_async, is_unsafe, vis) = (FnMeta::default(), false, false, false, 0); } } }
pub(crate) fn scan_file(toks: &[Tok]) -> FileIndex { let (mut c, mut idx) = (Cursor { toks, pos: 0 }, FileIndex::default()); scan_items(&mut c, &mut idx, None, false, false, false); idx }
#[derive(Clone, Copy, Debug)]
struct BufBind {
    id: u8, base_const: usize, base_node: Option<usize>, len_const: usize, len_node: Option<usize>,
    root_len: Option<usize>, mutable: bool, elem_ty: ScalarTy, is_str: bool, }
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
    Slice { name: String, ety: ScalarTy, pidx: usize, mutable: bool }, Str { name: String, pidx: usize, owned: bool }, Opt { name: String, ty: ScalarTy, is_some: usize, val: usize },
    Struct { name: String, ty: String, fields: StructFields, by_ref: bool, mutable: bool }, Enum { name: String, ty: String, pidx: usize, by_ref: bool }, }
type BufFrame = (u8, usize, Option<usize>);
#[derive(Clone, Default)]
struct Utf8State {
    str_ascii: BTreeSet<BufFrame>, char_bounds: BTreeSet<(BufFrame, usize)>, ascii_at_idx: BTreeSet<(BufFrame, usize)>,
    starts_lens: BTreeSet<(BufFrame, i64)>, ends_lens: BTreeSet<(BufFrame, i64)>, find_lits: BTreeMap<(BufFrame, usize), i64>, find_dyn: BTreeMap<(BufFrame, usize), usize>,
    ascii_preds: BTreeMap<usize, BufFrame>, cb_preds: BTreeMap<usize, (BufFrame, usize)>,
    starts_preds: BTreeMap<usize, (BufFrame, i64)>, ends_preds: BTreeMap<usize, (BufFrame, i64)>,
    ascii_byte_preds: BTreeMap<usize, (BufFrame, usize)>, byte_loads: BTreeMap<usize, (BufFrame, usize)>, }
fn scalar_id(v: &Val) -> Option<(usize, Option<ScalarTy>)> { if let &Val::Scalar(id, ty) = v { Some((id, ty)) } else { None } }
fn bin_prec(sym: &str) -> Option<u8> {
    match sym { "||" => Some(1), "&&" => Some(2), "==" | "!=" | "<" | "<=" | ">" | ">=" => Some(3), "|" => Some(4), "^" => Some(5), "&" => Some(6), "<<" | ">>" => Some(7), "+" | "-" => Some(8), "*" | "/" | "%" => Some(9), _ => None } }
struct LowerCtx<'a> {
    prog: Program, poc_params: Vec<PocParam>, vars: BTreeMap<String, Val>, mut_refs: BTreeSet<String>, stores: Vec<usize>, cur_guard: Option<(usize, bool)>,
    early_rets: Vec<(usize, Val)>, file: &'a FileIndex, toks: &'a [Tok], depth: u8, loop_depth: u8, in_loop: bool, inlined_fns: &'a mut BTreeSet<String>,
    next_region: u16, self_ty: Option<String>, no_struct_lit: bool, returns_opt: bool, is_async: bool, has_opaque: bool, utf8: Utf8State, }
impl<'a> LowerCtx<'a> {
    fn push_g(&mut self, op: IrOp) -> usize { self.prog.push_guarded(op, self.cur_guard) }
    fn mk_bool(&mut self, c: usize, pol: bool) -> usize { if pol { c } else { let z = self.prog.push(Op::Const(0)); self.prog.push(Op::Cmp(CmpKind::Eq, c, z)) } }
    fn and_guard(&mut self, old: Option<(usize, bool)>, add: (usize, bool)) -> Option<(usize, bool)> {
        let Some((g0, p0)) = old else { return Some(add); }; let (b0, b1, z) = (self.mk_bool(g0, p0), self.mk_bool(add.0, add.1), self.prog.push(Op::Const(0)));
        Some((self.prog.push(Op::Select { cond: b0, t_val: b1, f_val: z }), true)) }
    fn alloc_region(&mut self) -> u16 { let r = self.next_region; self.next_region = self.next_region.saturating_add(1); r }
    fn resolve_ty<'b>(&'b self, raw: &'b str) -> &'b str { if raw == "Self" { self.self_ty.as_deref().unwrap_or(raw) } else { raw } }
    fn const_of(&self, id: usize) -> Option<i64> { if let Some(&Op::Const(v)) = self.prog.nodes.get(id) { Some(v) } else { None } }
    fn buf_len_node(&mut self, bb: BufBind) -> usize { bb.len_node.unwrap_or_else(|| self.prog.push(Op::Const(bb.len_const as i64))) }
    fn mk_none(&mut self) -> Val { let z = self.prog.push(Op::Const(0)); Val::Opt { is_some: z, payload: Box::new(Val::Scalar(z, None)) } }
    fn is_const_zero_opt(&self, v: &Val) -> bool { matches!(v, Val::Opt { is_some, .. } if self.const_of(*is_some) == Some(0)) }
    fn in_bounds(&mut self, v: usize, lo: i64, hi: i64, inc: bool) -> usize {
        let (klo, khi, z) = (self.prog.push(Op::Const(lo)), self.prog.push(Op::Const(hi)), self.prog.push(Op::Const(0)));
        let (ge, le) = (self.push_g(Op::Cmp(CmpKind::Ge, v, klo)), self.push_g(Op::Cmp(if inc { CmpKind::Le } else { CmpKind::Lt }, v, khi)));
        self.push_g(Op::Select { cond: ge, t_val: le, f_val: z }) }
    fn store_guarded(&mut self, buf: u8, idx: usize, val: usize, lo: usize, hi: usize) {
        let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let (ge, lt) = (self.push_g(Op::Cmp(CmpKind::Ge, idx, lo)), self.push_g(Op::Cmp(CmpKind::Lt, idx, hi)));
        let ok = self.push_g(Op::Select { cond: ge, t_val: lt, f_val: z }); self.cur_guard = self.and_guard(old_g, (ok, true));
        let st = self.push_g(Op::Store { buf, idx, val }); self.stores.push(st); self.cur_guard = old_g; }
    fn zero_like(&mut self, v: &Val) -> Val {
        match v {
            Val::Scalar(_, ty) => Val::Scalar(self.prog.push(Op::Const(0)), *ty),
            Val::Opt { payload, .. } => { let z = self.prog.push(Op::Const(0)); Val::Opt { is_some: z, payload: Box::new(self.zero_like(payload)) } }
            Val::Tuple(xs) => Val::Tuple(xs.iter().map(|x| self.zero_like(x)).collect()),
            Val::Struct(n, fs) => Val::Struct(n.clone(), fs.iter().map(|(k, x)| (k.clone(), self.zero_like(x))).collect()),
            Val::Buf(b) => Val::Buf(*b), Val::Opaque => Val::Opaque, } }
    fn merge_opt_node(&mut self, cond: usize, a: Option<usize>, b: Option<usize>, guard: Option<(usize, bool)>) -> Option<Option<usize>> {
        match (a, b) {
            (Some(x), Some(y)) => Some(Some(if x == y { x } else { self.prog.push_guarded(Op::Select { cond, t_val: x, f_val: y }, guard) })),
            (None, None) => Some(None), _ => None, } }
    fn merge_val(&mut self, cond: usize, tv: Val, fv: Val, guard: Option<(usize, bool)>) -> Option<Val> {
        match (tv, fv) {
            (Val::Scalar(a, ta), Val::Scalar(b, tb)) => Some(Val::Scalar(if a == b { a } else { self.prog.push_guarded(Op::Select { cond, t_val: a, f_val: b }, guard) }, ta.or(tb))),
            (Val::Opt { is_some: sa, payload: pa }, Val::Opt { is_some: sb, payload: pb }) => {
                let is_some = if sa == sb { sa } else { self.prog.push_guarded(Op::Select { cond, t_val: sa, f_val: sb }, guard) };
                let payload = if self.const_of(sa) == Some(0) { *pb } else if self.const_of(sb) == Some(0) { *pa } else { self.merge_val(cond, *pa, *pb, guard)? };
                Some(Val::Opt { is_some, payload: Box::new(payload) }) }
            (Val::Tuple(va), Val::Tuple(vb)) if va.len() == vb.len() => Some(Val::Tuple(va.into_iter().zip(vb).map(|(a, b)| self.merge_val(cond, a, b, guard)).collect::<Option<Vec<_>>>()?)),
            (Val::Struct(na, fa), Val::Struct(nb, fb)) if na == nb && fa.len() == fb.len() => { Some(Val::Struct(na, fa.into_iter().zip(fb).map(|((ka, va), (_, vb))| Some((ka, self.merge_val(cond, va, vb, guard)?))).collect::<Option<Vec<_>>>()?)) }
            (Val::Buf(a), Val::Buf(b)) if a.id == b.id && a.mutable == b.mutable && a.elem_ty == b.elem_ty && a.base_const == b.base_const && a.len_const == b.len_const && a.root_len == b.root_len => {
                Some(Val::Buf(BufBind { base_node: self.merge_opt_node(cond, a.base_node, b.base_node, guard)?, len_node: self.merge_opt_node(cond, a.len_node, b.len_node, guard)?, ..a })) }
            (Val::Opaque, Val::Opaque) => Some(Val::Opaque), _ => None, } }
    fn flatten_val(v: &Val, out: &mut Vec<usize>) {
        match v {
            Val::Scalar(id, _) => out.push(*id), Val::Opt { is_some, payload } => { out.push(*is_some); Self::flatten_val(payload, out); }
            Val::Tuple(xs) => for x in xs { Self::flatten_val(x, out); }, Val::Struct(_, fs) => for (_, x) in fs { Self::flatten_val(x, out); }, Val::Buf(_) | Val::Opaque => {} } }
    fn emit_range_check(&mut self, val: usize, ty: ScalarTy) {
        if !ty.is_narrow() { return; }
        let (lo, hi) = ty.bounds(); if !ty.is_unsigned() { let lok = self.prog.push(Op::Const(lo)); let ge = self.push_g(Op::Cmp(CmpKind::Ge, val, lok)); self.push_g(Op::PanicIfZero(ge, 4)); }
        let hik = self.prog.push(Op::Const(hi)); let le = self.push_g(Op::Cmp(CmpKind::Le, val, hik)); self.push_g(Op::PanicIfZero(le, 4)); }
    fn emit_nonneg_check(&mut self, val: usize, ty: Option<ScalarTy>) {
        if ty.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { return; }
        let z = self.prog.push(Op::Const(0)); let ge = self.push_g(Op::Cmp(CmpKind::Ge, val, z)); self.push_g(Op::PanicIfZero(ge, 2)); }
    fn buf_index(&mut self, bb: BufBind, idx: usize) -> usize {
        let checked = if let Some(ln) = bb.len_node { self.push_g(Op::DynBoundsCheck(idx, ln)) }
            else if bb.base_const == 0 && bb.base_node.is_none() && self.prog.bufs.get(usize::from(bb.id)).is_some_and(|b| b.len == bb.len_const) { return idx; }
            else { self.push_g(Op::BoundsCheck { idx, limit: bb.len_const }) };
        let ri = if let Some(bn) = bb.base_node { self.push_g(Op::Add(bn, checked)) }
            else if bb.base_const > 0 { let off = self.prog.push(Op::Const(bb.base_const as i64)); self.push_g(Op::Add(checked, off)) } else { checked };
        if let Some(rl) = bb.root_len { if bb.len_node != Some(rl) { return self.push_g(Op::DynBoundsCheck(ri, rl)); } }
        ri }
    fn buf_frame(bb: BufBind) -> BufFrame { (bb.id, bb.base_const, bb.base_node) }
    fn is_proven_cb_frame(&self, f: BufFrame, idx: usize, len_n: Option<usize>, depth: u8) -> bool {
        if self.utf8.str_ascii.contains(&f) || self.utf8.str_ascii.contains(&(f.0, 0, None))
            || len_n == Some(idx) || self.const_of(idx) == Some(0) || self.utf8.char_bounds.contains(&(f, idx)) { return true; }
        if let Some(k) = self.const_of(idx) { if self.utf8.starts_lens.contains(&(f, k)) { return true; } }
        if depth >= 3 { return false; }
        match self.prog.nodes.get(idx).copied() {
            Some(Op::Select { t_val, f_val, .. }) => self.is_proven_cb_frame(f, t_val, len_n, depth + 1) && self.is_proven_cb_frame(f, f_val, len_n, depth + 1),
            Some(Op::Add(a, b)) => {
                let (ka, kb) = (self.const_of(a), self.const_of(b));
                if (kb == Some(1) && self.utf8.ascii_at_idx.contains(&(f, a)))
                    || (ka == Some(1) && self.utf8.ascii_at_idx.contains(&(f, b)))
                    || kb.is_some_and(|k| self.utf8.find_lits.get(&(f, a)) == Some(&k))
                    || ka.is_some_and(|k| self.utf8.find_lits.get(&(f, b)) == Some(&k))
                    || self.utf8.find_dyn.get(&(f, a)) == Some(&b)
                    || self.utf8.find_dyn.get(&(f, b)) == Some(&a) { return true; }
                if f.1 == 0 && f.2.is_none() {
                    for (base, rel) in [(a, b), (b, a)] {
                        if self.is_proven_cb_frame(f, base, len_n, depth + 1)
                            && (self.is_proven_cb_frame((f.0, 0, Some(base)), rel, None, depth + 1)
                                || self.const_of(base).filter(|&k| k >= 0).is_some_and(|k| self.is_proven_cb_frame((f.0, k as usize, None), rel, None, depth + 1))) { return true; } }
                    if let Some((sum_n, kv)) = kb.map(|k| (a, k)).or_else(|| ka.map(|k| (b, k))) {
                        if let Some(Op::Add(x, y)) = self.prog.nodes.get(sum_n).copied() {
                            for (base, pos) in [(x, y), (y, x)] {
                                if self.is_proven_cb_frame(f, base, len_n, depth + 1)
                                    && (self.utf8.find_lits.get(&((f.0, 0, Some(base)), pos)) == Some(&kv)
                                        || self.const_of(base).filter(|&k| k >= 0).is_some_and(|k| self.utf8.find_lits.get(&((f.0, k as usize, None), pos)) == Some(&kv))) { return true; } }
                        } } }
                false }
            Some(Op::Sub(a, b)) if len_n == Some(a) => self.const_of(b).is_some_and(|k| self.utf8.ends_lens.contains(&(f, k))),
            _ => false, } }
    fn is_proven_cb(&self, bb: BufBind, idx: usize, len_n: usize, depth: u8) -> bool { self.is_proven_cb_frame(Self::buf_frame(bb), idx, Some(len_n), depth) }
    fn apply_utf8_guard(&mut self, cond: usize, pol: bool, depth: u8) {
        if depth >= 4 { return; }
        if pol {
            if let Some(&bid) = self.utf8.ascii_preds.get(&cond) { self.utf8.str_ascii.insert(bid); }
            if let Some(&(bid, ix)) = self.utf8.cb_preds.get(&cond) { self.utf8.char_bounds.insert((bid, ix)); }
            if let Some(&(bid, k)) = self.utf8.starts_preds.get(&cond) { self.utf8.starts_lens.insert((bid, k)); }
            if let Some(&(bid, k)) = self.utf8.ends_preds.get(&cond) { self.utf8.ends_lens.insert((bid, k)); }
            if let Some(&(bid, ix)) = self.utf8.ascii_byte_preds.get(&cond) { self.utf8.char_bounds.insert((bid, ix)); self.utf8.ascii_at_idx.insert((bid, ix)); } }
        match self.prog.nodes.get(cond).copied() {
            Some(Op::Cmp(CmpKind::Eq, x, y)) if self.const_of(y) == Some(0) => self.apply_utf8_guard(x, !pol, depth + 1),
            Some(Op::Cmp(CmpKind::Eq, x, y)) if self.const_of(x) == Some(0) => self.apply_utf8_guard(y, !pol, depth + 1),
            Some(Op::Select { cond: a, t_val: b, f_val }) if pol && self.const_of(f_val) == Some(0) => { self.apply_utf8_guard(a, true, depth + 1); self.apply_utf8_guard(b, true, depth + 1); }
            Some(Op::Select { cond: a, t_val, f_val: b }) if !pol && self.const_of(t_val) == Some(1) => { self.apply_utf8_guard(a, false, depth + 1); self.apply_utf8_guard(b, false, depth + 1); }
            Some(Op::Cmp(k, a, b)) if pol => {
                let ascii_hit = match (self.utf8.byte_loads.get(&a).copied(), self.const_of(b), self.utf8.byte_loads.get(&b).copied(), self.const_of(a)) {
                    (Some(p), Some(v), _, _) if (k == CmpKind::Eq && (0..128).contains(&v)) || (k == CmpKind::Lt && v <= 128) || (k == CmpKind::Le && v < 128) => Some(p),
                    (_, _, Some(p), Some(v)) if (k == CmpKind::Eq && (0..128).contains(&v)) || (k == CmpKind::Gt && v <= 128) || (k == CmpKind::Ge && v < 128) => Some(p),
                    _ => None, };
                if let Some((bid, ix)) = ascii_hit { self.utf8.char_bounds.insert((bid, ix)); self.utf8.ascii_at_idx.insert((bid, ix)); } }
            _ => {} } }
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
            self.push_g(Op::PanicIfZero(le1, 2)); self.push_g(Op::PanicIfZero(le2, 2));
            if bb.is_str && (!self.is_proven_cb(bb, a_id, len_n, 0) || !self.is_proven_cb(bb, b_id, len_n, 0)) {
                let z = self.prog.push(Op::Const(0)); self.push_g(Op::PanicIfZero(z, 5)); }
            None
        }; let old_g = self.cur_guard; if let Some(ok) = ok_opt { self.cur_guard = self.and_guard(old_g, (ok, true)); }
        let (sub_bc, sub_bn, sub_lc, sub_ln) = match (self.const_of(a_id), self.const_of(b_id), bb.base_node, bb.len_node) {
            (Some(ac), Some(bc), None, None) if ac >= 0 && bc >= ac => (bb.base_const + ac as usize, None, (bc - ac) as usize, None),
            _ => {
                let bn = match (bb.base_node, bb.base_const, self.const_of(a_id)) {
                    (Some(b0), _, Some(0)) => Some(b0), (Some(b0), _, _) => Some(self.push_g(Op::Add(b0, a_id))), (None, 0, Some(0)) => None, (None, 0, _) => Some(a_id),
                    (None, bc, _) => { let k = self.prog.push(Op::Const(bc as i64)); Some(self.push_g(Op::Add(k, a_id))) } };
                (0, bn, bb.len_const, Some(self.push_g(Op::Sub(b_id, a_id)))) }
        }; self.cur_guard = old_g;
        Some((ok_opt, BufBind { id: bb.id, base_const: sub_bc, base_node: sub_bn, len_const: sub_lc, len_node: sub_ln, root_len: bb.root_len.or(bb.len_node), mutable, elem_ty: bb.elem_ty, is_str: bb.is_str })) }
    fn apply_binop(&mut self, op: &str, l: usize, lt: Option<ScalarTy>, r: usize, rt: Option<ScalarTy>) -> Option<Val> {
        let ty = lt.or(rt);
        match op {
            "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                let k = match op { "==" => CmpKind::Eq, "!=" => CmpKind::Ne, "<" => CmpKind::Lt, "<=" => CmpKind::Le, ">" => CmpKind::Gt, _ => CmpKind::Ge };
                Some(Val::Scalar(self.push_g(Op::Cmp(k, l, r)), Some(ScalarTy::Bool))) }
            "|" | "^" | "&" => Some(Val::Scalar(self.push_g(match op { "|" => Op::BitOr(l, r), "^" => Op::BitXor(l, r), _ => Op::BitAnd(l, r) }), ty)),
            "+" | "*" => {
                let res = self.push_g(if op == "+" { Op::Add(l, r) } else { Op::Mul(l, r) });
                if let Some(t) = ty.filter(|t| t.is_narrow()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty)) }
            "-" => {
                if matches!(ty, Some(ScalarTy::U64 | ScalarTy::Usize)) && self.const_of(r) == Some(1) {
                    match self.prog.nodes.get(l).copied() {
                        Some(Op::Shl(a, s)) if self.const_of(a) == Some(1) && s < 64 => { let mx = self.prog.push(Op::Const(i64::MAX)); return Some(Val::Scalar(self.push_g(Op::Shr(mx, 63 - s)), ty)); }
                        Some(Op::ShlVar(a, s)) if self.const_of(a) == Some(1) => { let (c63, mx) = (self.prog.push(Op::Const(63)), self.prog.push(Op::Const(i64::MAX))); let inv = self.push_g(Op::Sub(c63, s)); return Some(Val::Scalar(self.push_g(Op::ShrVar(mx, inv)), ty)); }
                        _ => {} } }
                if ty.is_some_and(ScalarTy::is_unsigned) { let ge = self.push_g(Op::Cmp(CmpKind::Ge, l, r)); self.push_g(Op::PanicIfZero(ge, 4)); }
                let res = self.push_g(Op::Sub(l, r));
                if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty)) }
            "/" | "%" => {
                let res = self.push_g(if op == "/" { Op::Div(l, r) } else { Op::Rem(l, r) });
                if op == "/" { if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); } } Some(Val::Scalar(res, ty)) }
            "<<" | ">>" => {
                let (shl, bits) = (op == "<<", lt.map_or(64, ScalarTy::bits)); let r_use = if bits < 64 { self.push_g(Op::BoundsCheck { idx: r, limit: bits }) } else { r };
                let mut res = match self.const_of(r) {
                    Some(v) if (0..bits as i64).contains(&v) || (bits == 64 && (0..=255).contains(&v)) => self.push_g(if shl { Op::Shl(l, v as u8) } else { Op::Shr(l, v as u8) }),
                    _ => self.push_g(if shl { Op::ShlVar(l, r_use) } else { Op::ShrVar(l, r_use) }),
                }; if shl { if let Some(t) = lt.filter(|t| t.is_narrow() && t.is_unsigned()) { let m = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, m)); } }
                Some(Val::Scalar(res, lt)) }
            _ => None, } }
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
                lv = Val::Scalar(id, Some(ScalarTy::Bool)); continue; }
            let rv = self.parse_binop(c, p + 1)?; let (r, rt) = scalar_id(&rv)?; lv = self.apply_binop(op, l, lt, r, rt)?; }
        Some(lv) }
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
            }; val = Val::Scalar(nv, Some(dst)); }
        Some(val) }
    fn parse_unary(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        if c.eat_sym("-") {
            if let Some(&Tok::Int(v, ty)) = c.peek() { c.pos += 1; return Some(Val::Scalar(self.prog.push(Op::Const(v.checked_neg()?)), ty)); }
            let rv = self.parse_unary(c)?; let ((r, rty), z) = (scalar_id(&rv)?, self.prog.push(Op::Const(0))); let res = self.push_g(Op::Sub(z, r));
            if let Some(t) = rty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(res, t); }
            return Some(Val::Scalar(res, rty)); }
        if c.eat_sym("!") {
            let rv = self.parse_unary(c)?; let (r, rty) = scalar_id(&rv)?;
            if rty == Some(ScalarTy::Bool) || matches!(self.prog.nodes.get(r), Some(Op::Cmp(..))) {
                let z = self.prog.push(Op::Const(0)); return Some(Val::Scalar(self.push_g(Op::Cmp(CmpKind::Eq, r, z)), Some(ScalarTy::Bool))); }
            let mk = self.prog.push(Op::Const(rty.filter(|t| t.is_narrow() && t.is_unsigned()).map_or(-1, |t| t.bounds().1))); return Some(Val::Scalar(self.push_g(Op::BitXor(r, mk)), rty)); }
        if c.eat_sym("*") { return self.parse_unary(c); }
        if c.eat_sym("&") {
            let is_mut = c.eat_ident("mut");
            return match self.parse_unary(c)? { Val::Buf(bb) => (!is_mut || bb.mutable).then_some(Val::Buf(BufBind { mutable: is_mut, ..bb })), other => Some(other) }; }
        self.parse_postfix(c) }
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
            for (k, &val) in elems.iter().enumerate() { let ki = self.prog.push(Op::Const(k as i64)); let st = self.push_g(Op::Store { buf: id, idx: ki, val }); self.stores.push(st); } id };
        Some(Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: elems.len(), len_node: None, root_len: None, mutable: true, elem_ty: ety, is_str: false })) }
    fn parse_struct_lit(&mut self, name: &str, c: &mut Cursor<'_>) -> Option<Val> {
        let (def, mut map, mut base_fs) = (self.file.structs.get(name)?, BTreeMap::new(), None);
        while !c.eat_sym("}") {
            if c.eat_sym("..") {
                let Val::Struct(bn, bfs) = self.parse_expr(c)? else { return None; };
                if bn != name { return None; } base_fs = Some(bfs); let _ = c.eat_sym(","); if !c.eat_sym("}") { return None; } break; }
            let fname = c.expect_ident()?; let val = if c.eat_sym(":") { self.parse_expr(c)? } else { self.vars.get(&fname)?.clone() }; map.insert(fname, val); let _ = c.eat_sym(","); }
        let mut ordered = Vec::with_capacity(def.fields.len());
        for (fname, fty) in &def.fields {
            let v = map.remove(fname).or_else(|| base_fs.as_ref()?.iter().find(|(k, _)| k == fname).map(|(_, v)| v.clone()))?;
            let fv = match fty { FieldTy::Scalar(st) => Val::Scalar(scalar_id(&v)?.0, Some(*st)), FieldTy::Slice(..) | FieldTy::Str => v, FieldTy::Opaque => Val::Opaque };
            ordered.push((fname.clone(), fv)); }
        Some(Val::Struct(name.to_string(), ordered)) }
    fn parse_range_or_idx(&mut self, c: &mut Cursor<'_>, end_sym: &str) -> Option<RangeOrIdx> {
        if c.eat_sym("..=") { let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((None, Some(scalar_id(&hv)?), true))); }
        if c.eat_sym("..") { if c.eat_sym(end_sym) { return Some(Err((None, None, false))); } let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((None, Some(scalar_id(&hv)?), false))); }
        let fv = self.parse_expr(c)?; let first = scalar_id(&fv)?;
        if c.eat_sym("..=") { let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((Some(first), Some(scalar_id(&hv)?), true))); }
        if c.eat_sym("..") { if c.eat_sym(end_sym) { return Some(Err((Some(first), None, false))); } let hv = self.parse_expr(c)?; return c.eat_sym(end_sym).then_some(Err((Some(first), Some(scalar_id(&hv)?), false))); }
        c.eat_sym(end_sym).then_some(Ok(first)) }
    fn parse_path_expr(&mut self, first: String, c: &mut Cursor<'_>) -> Option<Val> {
        let (mut base_owned, mut sub) = (self.resolve_ty(&first).to_string(), c.expect_ident()?);
        while c.eat_sym("::") {
            if self.is_async && matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); break; }
            base_owned.push_str("::"); base_owned.push_str(&sub); sub = c.expect_ident()?; }
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
                        acc = Some(match acc { Some(a) => self.push_g(Op::BitOr(a, term)), None => term }); }
                    return Some(Val::Scalar(acc?, Some(st))); }
                return None; }
            if (is_opt && sub == "Some") || (is_res && sub == "Ok") { let v = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } return Some(Val::Opt { is_some: self.prog.push(Op::Const(1)), payload: Box::new(v) }); }
            if is_res && sub == "Err" { return self.parse_err_ctor(c); }
            return self.parse_call(&format!("{base_owned}::{sub}"), None, None, c); }
        if let Some(st) = self.file.resolve_scalar(&base_owned) { return Some(Val::Scalar(self.prog.push(Op::Const(st.assoc_const(&sub)?)), Some(st))); }
        if let Some(e) = self.file.enums.get(&base_owned) { return Some(Val::Scalar(self.prog.push(Op::Const(*e.variants.get(&sub)?)), Some(ScalarTy::Usize))); }
        if is_opt && sub == "None" { return Some(self.mk_none()); }
        let (cv, cty) = *self.file.consts.get(&format!("{base_owned}::{sub}"))?;
        Some(Val::Scalar(self.prog.push(Op::Const(cv)), cty)) }
    fn parse_err_ctor(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        let (start, mut d) = (c.pos, 1usize); while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let body = c.toks.get(start..c.pos.saturating_sub(1)).unwrap_or(&[]);
        if body.iter().any(|t| matches!(t, Tok::Sym("/" | "%" | "[" | "<<" | ">>" | "+" | "-" | "*")) || matches!(t, Tok::Ident(w) if w == "unwrap" || w == "expect")) {
            let end = c.pos; c.pos = start; let _ = self.parse_expr(c)?; if c.pos + 1 != end { return None; } c.pos = end; }
        Some(self.mk_none()) }
    fn checked_unsigned_add_sub(&mut self, base: usize, r: usize, is_add: bool) -> (usize, usize) {
        let old_g = self.cur_guard;
        if is_add {
            let mx = self.prog.push(Op::Const(i64::MAX)); let room = self.push_g(Op::Sub(mx, base));
            let ok = self.push_g(Op::Cmp(CmpKind::Le, r, room)); self.cur_guard = self.and_guard(old_g, (ok, true));
            let raw = self.push_g(Op::WrapAdd(base, r)); let s = self.push_g(Op::BitAnd(raw, mx)); self.cur_guard = old_g; (ok, s)
        } else {
            let ok = self.push_g(Op::Cmp(CmpKind::Ge, base, r)); self.cur_guard = self.and_guard(old_g, (ok, true));
            let d = self.push_g(Op::Sub(base, r)); self.cur_guard = old_g; (ok, d) } }
    fn parse_scalar_method(&mut self, base: usize, ty: Option<ScalarTy>, m: &str, c: &mut Cursor<'_>) -> Option<Val> {
        let mut args = Vec::new(); while !c.eat_sym(")") { args.push(self.parse_expr(c)?); let _ = c.eat_sym(","); }
        match m {
            "wrapping_add" | "wrapping_sub" | "wrapping_mul" => {
                let (r, rt) = scalar_id(args.first()?)?; let eff = ty.or(rt);
                let mut res = self.push_g(match m { "wrapping_add" => Op::WrapAdd(base, r), "wrapping_sub" => Op::WrapSub(base, r), _ => Op::WrapMul(base, r) });
                if let Some(t) = eff.filter(|t| t.is_narrow() && t.is_unsigned()) { let mk = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, mk)); }
                Some(Val::Scalar(res, eff)) }
            "wrapping_shl" | "wrapping_shr" => {
                let ((r, _), shl, mask_v) = (scalar_id(args.first()?)?, m == "wrapping_shl", (ty.map_or(64, ScalarTy::bits) - 1) as i64);
                let mut res = if let Some(v) = self.const_of(r) { self.push_g(if shl { Op::Shl(base, (v & mask_v) as u8) } else { Op::Shr(base, (v & mask_v) as u8) }) }
                    else { let mk = self.prog.push(Op::Const(mask_v)); let s = self.push_g(Op::BitAnd(r, mk)); self.push_g(if shl { Op::ShlVar(base, s) } else { Op::ShrVar(base, s) }) };
                if shl { if let Some(t) = ty.filter(|t| t.is_narrow() && t.is_unsigned()) { let mk = self.prog.push(Op::Const(t.bounds().1)); res = self.push_g(Op::BitAnd(res, mk)); } }
                Some(Val::Scalar(res, ty)) }
            "min" | "max" => {
                let (r, rt) = scalar_id(args.first()?)?; let cmp = self.push_g(Op::Cmp(if m == "min" { CmpKind::Lt } else { CmpKind::Gt }, base, r));
                Some(Val::Scalar(self.push_g(Op::Select { cond: cmp, t_val: base, f_val: r }), ty.or(rt))) }
            "saturating_sub" | "saturating_add" => {
                let ((r, rt), is_add) = (scalar_id(args.first()?)?, m == "saturating_add"); let eff = ty.or(rt)?;
                if eff.is_narrow() {
                    let ((lo, hi), raw) = (eff.bounds(), self.push_g(if is_add { Op::Add(base, r) } else { Op::Sub(base, r) }));
                    let (lok, hik) = (self.prog.push(Op::Const(lo)), self.prog.push(Op::Const(hi)));
                    let c1 = self.push_g(Op::Cmp(CmpKind::Lt, raw, lok)); let s1 = self.push_g(Op::Select { cond: c1, t_val: lok, f_val: raw });
                    let c2 = self.push_g(Op::Cmp(CmpKind::Gt, s1, hik)); return Some(Val::Scalar(self.push_g(Op::Select { cond: c2, t_val: hik, f_val: s1 }), Some(eff))); }
                if !eff.is_unsigned() { return None; }
                let (ok, val) = self.checked_unsigned_add_sub(base, r, is_add); let sat = self.prog.push(Op::Const(if is_add { i64::MAX } else { 0 }));
                Some(Val::Scalar(self.push_g(Op::Select { cond: ok, t_val: val, f_val: sat }), Some(eff))) }
            "checked_add" | "checked_sub" | "checked_mul" | "checked_div" | "checked_rem" => {
                let (r, rt) = scalar_id(args.first()?)?; let eff = ty.or(rt)?; let ((lo, hi), old_g) = (eff.bounds(), self.cur_guard);
                let (ok, val) = match m {
                    "checked_add" if eff.is_narrow() => { let s = self.push_g(Op::Add(base, r)); (self.in_bounds(s, lo, hi, true), s) }
                    "checked_add" if eff.is_unsigned() => self.checked_unsigned_add_sub(base, r, true),
                    "checked_sub" if eff.is_unsigned() => self.checked_unsigned_add_sub(base, r, false),
                    "checked_sub" if eff.is_narrow() => { let d = self.push_g(Op::Sub(base, r)); (self.in_bounds(d, lo, hi, true), d) }
                    "checked_mul" if matches!(eff, ScalarTy::U8 | ScalarTy::U16 | ScalarTy::I8 | ScalarTy::I16 | ScalarTy::I32) => { let p = self.push_g(Op::Mul(base, r)); (self.in_bounds(p, lo, hi, true), p) }
                    "checked_div" | "checked_rem" if eff.is_unsigned() => { let z = self.prog.push(Op::Const(0)); let ok = self.push_g(Op::Cmp(CmpKind::Ne, r, z)); self.cur_guard = self.and_guard(old_g, (ok, true)); let q = self.push_g(if m == "checked_div" { Op::Div(base, r) } else { Op::Rem(base, r) }); self.cur_guard = old_g; (ok, q) }
                    _ => return None, };
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(val, Some(eff))) }) }
            "abs" | "unsigned_abs" if args.is_empty() => {
                let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let lt = self.push_g(Op::Cmp(CmpKind::Lt, base, z));
                self.cur_guard = self.and_guard(old_g, (lt, true)); let neg = self.push_g(Op::Sub(z, base));
                if m == "abs" { if let Some(t) = ty.filter(|t| t.is_narrow() && !t.is_unsigned()) { self.emit_range_check(neg, t); } }
                self.cur_guard = old_g;
                let rty = if m == "unsigned_abs" { match ty { Some(ScalarTy::I8) => Some(ScalarTy::U8), Some(ScalarTy::I16) => Some(ScalarTy::U16), Some(ScalarTy::I32) => Some(ScalarTy::U32), Some(ScalarTy::I64) => Some(ScalarTy::U64), _ => Some(ScalarTy::Usize) } } else { ty };
                Some(Val::Scalar(self.push_g(Op::Select { cond: lt, t_val: neg, f_val: base }), rty)) }
            "is_multiple_of" => {
                let ((r, _), z, old_g) = (scalar_id(args.first()?)?, self.prog.push(Op::Const(0)), self.cur_guard);
                let nz = self.push_g(Op::Cmp(CmpKind::Ne, r, z)); self.cur_guard = self.and_guard(old_g, (nz, true));
                let rem = self.push_g(Op::Rem(base, r)); let eq0 = self.push_g(Op::Cmp(CmpKind::Eq, rem, z)); self.cur_guard = old_g; let base0 = self.push_g(Op::Cmp(CmpKind::Eq, base, z));
                Some(Val::Scalar(self.push_g(Op::Select { cond: nz, t_val: eq0, f_val: base0 }), Some(ScalarTy::Bool))) }
            "div_ceil" if ty.is_some_and(ScalarTy::is_unsigned) => {
                let ((r, _), z, one, mx, old_g) = (scalar_id(args.first()?)?, self.prog.push(Op::Const(0)), self.prog.push(Op::Const(1)), self.prog.push(Op::Const(i64::MAX)), self.cur_guard);
                let (q, rem) = (self.push_g(Op::Div(base, r)), self.push_g(Op::Rem(base, r)));
                let has_rem = self.push_g(Op::Cmp(CmpKind::Ne, rem, z)); self.cur_guard = self.and_guard(old_g, (has_rem, true));
                let raw_qp1 = self.push_g(Op::WrapAdd(q, one)); let qp1 = self.push_g(Op::BitAnd(raw_qp1, mx)); self.cur_guard = old_g;
                let res = self.push_g(Op::Select { cond: has_rem, t_val: qp1, f_val: q });
                if let Some(t) = ty.filter(|t| t.is_narrow()) { self.emit_range_check(res, t); } Some(Val::Scalar(res, ty)) }
            "rem_euclid" => {
                let (r, _) = scalar_id(args.first()?)?; let rem = self.push_g(Op::Rem(base, r)); if ty.is_some_and(ScalarTy::is_unsigned) { return Some(Val::Scalar(rem, ty)); }
                let (z, old_g) = (self.prog.push(Op::Const(0)), self.cur_guard); let (neg_r, r_neg) = (self.push_g(Op::Cmp(CmpKind::Lt, rem, z)), self.push_g(Op::Cmp(CmpKind::Lt, r, z)));
                let g_neg = self.and_guard(old_g, (neg_r, true)); self.cur_guard = self.and_guard(g_neg, (r_neg, true)); let sub_v = self.push_g(Op::Sub(rem, r));
                self.cur_guard = self.and_guard(g_neg, (r_neg, false)); let add_v = self.push_g(Op::Add(rem, r));
                self.cur_guard = g_neg; let adj = self.push_g(Op::Select { cond: r_neg, t_val: sub_v, f_val: add_v });
                self.cur_guard = old_g; Some(Val::Scalar(self.push_g(Op::Select { cond: neg_r, t_val: adj, f_val: rem }), ty)) }
            "is_ascii" | "is_ascii_digit" | "is_ascii_alphabetic" | "is_ascii_alphanumeric" | "is_ascii_whitespace" | "is_ascii_hexdigit" if args.is_empty() && ty == Some(ScalarTy::U8) => {
                let rs: &[(i64, i64)] = match m {
                    "is_ascii" => &[(0, 127)], "is_ascii_digit" => &[(48, 57)], "is_ascii_alphabetic" => &[(65, 90), (97, 122)],
                    "is_ascii_alphanumeric" => &[(48, 57), (65, 90), (97, 122)], "is_ascii_hexdigit" => &[(48, 57), (65, 70), (97, 102)],
                    _ => &[(9, 10), (12, 13), (32, 32)],
                }; let (one, mut acc) = (self.prog.push(Op::Const(1)), None);
                for &(lo, hi) in rs { let in_r = self.in_bounds(base, lo, hi, true); acc = Some(match acc { Some(a) => self.push_g(Op::Select { cond: a, t_val: one, f_val: in_r }), None => in_r }); }
                let rid = acc?;
                if let Some(&bl) = self.utf8.byte_loads.get(&base) { self.utf8.ascii_byte_preds.insert(rid, bl); }
                Some(Val::Scalar(rid, Some(ScalarTy::Bool))) }
            _ if ty == Some(ScalarTy::Usize) => {
                let st = self.self_ty.as_deref().filter(|s| self.file.enums.contains_key(*s))?;
                let mut all = vec![Val::Scalar(base, ty)]; all.extend(args); self.inline_call(&format!("{st}::{m}"), &all, &[]) }
            _ => None, } }
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
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(ld, Some(bb.elem_ty))) }) }
            "get" | "get_mut" => {
                let mut_req = m == "get_mut"; if mut_req && !bb.mutable { return None; }
                match self.parse_range_or_idx(c, ")")? {
                    Ok((idx, ity)) => {
                        let ln = self.buf_len_node(bb); let mut ok = self.push_g(Op::Cmp(CmpKind::Lt, idx, ln));
                        if !ity.is_some_and(|t| t.is_unsigned() || t == ScalarTy::Bool) { let z = self.prog.push(Op::Const(0)); let ge0 = self.push_g(Op::Cmp(CmpKind::Ge, idx, z)); ok = self.push_g(Op::Select { cond: ge0, t_val: ok, f_val: z }); }
                        let old_g = self.cur_guard; self.cur_guard = self.and_guard(old_g, (ok, true));
                        let ri = self.buf_index(bb, idx); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri }); self.cur_guard = old_g;
                        if bb.elem_ty == ScalarTy::U8 { self.utf8.byte_loads.insert(ld, (Self::buf_frame(bb), idx)); }
                        Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(ld, Some(bb.elem_ty))) }) }
                    Err((lo, hi, inc)) => { let (ok, sub) = self.make_subslice(bb, lo, hi, inc, true, mut_req)?; Some(Val::Opt { is_some: ok?, payload: Box::new(Val::Buf(sub)) }) } } }
            "split_at" | "split_at_mut" => {
                let mut_req = m == "split_at_mut"; let mv = self.parse_expr(c)?; let mid = scalar_id(&mv)?; if !c.eat_sym(")") { return None; }
                let ((_, left), (_, right)) = (self.make_subslice(bb, None, Some(mid), false, false, mut_req)?, self.make_subslice(bb, Some(mid), None, false, false, mut_req)?);
                Some(Val::Tuple(vec![Val::Buf(left), Val::Buf(right)])) }
            "split_first" => {
                if !c.eat_sym(")") { return None; }
                let (ln, z, one, old_g) = (self.buf_len_node(bb), self.prog.push(Op::Const(0)), self.prog.push(Op::Const(1)), self.cur_guard);
                let ok = self.push_g(Op::Cmp(CmpKind::Gt, ln, z)); self.cur_guard = self.and_guard(old_g, (ok, true));
                let ri = self.buf_index(bb, z); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri });
                let (_, rest) = self.make_subslice(bb, Some((one, Some(ScalarTy::Usize))), None, false, false, false)?; self.cur_guard = old_g;
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Tuple(vec![Val::Scalar(ld, Some(bb.elem_ty)), Val::Buf(rest)])) }) }
            "as_slice" => c.eat_sym(")").then_some(Val::Buf(BufBind { is_str: false, ..bb })),
            "as_bytes" => c.eat_sym(")").then_some(Val::Buf(BufBind { is_str: false, mutable: false, ..bb })),
            "as_str" => c.eat_sym(")").then_some(Val::Buf(BufBind { is_str: true, mutable: false, ..bb })),
            "is_ascii" => {
                if !c.eat_sym(")") { return None; }
                let p = self.prog.add_named_param("__is_ascii", Domain::range(0, 1)); self.utf8.ascii_preds.insert(p, Self::buf_frame(bb));
                Some(Val::Scalar(p, Some(ScalarTy::Bool))) }
            "is_char_boundary" => {
                let idx = scalar_id(&self.parse_expr(c)?)?.0; if !c.eat_sym(")") { return None; }
                let p = self.prog.add_named_param("__is_cb", Domain::range(0, 1)); self.utf8.cb_preds.insert(p, (Self::buf_frame(bb), idx));
                Some(Val::Scalar(p, Some(ScalarTy::Bool))) }
            "starts_with" | "ends_with" => {
                let lit_len = match c.peek() { Some(&Tok::Str(l, true)) => { c.pos += 1; Some(l as i64) } Some(Tok::Sym("@c")) => { c.pos += 1; Some(1) } _ => { let _ = self.parse_expr(c); None } };
                if !c.eat_sym(")") { return None; }
                let raw = self.prog.add_named_param("__str_affix", Domain::range(0, 1));
                let p = if let Some(ll) = lit_len {
                    let (ln, lk, z) = (self.buf_len_node(bb), self.prog.push(Op::Const(ll)), self.prog.push(Op::Const(0)));
                    let ge = self.push_g(Op::Cmp(CmpKind::Ge, ln, lk)); let ok = self.push_g(Op::Select { cond: raw, t_val: ge, f_val: z });
                    if m == "starts_with" { self.utf8.starts_preds.insert(ok, (Self::buf_frame(bb), ll)); } else { self.utf8.ends_preds.insert(ok, (Self::buf_frame(bb), ll)); }
                    ok
                } else { raw };
                Some(Val::Scalar(p, Some(ScalarTy::Bool))) }
            "find" | "rfind" => {
                let (mut lit_len, mut dyn_len) = (None, None);
                match c.peek() {
                    Some(&Tok::Str(l, true)) => { c.pos += 1; lit_len = Some(l as i64); }
                    Some(Tok::Sym("@c")) => { c.pos += 1; lit_len = Some(1); }
                    Some(Tok::Ident(nv)) if matches!(c.peek_at(1), Some(Tok::Sym(")"))) => {
                        if let Some(&Val::Buf(nb)) = self.vars.get(nv) { dyn_len = Some(self.buf_len_node(nb)); }
                        c.pos += 1; }
                    _ => { let mut d = 1usize; while let Some(t) = c.peek() { match t { Tok::Sym("(") => { d += 1; c.pos += 1; } Tok::Sym(")") => { d -= 1; if d == 0 { break; } c.pos += 1; } _ => c.pos += 1 } } } }
                if !c.eat_sym(")") { return None; }
                let (ln, raw_ok, z, fr) = (self.buf_len_node(bb), self.prog.add_named_param("__find_ok", Domain::range(0, 1)), self.prog.push(Op::Const(0)), Self::buf_frame(bb));
                let pos = self.prog.add_named_param("__find_pos", Domain::range(0, MAX_SYM_SLICE_LEN as i64));
                let lim = if let Some(ll) = lit_len {
                    let lk = self.prog.push(Op::Const(ll)); let end = self.push_g(Op::Add(pos, lk)); self.utf8.find_lits.insert((fr, pos), ll); self.push_g(Op::Cmp(CmpKind::Le, end, ln))
                } else if let Some(nl) = dyn_len {
                    let end = self.push_g(Op::Add(pos, nl)); self.utf8.find_dyn.insert((fr, pos), nl); self.push_g(Op::Cmp(CmpKind::Le, end, ln))
                } else { self.push_g(Op::Cmp(CmpKind::Le, pos, ln)) }; let ok = self.push_g(Op::Select { cond: raw_ok, t_val: lim, f_val: z }); self.utf8.char_bounds.insert((fr, pos));
                Some(Val::Opt { is_some: ok, payload: Box::new(Val::Scalar(pos, Some(ScalarTy::Usize))) }) }
            "trim" | "trim_start" | "trim_end" => c.eat_sym(")").then_some(Val::Buf(bb)),
            _ => None, } }
    fn parse_opt_method(&mut self, is_some: usize, payload: Val, m: &str, c: &mut Cursor<'_>) -> Option<Val> {
        match m {
            "is_some" | "is_ok" => c.eat_sym(")").then_some(Val::Scalar(is_some, Some(ScalarTy::Bool))),
            "is_none" | "is_err" => { if !c.eat_sym(")") { return None; } let z = self.prog.push(Op::Const(0)); Some(Val::Scalar(self.push_g(Op::Cmp(CmpKind::Eq, is_some, z)), Some(ScalarTy::Bool))) }
            "copied" | "cloned" => c.eat_sym(")").then_some(Val::Opt { is_some, payload: Box::new(payload) }),
            "unwrap" | "expect" => { let mut d = 1usize; while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } } self.push_g(Op::PanicIfZero(is_some, 1)); Some(payload) }
            "unwrap_or" => { let def = self.parse_expr(c)?; if !c.eat_sym(")") { return None; } self.merge_val(is_some, payload, def, self.cur_guard) }
            "unwrap_or_default" => { if !c.eat_sym(")") { return None; } let def = self.zero_like(&payload); self.merge_val(is_some, payload, def, self.cur_guard) }
            "ok_or" => { let _ = self.parse_err_ctor(c)?; Some(Val::Opt { is_some, payload: Box::new(payload) }) } _ => None,
        } }
    fn is_await_next(c: &Cursor<'_>) -> bool { matches!(c.peek(), Some(Tok::Sym("."))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if w == "await") }
    fn peek_mut_target(&self, c: &Cursor<'_>) -> MutTarget {
        if matches!(c.peek(), Some(Tok::Sym("&"))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if w == "mut") {
            let off = 2 + usize::from(matches!(c.peek_at(2), Some(Tok::Sym("*"))));
            if let Some(Tok::Ident(nm)) = c.peek_at(off) {
                if matches!(c.peek_at(off + 1), Some(Tok::Sym("," | ")"))) { return Some((nm.clone(), None)); }
                if matches!(c.peek_at(off + 1), Some(Tok::Sym("."))) { if let (Some(Tok::Ident(f)), Some(Tok::Sym("," | ")"))) = (c.peek_at(off + 2), c.peek_at(off + 3)) { return Some((nm.clone(), Some(f.clone()))); } } }
        } else if let Some(Tok::Ident(nm)) = c.peek() { if self.mut_refs.contains(nm) && matches!(c.peek_at(1), Some(Tok::Sym("," | ")"))) { return Some((nm.clone(), None)); } }
        None }
    fn write_mut_target(&mut self, vname: &str, fld: Option<&str>, new_val: Val) {
        if let Some(f) = fld {
            if let Some(Val::Struct(sn, mut fs)) = self.vars.get(vname).cloned() { if let Some((_, fv)) = fs.iter_mut().find(|(k, _)| k == f) { *fv = new_val; } self.vars.insert(vname.to_string(), Val::Struct(sn, fs)); }
        } else { self.vars.insert(vname.to_string(), new_val); } }
    fn havoc_buf(&mut self, bb: BufBind) {
        let hv = self.prog.add_named_param("__havoc_buf", bb.elem_ty.domain());
        if bb.len_node.is_none() && bb.len_const <= 64 {
            for k in 0..bb.len_const { let ki = self.prog.push(Op::Const(k as i64)); let ri = self.buf_index(bb, ki); let st = self.push_g(Op::Store { buf: bb.id, idx: ri, val: hv }); self.stores.push(st); }
            return; }
        if let (Some(ln), Some(rlen)) = (bb.len_node, self.prog.bufs.get(usize::from(bb.id)).map(|b| b.len).filter(|&l| l <= 64)) {
            let lo = bb.base_node.unwrap_or_else(|| self.prog.push(Op::Const(bb.base_const as i64))); let hi = self.push_g(Op::Add(lo, ln));
            for k in 0..rlen { let ki = self.prog.push(Op::Const(k as i64)); self.store_guarded(bb.id, ki, hv, lo, hi); }
            return; }
        let mut seen = Vec::new();
        for &op in &self.prog.nodes { if let Op::Store { buf, idx, .. } = op { if buf == bb.id && !seen.contains(&idx) { seen.push(idx); if seen.len() >= 8 { break; } } } }
        let (rln, z) = (bb.root_len.or(bb.len_node).unwrap_or_else(|| self.prog.push(Op::Const(bb.len_const as i64))), self.prog.push(Op::Const(0)));
        for idx in seen { self.store_guarded(bb.id, idx, hv, z, rln); } }
    fn havoc_val(&mut self, v: &Val) -> Val {
        match v {
            Val::Scalar(_, ty) => Val::Scalar(self.prog.add_named_param("__havoc", ty.map_or_else(Domain::top, ScalarTy::domain)), *ty),
            Val::Struct(sn, fs) => Val::Struct(sn.clone(), fs.iter().map(|(k, fv)| (k.clone(), self.havoc_val(fv))).collect()),
            Val::Opt { payload, .. } => Val::Opt { is_some: self.prog.add_named_param("__havoc_ok", Domain::range(0, 1)), payload: Box::new(self.havoc_val(payload)) },
            Val::Tuple(xs) => Val::Tuple(xs.iter().map(|x| self.havoc_val(x)).collect()),
            Val::Buf(bb) => { if bb.mutable { self.havoc_buf(*bb); } Val::Buf(*bb) } Val::Opaque => Val::Opaque, } }
    fn havoc_mut_args(&mut self, targets: &[MutTarget], args: &[Val]) {
        let mut done_bufs = BTreeSet::new();
        for (tgt, arg) in targets.iter().zip(args) {
            if let Some((vname, fld)) = tgt {
                if let Some(cur) = self.vars.get(vname).cloned() {
                    if let Some(f) = fld {
                        if let Val::Struct(sn, mut fs) = cur { if let Some((_, fv)) = fs.iter_mut().find(|(k, _)| k == f) { *fv = self.havoc_val(fv); } self.vars.insert(vname.clone(), Val::Struct(sn, fs)); }
                    } else { if let Val::Buf(bb) = cur { done_bufs.insert(bb.id); } let hv = self.havoc_val(&cur); self.vars.insert(vname.clone(), hv); }
                    continue; } }
            if let Val::Buf(bb) = arg { if bb.mutable && done_bufs.insert(bb.id) { self.havoc_buf(*bb); } } } }
    fn parse_postfix(&mut self, c: &mut Cursor<'_>) -> Option<Val> {
        let mut base_var: Option<String> = None;
        let mut base = match c.peek()? {
            &Tok::Int(v, ty) => { c.pos += 1; Val::Scalar(self.prog.push(Op::Const(v)), ty) }
            &Tok::Str(slen, is_ascii) => {
                c.pos += 1;
                let reg = self.alloc_region(); let bid = self.prog.add_buf(format!("__str_{reg}"), slen.max(1), false, reg, 0, Domain::range(0, if is_ascii { 127 } else { 255 }));
                if is_ascii { self.utf8.str_ascii.insert((bid, 0, None)); }
                Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: slen, len_node: None, root_len: None, mutable: false, elem_ty: ScalarTy::U8, is_str: true }) }
            Tok::Sym("(") => {
                c.pos += 1;
                if c.eat_sym(")") { Val::Tuple(Vec::new()) } else {
                    let first = self.parse_expr(c)?;
                    if c.eat_sym(",") { let mut xs = vec![first]; while !c.eat_sym(")") { xs.push(self.parse_expr(c)?); let _ = c.eat_sym(","); } Val::Tuple(xs) }
                    else { if !c.eat_sym(")") { return None; } first } } }
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
                Val::Scalar(pc.unwrap_or_else(|| self.prog.push(Op::Const(1))), Some(ScalarTy::Bool)) }
            Tok::Ident(kw) if matches!(kw.as_str(), "panic" | "unreachable" | "todo" | "unimplemented") && matches!(c.peek_at(1), Some(Tok::Sym("!"))) => {
                c.pos += 2;
                match c.peek() { Some(Tok::Sym("(")) => c.skip_balanced("(", ")"), Some(Tok::Sym("[")) => c.skip_balanced("[", "]"), Some(Tok::Sym("{")) => c.skip_balanced("{", "}"), _ => return None }
                let z = self.prog.push(Op::Const(0)); self.push_g(Op::PanicIfZero(z, 1)); Val::Scalar(z, None) }
            Tok::Ident(nm) => {
                let nm = nm.clone(); c.pos += 1;
                if c.eat_sym("::") { self.parse_path_expr(nm, c)? }
                else if !self.no_struct_lit && matches!(c.peek(), Some(Tok::Sym("{"))) && self.file.structs.contains_key(self.resolve_ty(&nm)) { c.pos += 1; let rn = self.resolve_ty(&nm).to_string(); self.parse_struct_lit(&rn, c)? }
                else if !self.no_struct_lit && self.is_async && matches!(c.peek(), Some(Tok::Sym("{"))) { let p0 = c.pos; c.skip_balanced("{", "}"); if Self::is_await_next(c) { Val::Opaque } else { c.pos = p0; return None; } }
                else if c.eat_sym("(") { self.parse_call(&nm, None, None, c)? }
                else if let Some(v) = self.vars.get(&nm) { base_var = Some(nm); v.clone() }
                else if let Some(&(cv, cty)) = self.file.consts.get(&nm) { Val::Scalar(self.prog.push(Op::Const(cv)), cty) } else { return None; } }
            _ => return None, };
        loop {
            if c.eat_sym("[") {
                base_var = None; let Val::Buf(bb) = base else { return None; };
                base = match self.parse_range_or_idx(c, "]")? {
                    Ok((idx, _)) => {
                        let ri = self.buf_index(bb, idx); let ld = self.push_g(Op::Load { buf: bb.id, idx: ri });
                        if bb.elem_ty == ScalarTy::U8 { self.utf8.byte_loads.insert(ld, (Self::buf_frame(bb), idx)); }
                        Val::Scalar(ld, Some(bb.elem_ty)) }
                    Err((lo, hi, inc)) => Val::Buf(self.make_subslice(bb, lo, hi, inc, false, bb.mutable)?.1), };
            } else if c.eat_sym(".") {
                if let Some(&Tok::Int(ti, None)) = c.peek() { c.pos += 1; base_var = None; let Val::Tuple(ref xs) = base else { return None; }; base = xs.get(usize::try_from(ti).ok()?)?.clone(); continue; }
                if c.eat_ident("await") {
                    if !self.is_async { return None; } base_var = None;
                    if matches!(base, Val::Opaque) {
                        let opt_next = matches!(c.peek(), Some(Tok::Sym("?"))) || (matches!(c.peek(), Some(Tok::Sym("."))) && matches!(c.peek_at(1), Some(Tok::Ident(w)) if matches!(w.as_str(), "unwrap" | "expect" | "unwrap_or" | "unwrap_or_default" | "is_ok" | "is_err" | "is_some" | "is_none" | "ok_or" | "copied" | "cloned")));
                        base = if opt_next { Val::Opt { is_some: self.prog.add_named_param("__await_ok", Domain::range(0, 1)), payload: Box::new(Val::Scalar(self.prog.add_named_param("__await_val", Domain::range(0, MAX_SYM_SLICE_LEN as i64)), None)) } }
                            else { Val::Scalar(self.prog.add_named_param("__await_val", Domain::top()), None) }; }
                    continue; }
                let m = c.expect_ident()?;
                if c.eat_sym("(") {
                    let (arg_pos, recv_t, saved) = (c.pos, base_var.take().map(|n| (n, None)), self.is_async.then(|| (self.prog.clone(), self.stores.len(), self.next_region, self.inlined_fns.clone())));
                    let known = match base.clone() {
                        Val::Scalar(id, ty) => self.parse_scalar_method(id, ty, &m, c), Val::Buf(bb) => self.parse_buf_method(bb, &m, c),
                        Val::Opt { is_some, payload } => self.parse_opt_method(is_some, *payload, &m, c),
                        Val::Struct(ref sn, _) => self.parse_call(&format!("{sn}::{m}"), Some(base.clone()), recv_t.clone(), c),
                        Val::Opaque => self.parse_call(&m, Some(Val::Opaque), None, c), Val::Tuple(_) => None, };
                    base = match known {
                        Some(v) => v,
                        None if self.is_async && !matches!(base, Val::Opaque | Val::Struct(..)) => {
                            if let Some((sp, sl, nr, inf)) = saved { (self.prog, self.next_region, *self.inlined_fns) = (sp, nr, inf); self.stores.truncate(sl); }
                            c.pos = arg_pos; self.parse_call(&m, Some(base), recv_t, c)? }
                        None => return None, };
                } else { base_var = None; base = match base { Val::Struct(_, ref fs) => fs.iter().find(|(k, _)| k == &m)?.1.clone(), Val::Opaque => Val::Opaque, _ => return None }; }
            } else if c.eat_sym("?") {
                base_var = None; if !self.returns_opt { return None; } let Val::Opt { is_some, payload } = base else { return None; }; let not_some = self.mk_bool(is_some, false);
                let gfail = match self.cur_guard { Some((g, p)) => { let (gb, z) = (self.mk_bool(g, p), self.prog.push(Op::Const(0))); self.prog.push(Op::Select { cond: gb, t_val: not_some, f_val: z }) } None => not_some };
                let none_v = self.mk_none(); self.early_rets.push((gfail, none_v)); self.cur_guard = self.and_guard(self.cur_guard, (is_some, true)); base = *payload;
            } else { break; } }
        Some(base) }
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
                    self.havoc_mut_args(&targets, &args); return Some(Val::Opaque); }
                None }
        } }
    fn inline_call(&mut self, name: &str, args: &[Val], mut_targets: &[MutTarget]) -> Option<Val> {
        if self.depth >= 4 { return None; }
        let item = self.file.fns.iter().find(|f| f.name == name)?; if item.is_unsafe { return None; }
        let bufs: Vec<BufBind> = args.iter().filter_map(|a| if let Val::Buf(b) = a { Some(*b) } else { None }).collect();
        for (i, a) in bufs.iter().enumerate() {
            for b in bufs.get(i + 1..).unwrap_or(&[]) {
                if a.id == b.id && (a.mutable || b.mutable) && a.base_node.is_none() && b.base_node.is_none() && a.base_const < b.base_const + b.len_const && b.base_const < a.base_const + a.len_const {
                    if let Some(r) = self.prog.bufs.get(usize::from(a.id)).cloned() { self.prog.add_buf(format!("__alias_{name}"), b.len_const.max(1), true, r.region, r.offset + b.base_const, r.elem_domain); } }
            } }
        let mut cc = Cursor { toks: self.toks, pos: item.sig_pos }; let gpos = cc.pos; if !cc.eat_empty_generics() { if !item.is_async { return None; } cc.pos = gpos; cc.skip_angles(); }
        if !cc.eat_sym("(") { return None; }
        let (mut nv, mut ai, mut dm, mut mut_params, mut cmr) = (BTreeMap::new(), 0usize, FnMeta::default(), Vec::new(), BTreeSet::new());
        while !cc.eat_sym(")") {
            while let Some(Tok::Doc(l)) = cc.peek() { parse_doc_meta(l, &mut dm); cc.pos += 1; }
            while matches!(cc.peek(), Some(Tok::Sym("#"))) { let _ = cc.parse_attr(&mut dm); }
            let (is_ref_self, is_mut_self) = (cc.eat_sym("&"), cc.eat_ident("mut"));
            if cc.eat_ident("self") {
                if is_ref_self && is_mut_self { mut_params.push((ai, "self".to_string())); cmr.insert("self".to_string()); }
                nv.insert("self".to_string(), args.get(ai)?.clone()); ai += 1; let _ = cc.eat_sym(","); continue; }
            if is_ref_self { return None; }
            let pname = cc.expect_ident()?; if !cc.eat_sym(":") { return None; }
            if matches!(cc.peek(), Some(Tok::Sym("&"))) && matches!(cc.peek_at(1), Some(Tok::Ident(w)) if w == "mut") { cmr.insert(pname.clone()); if !matches!(cc.peek_at(2), Some(Tok::Sym("["))) { mut_params.push((ai, pname.clone())); } }
            cc.skip_until(",", ")", true); nv.insert(pname, args.get(ai)?.clone()); ai += 1; let _ = cc.eat_sym(","); }
        if ai != args.len() { return None; }
        let mut callee_ret_opt = false;
        if cc.eat_sym("->") {
            let (mut d, mut last_id) = (0usize, "");
            while let Some(t) = cc.peek() {
                match t {
                    Tok::Sym("{") if d == 0 => break, Tok::Ident(w) if d == 0 => { last_id = w.as_str(); cc.pos += 1; }
                    Tok::Sym("<") => { if d == 0 && (last_id == "Option" || last_id == "Result") { callee_ret_opt = true; } d += 1; cc.pos += 1; }
                    Tok::Sym("(" | "[") => { d += 1; cc.pos += 1; } Tok::Sym(")" | "]" | ">") => { d = d.saturating_sub(1); cc.pos += 1; }
                    Tok::Sym(">>") => { d = d.saturating_sub(2); cc.pos += 1; } _ => cc.pos += 1, } }
        } else if cc.eat_ident("where") { cc.skip_until("{", ";", false); }
        let (sv, se, sg, sst, sro, sa, smr, sld, sil) = (std::mem::replace(&mut self.vars, nv), std::mem::take(&mut self.early_rets), self.cur_guard,
            std::mem::replace(&mut self.self_ty, item.self_ty.clone()), std::mem::replace(&mut self.returns_opt, callee_ret_opt),
            std::mem::replace(&mut self.is_async, item.is_async), std::mem::replace(&mut self.mut_refs, cmr),
            std::mem::replace(&mut self.loop_depth, 0), std::mem::replace(&mut self.in_loop, false),
        ); self.depth += 1; let res = self.parse_block(&mut cc); self.depth -= 1;
        let (callee_vars, callee_early) = (std::mem::replace(&mut self.vars, sv), std::mem::replace(&mut self.early_rets, se));
        (self.cur_guard, self.self_ty, self.returns_opt, self.is_async, self.mut_refs, self.loop_depth, self.in_loop) = (sg, sst, sro, sa, smr, sld, sil); let (rets, tail, _) = res?;
        if !mut_params.is_empty() {
            if !callee_early.is_empty() { return None; }
            for (arg_idx, pname) in mut_params {
                let Some(Some((vname, fld))) = mut_targets.get(arg_idx) else { return None; };
                if let Some(nv) = callee_vars.get(&pname) { self.write_mut_target(vname, fld.as_deref(), nv.clone()); } } }
        self.inlined_fns.insert(name.to_string()); let mut val = tail.or_else(|| rets.into_iter().next()).unwrap_or_else(|| Val::Scalar(self.prog.push(Op::Const(0)), None));
        for (cond, ev) in callee_early.into_iter().rev() { val = self.merge_val(cond, ev, val, self.cur_guard)?; }
        Some(val) }
    fn bind_pat(&mut self, c: &mut Cursor<'_>, val: Val) -> Option<()> {
        if c.eat_sym("(") {
            let Val::Tuple(xs) = val else { return None; }; let mut i = 0usize;
            while !c.eat_sym(")") { let _ = c.eat_ident("mut"); let v = xs.get(i)?.clone(); i += 1; self.bind_pat(c, v)?; let _ = c.eat_sym(","); }
            return (i == xs.len()).then_some(()); }
        let _ = c.eat_ident("mut"); let name = c.expect_ident()?;
        if name != "_" { self.vars.insert(name, val); } Some(()) }
    fn match_opt_inner(&mut self, is_some: usize, payload: &Val, c: &mut Cursor<'_>) -> Option<(usize, Option<(String, Val)>)> {
        let _ = c.eat_ident("mut"); let (inner_c, inner_b) = self.parse_match_pat(payload, c)?; if !c.eat_sym(")") { return None; }
        let cond = match inner_c { Some(ic) => { let z = self.prog.push(Op::Const(0)); self.push_g(Op::Select { cond: is_some, t_val: ic, f_val: z }) } None => is_some };
        Some((cond, inner_b)) }
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
        let u_cond = self.utf8.clone(); self.apply_utf8_guard(cond, true, 0);
        if let Some((pat_pos, payload)) = opt_bind { let mut pc = Cursor { toks: self.toks, pos: pat_pos }; self.bind_pat(&mut pc, payload)?; }
        if let Some((k, v)) = opt_var { self.vars.insert(k, v); }
        let (_, t_tail, t_ret) = self.parse_block(c)?; let vars_t = std::mem::replace(&mut self.vars, vars0.clone()); self.utf8 = u_cond.clone();
        let (f_tail, f_ret, vars_f) = if c.eat_ident("else") {
            self.cur_guard = self.and_guard(old_g, (cond, false)); self.apply_utf8_guard(cond, false, 0);
            let res = if c.eat_ident("if") { self.parse_if(c)? } else { let (_, t, r) = self.parse_block(c)?; (t, r) };
            (res.0, res.1, std::mem::replace(&mut self.vars, vars0.clone()))
        } else { (None, false, vars0.clone()) }; self.cur_guard = old_g; self.utf8 = u_cond;
        for (k, v0) in vars0 {
            let (vt, vf) = (vars_t.get(&k).cloned().unwrap_or_else(|| v0.clone()), vars_f.get(&k).cloned().unwrap_or(v0));
            let mv = if t_ret && !f_ret { vf } else if f_ret && !t_ret { vt } else { self.merge_val(cond, vt, vf, old_g)? }; self.vars.insert(k, mv); }
        if t_ret ^ f_ret { self.cur_guard = self.and_guard(old_g, (cond, f_ret)); self.apply_utf8_guard(cond, f_ret, 0); }
        let val = match (t_tail, f_tail, t_ret, f_ret) {
            (Some(tt), Some(ft), false, false) => Some(self.merge_val(cond, tt, ft, old_g)?),
            (Some(tt), _, false, true) => Some(tt), (_, Some(ft), true, false) => Some(ft), _ => None, };
        Some((val, t_ret && f_ret)) }
    fn parse_match_pat(&mut self, scrut: &Val, c: &mut Cursor<'_>) -> Option<PatMatch> {
        let (mut cond, mut bind, mut unconditional): (Option<usize>, Option<(String, Val)>, bool) = (None, None, false);
        loop {
            let piece = match c.peek()? {
                Tok::Ident(s) if s == "_" => { c.pos += 1; unconditional = true; None }
                Tok::Ident(s) if s == "true" || s == "false" => { let (sv, _) = scalar_id(scrut)?; let k = self.prog.push(Op::Const(i64::from(s == "true"))); c.pos += 1; Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                Tok::Ident(s) if s == "None" => { let Val::Opt { is_some, .. } = scrut else { return None; }; c.pos += 1; let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                Tok::Ident(s) if s == "Some" || s == "Ok" => {
                    let Val::Opt { is_some, payload } = scrut else { return None; }; c.pos += 1; if !c.eat_sym("(") { return None; }
                    let (mc, mb) = self.match_opt_inner(*is_some, payload, c)?; if let Some(b) = mb { bind = Some(b); } Some(mc) }
                Tok::Ident(s) if s == "Err" => { let Val::Opt { is_some, .. } = scrut else { return None; }; c.pos += 1; c.skip_balanced("(", ")"); let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                Tok::Ident(s) => {
                    let nm = s.clone(); c.pos += 1;
                    if c.eat_sym("::") {
                        let (sub, base) = (c.expect_ident()?, self.resolve_ty(&nm).to_string());
                        if base == "Option" && sub == "None" { let Val::Opt { is_some, .. } = scrut else { return None; }; let z = self.prog.push(Op::Const(0)); Some(self.push_g(Op::Cmp(CmpKind::Eq, *is_some, z))) }
                        else {
                            let (sv, _) = scalar_id(scrut)?;
                            let cv = self.file.enums.get(&base).and_then(|e| e.variants.get(&sub).copied()).or_else(|| self.file.consts.get(&format!("{base}::{sub}")).map(|(v, _)| *v))?;
                            let k = self.prog.push(Op::Const(cv)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                    } else if let Some(&(cv, _)) = self.file.consts.get(&nm) { let (sv, _) = scalar_id(scrut)?; let k = self.prog.push(Op::Const(cv)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) }
                    else { bind = Some((nm, scrut.clone())); unconditional = true; None } }
                Tok::Sym("-") | Tok::Int(_, _) => {
                    let (sv, _) = scalar_id(scrut)?; let lo = self.file.eval_const_atom(c, self.self_ty.as_deref())?.0;
                    if c.eat_sym("..=") || c.eat_sym("..") {
                        let inc = matches!(c.toks.get(c.pos.saturating_sub(1)), Some(Tok::Sym("..=")));
                        Some(self.in_bounds(sv, lo, self.file.eval_const_atom(c, self.self_ty.as_deref())?.0, inc))
                    } else { let k = self.prog.push(Op::Const(lo)); Some(self.push_g(Op::Cmp(CmpKind::Eq, sv, k))) } }
                _ => return None, };
            cond = if unconditional { None } else { match (cond, piece) { (None, p) => p, (c0, None) => c0, (Some(a), Some(b)) => { let one = self.prog.push(Op::Const(1)); Some(self.push_g(Op::Select { cond: a, t_val: one, f_val: b })) } } };
            if !c.eat_sym("|") { break; } }
        if c.eat_ident("if") {
            let (gc, _) = scalar_id(&self.parse_expr_head(c)?)?;
            cond = Some(match cond { Some(a) => { let z = self.prog.push(Op::Const(0)); self.push_g(Op::Select { cond: a, t_val: gc, f_val: z }) } None => gc }); }
        Some((cond, bind)) }
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
                        (Some(u), None) => u, (None, Some(pc)) => pc, (None, None) => self.prog.push(Op::Const(0)), };
                    for (k, v0) in &vars0 { let mv = self.merge_val(take, arm_vars.get(k).cloned().unwrap_or_else(|| v0.clone()), prev_vars.remove(k).unwrap_or_else(|| v0.clone()), old_g)?; prev_vars.insert(k.clone(), mv); }
                    acc_vars = Some(prev_vars); acc_val = match (val, acc_val) { (Some(v), Some(a)) => Some(self.merge_val(take, v, a, old_g)?), (v, a) => a.or(v) };
                } else { acc_vars = Some(arm_vars); acc_val = val; } }
            if let Some(pc) = pat_c {
                rem_g = self.and_guard(rem_g, (pc, false)); let npc = self.mk_bool(pc, false);
                unmatched = Some(match unmatched { None => npc, Some(u) => { let z = self.prog.push(Op::Const(0)); self.prog.push_guarded(Op::Select { cond: u, t_val: npc, f_val: z }, old_g) } });
            } else { let z = self.prog.push(Op::Const(0)); rem_g = self.and_guard(rem_g, (z, true)); unmatched = Some(z); } }
        self.cur_guard = old_g; let Some(final_vars) = acc_vars else { return Some((None, true)); };
        for (k, v0) in vars0 { self.vars.insert(k.clone(), final_vars.get(&k).cloned().unwrap_or(v0)); }
        Some((acc_val, false)) }
    fn record_return(&mut self, val: Val) { if let Some((g, p)) = self.cur_guard { let gb = self.mk_bool(g, p); self.early_rets.push((gb, val)); } }
    fn parse_assert(&mut self, kind: &str, c: &mut Cursor<'_>) -> Option<()> {
        if !c.eat_sym("!") || !c.eat_sym("(") { return None; }
        let cond = match kind {
            "assert_eq" | "debug_assert_eq" | "assert_ne" | "debug_assert_ne" => {
                let av = self.parse_expr(c)?; if !c.eat_sym(",") { return None; } let bv = self.parse_expr(c)?;
                self.push_g(Op::Cmp(if kind.ends_with("eq") { CmpKind::Eq } else { CmpKind::Ne }, scalar_id(&av)?.0, scalar_id(&bv)?.0)) }
            _ => scalar_id(&self.parse_expr(c)?)?.0,
        }; let mut d = 1usize; while let Some(t) = c.next() { match t { Tok::Sym("(") => d += 1, Tok::Sym(")") => { d -= 1; if d == 0 { break; } } _ => {} } }
        let _ = c.eat_sym(";"); self.push_g(Op::PanicIfZero(cond, 3)); self.cur_guard = self.and_guard(self.cur_guard, (cond, true)); Some(()) }
    fn looks_like_store(&self, c: &Cursor<'_>) -> bool {
        let mut k = c.pos + 1; if !matches!(c.toks.get(k), Some(Tok::Sym("["))) { return false; }
        let mut d = 1usize; k += 1; while k < c.toks.len() && d > 0 { match c.toks.get(k) { Some(Tok::Sym("[")) => d += 1, Some(Tok::Sym("]")) => d -= 1, _ => {} } k += 1; }
        matches!(c.toks.get(k), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^="))) }
    fn looks_like_assign(&self, c: &Cursor<'_>) -> bool {
        let off = usize::from(matches!(c.peek(), Some(Tok::Sym("*"))));
        matches!(c.peek_at(off), Some(Tok::Ident(nm)) if self.vars.contains_key(nm))
            && matches!(c.peek_at(off + 1), Some(Tok::Sym("=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="))) }
    fn parse_let_type_hint(&self, c: &mut Cursor<'_>) -> Option<Option<ScalarTy>> {
        if !c.eat_sym(":") { return Some(None); }
        let in_br = c.eat_sym("["); let hint = if let Some(Tok::Ident(s)) = c.peek() { self.file.resolve_scalar(s) } else { None };
        if in_br { c.skip_until("]", "]", true); let _ = c.eat_sym("]"); } else { c.skip_until("=", ";", true); }
        Some(hint) }
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
            if self.parse_block(c)?.2 { return None; } }
        Some(()) }
    fn parse_compound_rhs(&mut self, op: &str, old: usize, old_ty: Option<ScalarTy>, r: usize, r_ty: Option<ScalarTy>) -> Option<Val> {
        if op == "=" { Some(Val::Scalar(r, old_ty.or(r_ty))) } else { self.apply_binop(op.strip_suffix('=')?, old, old_ty, r, r_ty) } }
    fn scan_loop_mutations(toks: &[Tok], start: usize) -> Option<(LoopMutMap, bool)> {
        if !matches!(toks.get(start), Some(Tok::Sym("{"))) { return None; }
        let (mut i, mut d, mut muts, mut has_break) = (start + 1, 1usize, LoopMutMap::new(), false);
        while i < toks.len() && d > 0 {
            match toks.get(i) {
                Some(Tok::Sym("{")) => d += 1, Some(Tok::Sym("}")) => { d -= 1; if d == 0 { break; } }
                Some(Tok::Ident(w)) if w == "break" => {
                    has_break = true;
                    if !matches!(toks.get(i + 1), Some(Tok::Sym(";" | "}"))) { return None; } }
                Some(Tok::Ident(nm)) => {
                    let prev_dot = i > start + 1 && matches!(toks.get(i - 1), Some(Tok::Sym(".")));
                    if !prev_dot && matches!(toks.get(i + 1), Some(Tok::Sym("."))) {
                        if let (Some(Tok::Ident(f)), Some(Tok::Sym(op))) = (toks.get(i + 2), toks.get(i + 3)) {
                            let bit = match *op { "+=" => 1u8, "-=" => 2u8, "=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" => 4u8, _ => 0 };
                            if bit != 0 { *muts.entry((nm.clone(), Some(f.clone()))).or_insert(0) |= bit; } }
                    } else if !prev_dot {
                        if let Some(Tok::Sym(op)) = toks.get(i + 1) {
                            let bit = match *op { "+=" => 1u8, "-=" => 2u8, "=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" => 4u8, _ => 0 };
                            if bit != 0 { *muts.entry((nm.clone(), None)).or_insert(0) |= bit; } }
                    } }
                _ => {} }
            i += 1; }
        Some((muts, has_break)) }
    fn havoc_loop_vars(&mut self, muts: &LoopMutMap, pre: &LoopPreMap, len_vars: &BTreeSet<String>, sq_doms: &BTreeMap<String, Domain>) -> Option<()> {
        for (key, &bits) in muts {
            let Some(&(pre_id, ty)) = pre.get(key) else { continue; };
            let (dom, eff_ty) = if let Some(&sd) = key.1.is_none().then(|| sq_doms.get(&key.0)).flatten() { (sd, ty) }
                else if key.1.is_none() && ty.is_none() && len_vars.contains(&key.0) { (Domain::range(0, MAX_SYM_SLICE_LEN as i64), Some(ScalarTy::Usize)) }
                else { (match ty { Some(ScalarTy::Usize) => Domain::range(0, MAX_SYM_SLICE_LEN as i64), Some(t) => t.domain(), None => Domain::top() }, ty) };
            let hv = self.prog.add_named_param("__loop_var", dom);
            if bits == 1 { let ge = self.push_g(Op::Cmp(CmpKind::Ge, hv, pre_id)); self.cur_guard = self.and_guard(self.cur_guard, (ge, true)); }
            else if bits == 2 { let le = self.push_g(Op::Cmp(CmpKind::Le, hv, pre_id)); self.cur_guard = self.and_guard(self.cur_guard, (le, true)); }
            self.write_mut_target(&key.0, key.1.as_deref(), Val::Scalar(hv, eff_ty)); }
        Some(()) }
    fn parse_while_or_loop(&mut self, c: &mut Cursor<'_>, is_while: bool) -> Option<()> {
        if !is_while || self.prog.check_reg_budget || self.loop_depth >= 2 { return None; }
        let cond_pos = c.pos; let mut d = 0usize;
        while let Some(t) = c.peek() { match t { Tok::Sym("{") if d == 0 => break, Tok::Sym("(" | "[") => { d += 1; c.pos += 1; } Tok::Sym(")" | "]") => { d = d.saturating_sub(1); c.pos += 1; } _ => c.pos += 1 } }
        let body_pos = c.pos; let (muts, has_break) = Self::scan_loop_mutations(self.toks, body_pos)?; let mut pre = BTreeMap::new();
        for key in muts.keys() {
            let val = match (&key.1, self.vars.get(&key.0)) {
                (None, Some(v)) => Some(v),
                (Some(f), Some(Val::Struct(_, fs))) => fs.iter().find(|(k, _)| k == f).map(|(_, v)| v),
                _ => None, };
            if let Some(v) = val { if let Some(s) = scalar_id(v) { pre.insert(key.clone(), s); } } }
        let cond_toks = self.toks.get(cond_pos..body_pos).unwrap_or(&[]); let (mut len_vars, mut sq_doms) = (BTreeSet::new(), BTreeMap::new());
        if cond_toks.iter().any(|t| matches!(t, Tok::Ident(w) if w == "len")) {
            for (k, &(pid, ty)) in &pre { if k.1.is_none() && ty.is_none() && self.const_of(pid).is_some_and(|v| v >= 0) && cond_toks.iter().any(|t| matches!(t, Tok::Ident(w) if w == &k.0)) { len_vars.insert(k.0.clone()); } } }
        if let [Tok::Ident(dv_n), Tok::Sym("*"), Tok::Ident(d2), Tok::Sym("<=" | "<"), Tok::Ident(vn)] = cond_toks {
            if dv_n == d2 && muts.get(&(dv_n.clone(), None)) == Some(&1) && !muts.contains_key(&(vn.clone(), None)) {
                if let (Some(&(pre_d, dty)), Some((v_id, _))) = (pre.get(&(dv_n.clone(), None)), self.vars.get(vn).and_then(scalar_id)) {
                    let (mut step, mut ok, mut bi, mut bd) = (0i64, true, body_pos.saturating_add(1), 1usize);
                    while let Some(t) = self.toks.get(bi) {
                        match t {
                            Tok::Sym("{") => bd = bd.saturating_add(1), Tok::Sym("}") => { bd = bd.saturating_sub(1); if bd == 0 { break; } }
                            Tok::Ident(nm) if nm == dv_n && matches!(self.toks.get(bi.saturating_add(1)), Some(Tok::Sym("+="))) => {
                                if let Some(&Tok::Int(k, _)) = self.toks.get(bi.saturating_add(2)) { if k > 0 { step = step.saturating_add(k); } else { ok = false; } } else { ok = false; } }
                            _ => {} }
                        bi = bi.saturating_add(1); }
                    if ok && step > 0 {
                        let doms = self.prog.infer_domains(&self.prog.param_domains);
                        let (dv, dd) = (doms.get(v_id).copied().unwrap_or_else(Domain::top), doms.get(pre_d).copied().unwrap_or_else(Domain::top));
                        if dv.lo >= 0 && dv.hi >= 0 && dv.hi <= i64::MAX / 4 && dd.lo >= 0 {
                            let mut hi = (dv.hi as f64).sqrt() as i64; while (hi.saturating_add(1)).saturating_mul(hi.saturating_add(1)) <= dv.hi { hi = hi.saturating_add(1); } while hi.saturating_mul(hi) > dv.hi { hi = hi.saturating_sub(1); } let hi = hi.saturating_add(step);
                            if dd.hi <= hi && match dty { None => true, Some(t) => hi <= t.bounds().1 } { sq_doms.insert(dv_n.clone(), Domain::range(dd.lo, hi)); } }
                    } }
            } }
        let (old_g, old_u, old_in) = (self.cur_guard, self.utf8.clone(), self.in_loop); self.havoc_loop_vars(&muts, &pre, &len_vars, &sq_doms)?;
        {
            let mut cc = Cursor { toks: self.toks, pos: cond_pos }; let cond = scalar_id(&self.parse_expr_head(&mut cc)?)?.0;
            self.cur_guard = self.and_guard(self.cur_guard, (cond, true)); self.apply_utf8_guard(cond, true, 0); }
        self.loop_depth += 1; self.in_loop = true; c.pos = body_pos; let res = self.parse_block(c);
        self.loop_depth -= 1; self.in_loop = old_in; let _ = res?; self.cur_guard = old_g; self.utf8 = old_u; self.havoc_loop_vars(&muts, &pre, &len_vars, &sq_doms)?;
        if is_while && !has_break {
            let mut cc = Cursor { toks: self.toks, pos: cond_pos }; let cond_post = scalar_id(&self.parse_expr_head(&mut cc)?)?.0;
            self.cur_guard = self.and_guard(self.cur_guard, (cond_post, false)); self.apply_utf8_guard(cond_post, false, 0); }
        Some(()) }
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
                    val = Val::Scalar(*id, Some(ht)); }
                if !c.eat_sym(";") { return None; }
                let mut pc = Cursor { toks: self.toks, pos: pat_pos }; self.bind_pat(&mut pc, val)?;
            } else if matches!(c.peek(), Some(Tok::Ident(w)) if matches!(w.as_str(), "assert" | "debug_assert" | "assert_eq" | "debug_assert_eq" | "assert_ne" | "debug_assert_ne")) {
                let kw = c.expect_ident()?; self.parse_assert(&kw, c)?;
            } else if c.eat_ident("if") || c.eat_ident("match") {
                let is_if = matches!(c.toks.get(c.pos.saturating_sub(1)), Some(Tok::Ident(w)) if w == "if"); let (val, all_ret) = if is_if { self.parse_if(c)? } else { self.parse_match(c)? };
                if all_ret { returned = true; }
                if !c.eat_sym(";") && matches!(c.peek(), Some(Tok::Sym("}"))) { if let Some(v) = val { tail = Some(v.clone()); rets.push(v); } }
            } else if c.eat_ident("for") { self.parse_for_loop(c)?; }
            else if c.eat_ident("while") { self.parse_while_or_loop(c, true)?; }
            else if c.eat_ident("loop") { self.parse_while_or_loop(c, false)?; }
            else if self.in_loop && (c.eat_ident("break") || c.eat_ident("continue")) {
                returned = true; let _ = c.eat_sym(";");
            } else if c.eat_ident("return") {
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
                tail = Some(v.clone()); rets.push(v); return c.eat_sym("}").then_some((rets, tail, returned)); } }
        Some((rets, tail, returned)) } }
fn add_struct_params(ctx: &mut LowerCtx<'_>, prefix: &str, tname: &str, mutable: bool) -> Option<(Val, StructFields)> {
    let def = ctx.file.structs.get(tname)?; let has_buf = def.fields.iter().any(|(_, t)| matches!(t, FieldTy::Slice(_, _) | FieldTy::Str));
    let has_opaque = def.fields.iter().any(|(_, t)| matches!(t, FieldTy::Opaque)); let has_non_scalar = def.fields.iter().any(|(_, t)| !matches!(t, FieldTy::Scalar(_)));
    if ctx.prog.check_reg_budget && (mutable || has_non_scalar) && !ctx.is_async { return None; }
    if (mutable || has_opaque) && !has_buf && !ctx.is_async { return None; }
    let (mut fs, mut pfs, mut buf_lens, mut usize_pids) = (Vec::with_capacity(def.fields.len()), Vec::with_capacity(def.fields.len()), Vec::new(), Vec::new());
    for (fname, fty) in &def.fields {
        let full = format!("{prefix}_{fname}");
        let v = match *fty {
            FieldTy::Scalar(st) => {
                let dom = if has_buf && st == ScalarTy::Usize { Domain::range(0, MAX_SYM_SLICE_LEN as i64) } else { st.domain() };
                let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(&full, dom);
                if st == ScalarTy::Usize { usize_pids.push(pid); }
                pfs.push((fname.clone(), st, pidx)); Val::Scalar(pid, Some(st)) }
            FieldTy::Slice(ety, mut_b) => {
                ctx.has_opaque = true; let reg = ctx.alloc_region();
                let len_pid = ctx.prog.add_named_param(format!("slice_len:{full}:{}", ety.as_str()), Domain::range(0, MAX_SYM_SLICE_LEN as i64));
                buf_lens.push(len_pid); let bid = ctx.prog.add_buf(&full, MAX_SYM_SLICE_LEN, mut_b, reg, 0, ety.domain());
                Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: MAX_SYM_SLICE_LEN, len_node: Some(len_pid), root_len: Some(len_pid), mutable: mut_b, elem_ty: ety, is_str: false }) }
            FieldTy::Str => {
                ctx.has_opaque = true; let reg = ctx.alloc_region(); let len_pid = ctx.prog.add_named_param(format!("str_len:{full}"), Domain::range(0, MAX_SYM_SLICE_LEN as i64));
                buf_lens.push(len_pid); let bid = ctx.prog.add_buf(&full, MAX_SYM_SLICE_LEN, false, reg, 0, ScalarTy::U8.domain());
                Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: MAX_SYM_SLICE_LEN, len_node: Some(len_pid), root_len: Some(len_pid), mutable: false, elem_ty: ScalarTy::U8, is_str: true }) }
            FieldTy::Opaque => { ctx.has_opaque = true; Val::Opaque }
        }; fs.push((fname.clone(), v)); }
    if buf_lens.len() == 1 {
        let bl = buf_lens[0];
        for pid in usize_pids { let le = ctx.push_g(Op::Cmp(CmpKind::Le, pid, bl)); ctx.cur_guard = ctx.and_guard(ctx.cur_guard, (le, true)); } }
    Some((Val::Struct(tname.to_string(), fs), pfs)) }
fn add_str_param(ctx: &mut LowerCtx<'_>, pname: String, poc_name: String, ov: Option<Domain>, reg_ov: Option<(u16, usize)>, owned: bool) -> Option<()> {
    if ctx.prog.check_reg_budget { return None; }
    let (region, offset) = reg_ov.unwrap_or_else(|| (ctx.alloc_region(), 0)); let pidx = ctx.prog.param_domains.len();
    let len_pid = ctx.prog.add_named_param(format!("str_len:{pname}"), ov.unwrap_or_else(|| Domain::range(0, MAX_SYM_SLICE_LEN as i64)));
    let bid = ctx.prog.add_buf(&pname, MAX_SYM_SLICE_LEN, false, region, offset, ScalarTy::U8.domain()); ctx.poc_params.push(PocParam::Str { name: poc_name, pidx, owned });
    ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: MAX_SYM_SLICE_LEN, len_node: Some(len_pid), root_len: Some(len_pid), mutable: false, elem_ty: ScalarTy::U8, is_str: true }));
    Some(()) }
fn push_scalar_param(ctx: &mut LowerCtx<'_>, pname: String, poc_name: String, st: ScalarTy, dom: Domain, by_ref: bool, mutable: bool) -> Option<()> {
    let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(&pname, dom); if by_ref && mutable { ctx.mut_refs.insert(pname.clone()); }
    ctx.poc_params.push(PocParam::Scalar { name: poc_name, ty: st, pidx, by_ref, mutable });
    ctx.vars.insert(pname, Val::Scalar(pid, Some(st))); Some(()) }
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
                ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: len, len_node: None, root_len: None, mutable, elem_ty: ety, is_str: false })); return Some(()); }
            if !c.eat_sym("]") { return None; }
            let spec = if mutable { format!("mut_slice_len:{pname}:{}", ety.as_str()) } else { format!("slice_len:{pname}:{}", ety.as_str()) };
            let pidx = ctx.prog.param_domains.len(); let len_pid = ctx.prog.add_named_param(spec, ov.unwrap_or_else(|| Domain::range(0, MAX_SYM_SLICE_LEN as i64)));
            let bid = if is_uninit { ctx.prog.add_uninit_buf(&pname, MAX_SYM_SLICE_LEN, mutable, region, offset, ety.domain()) } else { ctx.prog.add_buf(&pname, MAX_SYM_SLICE_LEN, mutable, region, offset, ety.domain()) };
            if mutable { ctx.mut_refs.insert(pname.clone()); }
            ctx.poc_params.push(PocParam::Slice { name: poc_name, ety, pidx, mutable });
            ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: MAX_SYM_SLICE_LEN, len_node: Some(len_pid), root_len: Some(len_pid), mutable, elem_ty: ety, is_str: false })); return Some(()); }
        let raw_t = c.expect_ident()?;
        if raw_t == "str" || raw_t == "String" { return add_str_param(ctx, pname, poc_name, ov, reg_ov, false); }
        if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); }
        let tname = ctx.resolve_ty(&raw_t).to_string();
        if let Some(st) = ctx.file.resolve_scalar(&tname) { return push_scalar_param(ctx, pname, poc_name, st, ov.unwrap_or_else(|| st.domain()), true, mutable); }
        if let Some((sv, fields)) = add_struct_params(ctx, &pname, &tname, mutable) {
            if mutable { ctx.mut_refs.insert(pname.clone()); }
            ctx.poc_params.push(PocParam::Struct { name: poc_name, ty: tname, fields, by_ref: true, mutable }); ctx.vars.insert(pname, sv); return Some(()); }
        return None; }
    if c.eat_sym("[") {
        let ety = c.expect_ident().and_then(|e| ctx.file.resolve_scalar(&e))?; if !c.eat_sym(";") { return None; }
        let len_i = ctx.file.eval_const_expr(c, item.self_ty.as_deref())?.0; if len_i <= 0 || len_i > 64 || !c.eat_sym("]") { return None; }
        let (region, offset) = reg_ov.unwrap_or_else(|| (ctx.alloc_region(), 0)); let bid = ctx.prog.add_buf(&pname, len_i as usize, bind_mut, region, offset, ov.unwrap_or_else(|| ety.domain()));
        ctx.poc_params.push(PocParam::Array { name: poc_name, ety, len: len_i as usize, by_ref: false, mutable: false });
        ctx.vars.insert(pname, Val::Buf(BufBind { id: bid, base_const: 0, base_node: None, len_const: len_i as usize, len_node: None, root_len: None, mutable: bind_mut, elem_ty: ety, is_str: false })); return Some(()); }
    let raw = c.expect_ident()?;
    if raw == "String" { return add_str_param(ctx, pname, poc_name, ov, reg_ov, true); }
    if raw == "Option" && c.eat_sym("<") {
        let it = ctx.file.resolve_scalar(&c.expect_ident()?)?; if !c.eat_sym(">") { return None; }
        let (is_some_idx, is_some) = (ctx.prog.param_domains.len(), ctx.prog.add_named_param(format!("{pname}_is_some"), Domain::range(0, 1)));
        let (val_idx, val) = (ctx.prog.param_domains.len(), ctx.prog.add_named_param(format!("{pname}_val"), ov.unwrap_or_else(|| it.domain())));
        ctx.poc_params.push(PocParam::Opt { name: poc_name, ty: it, is_some: is_some_idx, val: val_idx });
        ctx.vars.insert(pname, Val::Opt { is_some, payload: Box::new(Val::Scalar(val, Some(it))) }); return Some(()); }
    if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); }
    let tname = ctx.resolve_ty(&raw).to_string();
    if let Some(st) = ctx.file.resolve_scalar(&tname) { return push_scalar_param(ctx, pname, poc_name, st, ov.unwrap_or_else(|| st.domain()), false, false); }
    if let Some((sv, fields)) = add_struct_params(ctx, &pname, &tname, false) { ctx.poc_params.push(PocParam::Struct { name: poc_name, ty: tname, fields, by_ref: false, mutable: false }); ctx.vars.insert(pname, sv); return Some(()); }
    if let Some(ed) = ctx.file.enums.get(&tname) {
        let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param(&pname, Domain::range(0, ed.max_disc));
        ctx.poc_params.push(PocParam::Enum { name: poc_name, ty: tname, pidx, by_ref: false }); ctx.vars.insert(pname, Val::Scalar(pid, Some(ScalarTy::Usize))); return Some(()); }
    None }
fn lower_param(ctx: &mut LowerCtx<'_>, c: &mut Cursor<'_>, item: &FnItem) -> Option<()> {
    let (mut pm, mut pd, mut pu, mut pr) = (FnMeta::default(), None, false, None);
    loop {
        match c.peek() { Some(Tok::Doc(l)) => { parse_doc_meta(l, &mut pm); c.pos += 1; } Some(Tok::Sym("#")) => { let (d, u, r, _) = c.parse_attr(&mut pm); pd = pd.or(d); pu |= u; pr = pr.or(r); } _ => break }
    }
    let (is_ref_self, is_mut_self) = (c.eat_sym("&"), c.eat_ident("mut"));
    if c.eat_ident("self") {
        let st_name = item.self_ty.as_deref()?;
        if let Some((sv, fields)) = add_struct_params(ctx, "self", st_name, is_ref_self && is_mut_self) {
            if is_ref_self && is_mut_self { ctx.mut_refs.insert("self".to_string()); }
            ctx.poc_params.push(PocParam::Struct { name: "self_val".to_string(), ty: st_name.to_string(), fields, by_ref: is_ref_self, mutable: is_ref_self && is_mut_self });
            ctx.vars.insert("self".to_string(), sv); return Some(()); }
        if let Some(ed) = ctx.file.enums.get(st_name) {
            if is_ref_self && is_mut_self { return None; }
            let pidx = ctx.prog.param_domains.len(); let pid = ctx.prog.add_named_param("self", Domain::range(0, ed.max_disc));
            ctx.poc_params.push(PocParam::Enum { name: "self_val".to_string(), ty: st_name.to_string(), pidx, by_ref: is_ref_self });
            ctx.vars.insert("self".to_string(), Val::Scalar(pid, Some(ScalarTy::Usize))); return Some(()); }
        if item.is_async { ctx.has_opaque = true; ctx.vars.insert("self".to_string(), Val::Opaque); return Some(()); }
        return None; }
    if is_ref_self { return None; }
    let (bind_mut, pname) = (is_mut_self, c.expect_ident()?); if !c.eat_sym(":") { return None; }
    let (ty_pos, poc_name) = (c.pos, if pname == "_" { format!("p{}", ctx.poc_params.len()) } else { pname.clone() });
    let ov = pd.or_else(|| pm.domains.get(&pname).copied()).or_else(|| item.meta.domains.get(&pname).copied());
    let is_uninit = pu || pm.uninit.contains(&pname) || item.meta.uninit.contains(&pname);
    let reg_ov = pr.or_else(|| pm.regions.get(&pname).copied()).or_else(|| item.meta.regions.get(&pname).copied());
    if lower_concrete_param(ctx, c, item, (pname.clone(), poc_name, bind_mut), (ov, is_uninit, reg_ov)).is_some() { return Some(()); }
    if item.is_async { c.pos = ty_pos; c.skip_until(",", ")", true); ctx.has_opaque = true; if pname != "_" { ctx.vars.insert(pname, Val::Opaque); } return Some(()); }
    None }
fn eat_bracket_ret(c: &mut Cursor<'_>, idx: &FileIndex, self_ty: Option<&str>) -> Option<()> { idx.resolve_scalar(&c.expect_ident()?)?; if c.eat_sym(";") { let _ = idx.eval_const_expr(c, self_ty)?; } c.eat_sym("]").then_some(()) }
fn validate_ret_ty(c: &mut Cursor<'_>, idx: &FileIndex, self_ty: Option<&str>) -> Option<bool> {
    let ret_opt = if !c.eat_sym("->") { false } else if c.eat_sym("(") {
        while !c.eat_sym(")") {
            let _ = c.eat_sym("&"); let _ = c.eat_ident("mut");
            if c.eat_sym("[") { eat_bracket_ret(c, idx, self_ty)?; }
            else { let nm = c.expect_ident()?; if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); } let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if rn != "str" && rn != "String" && idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) && !idx.enums.contains_key(rn) { return None; } }
            let _ = c.eat_sym(","); }
        false
    } else if c.eat_sym("&") {
        let _ = c.eat_ident("mut");
        if c.eat_sym("[") { eat_bracket_ret(c, idx, self_ty)?; }
        else { let nm = c.expect_ident()?; if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); } let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if rn != "str" && rn != "String" && idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) { return None; } }
        false
    } else if c.eat_sym("[") {
        idx.resolve_scalar(&c.expect_ident()?)?; if !c.eat_sym(";") { return None; }
        let len = idx.eval_const_expr(c, self_ty)?.0; if len <= 0 || len > 64 || !c.eat_sym("]") { return None; } false
    } else {
        let mut nm = c.expect_ident()?; while c.eat_sym("::") { nm = c.expect_ident()?; }
        if (nm == "Option" || nm == "Result") && matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); true }
        else { if matches!(c.peek(), Some(Tok::Sym("<"))) { c.skip_angles(); } let rn = if nm == "Self" { self_ty? } else { nm.as_str() }; if rn != "str" && rn != "String" && idx.resolve_scalar(rn).is_none() && !idx.structs.contains_key(rn) && !idx.enums.contains_key(rn) { return None; } false }
    }; if c.eat_ident("where") { c.skip_until("{", ";", false); }
    matches!(c.peek(), Some(Tok::Sym("{"))).then_some(ret_opt) }
fn lower_fn_item(item: &FnItem, file: &FileIndex, toks: &[Tok], inlined: &mut BTreeSet<String>, opts: RustFeOptions) -> Option<LoweredFn> {
    if item.is_unsafe || (item.vis == 0 && item.in_generic_impl && !item.is_async) { return None; }
    let (mut c, mut has_opaque) = (Cursor { toks, pos: item.sig_pos }, false);
    if !c.eat_empty_generics() { if !item.is_async { return None; } c.pos = item.sig_pos; c.skip_angles(); has_opaque = true; }
    if !c.eat_sym("(") { return None; }
    let mut prog = Program::new(&item.name); prog.simd_lanes = 1; prog.check_reg_budget = opts.enforce_reg_budget;
    let mut ctx = LowerCtx {
        prog, poc_params: Vec::new(), vars: BTreeMap::new(), mut_refs: BTreeSet::new(), stores: Vec::new(), cur_guard: None, early_rets: Vec::new(), file, toks,
        depth: 0, loop_depth: 0, in_loop: false, inlined_fns: inlined, next_region: 1, self_ty: item.self_ty.clone(), no_struct_lit: false, returns_opt: false,
        is_async: item.is_async, has_opaque, utf8: Utf8State::default(),
    }; while !c.eat_sym(")") { lower_param(&mut ctx, &mut c, item)?; let _ = c.eat_sym(","); }
    ctx.returns_opt = validate_ret_ty(&mut c, file, item.self_ty.as_deref())?; let (rets, tail, _) = ctx.parse_block(&mut c)?; let mut final_val = tail.or_else(|| rets.into_iter().next());
    for (cond, ev) in std::mem::take(&mut ctx.early_rets).into_iter().rev() {
        final_val = Some(match final_val {
            Some(cur) if ctx.is_const_zero_opt(&cur) && matches!(ev, Val::Opt { .. }) => { let nc = ctx.mk_bool(cond, false); ctx.merge_val(nc, cur, ev, None)? }
            Some(cur) => ctx.merge_val(cond, ev, cur, None)?, None => ev,
        }); }
    if let Some(fv) = final_val { let mut flat = Vec::new(); LowerCtx::flatten_val(&fv, &mut flat); for r in flat { ctx.prog.add_output(r); } }
    for s in ctx.stores { if !ctx.prog.outputs.contains(&s) { ctx.prog.add_output(s); } }
    Some(LoweredFn { prog: ctx.prog, params: ctx.poc_params, is_async: ctx.is_async, has_opaque: ctx.has_opaque }) }
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
            PocParam::Str { name, pidx, owned } => { let len = usize::try_from(ce.inputs.get(*pidx).copied().unwrap_or(0)).map_or(0, |n| n.min(MAX_SYM_SLICE_LEN)); if *owned { (format!("    let {name}: String = \"a\".repeat({len});\n"), name.clone()) } else { (format!("    let {name}: String = \"a\".repeat({len});\n"), format!("&{name}")) } }
            PocParam::Opt { name, ty, is_some, val } => { let rhs = if ce.inputs.get(*is_some).copied().unwrap_or(0) != 0 { format!("Some({})", fmt_scalar(*ty, ce.inputs.get(*val).copied().unwrap_or(0))) } else { "None".to_string() }; (format!("    let {name}: Option<{}> = {rhs};\n", ty.as_str()), name.clone()) }
            PocParam::Struct { name, ty, fields, by_ref, mutable } => { let (kw, a) = ref_arg(name, *by_ref, *mutable); let fs: Vec<String> = fields.iter().map(|(f, ft, idx)| format!("{f}: {}", fmt_scalar(*ft, ce.inputs.get(*idx).copied().unwrap_or(0)))).collect(); (format!("    {kw} {name} = {ty} {{ {} }};\n", fs.join(", ")), a) }
            PocParam::Enum { name, ty, pidx, by_ref } => { let v = ce.inputs.get(*pidx).copied().unwrap_or(0); let vn = file.enums.get(ty).and_then(|e| e.variants.iter().find(|(_, &d)| d == v).or_else(|| e.variants.iter().next())).map_or("_", |(k, _)| k.as_str()); let (kw, a) = ref_arg(name, *by_ref, false); (format!("    {kw} {name} = {ty}::{vn};\n"), a) }
        }; out.push_str(&line); args.push(arg); }
    let call = format!("{}({})", lf.prog.name, args.join(", "));
    if lf.is_async { out.push_str(&format!("    let mut cx = std::task::Context::from_waker(std::task::Waker::noop());\n    let mut fut = std::pin::pin!({call});\n    for _ in 0..8 {{ if std::future::Future::poll(fut.as_mut(), &mut cx).is_ready() {{ break; }} }}\n}}\n")); }
    else { out.push_str(&format!("    let _ = {call};\n}}\n")); }
    out }
fn extract_poc(lf: &LoweredFn, file: &FileIndex, error: &VerifyError, cfg: RefineConfig) -> Option<String> {
    if lf.has_opaque { return None; }
    let ce = match error {
        VerifyError::CounterexampleFound { node, fault, inputs } => Counterexample { inputs: inputs.clone(), node: *node, fault: *fault },
        VerifyError::DivByZero { .. } | VerifyError::OutOfBounds { .. } | VerifyError::ExplicitPanic { .. } | VerifyError::Utf8CharBoundary { .. } | VerifyError::ShiftOverflow { .. } | VerifyError::IntOverflow { .. } | VerifyError::UseAfterFree { .. } | VerifyError::DoubleFree { .. } | VerifyError::UninitializedRead { .. } =>
            sample_counterexample(&lf.prog, cfg.seed).or_else(|| refine_and_fuzz(&lf.prog, RefineConfig { max_epochs: 1, fuzz_ticks_per_box: 1, ..cfg }).counterexamples.into_iter().next())?,
        _ => return None, };
    Some(render_poc_test(lf, file, &ce)) }
pub(crate) type FnSig<'a> = (bool, Vec<(String, &'a [Tok])>, &'a [Tok], &'a [Tok]);
pub(crate) fn fn_sig_params<'a>(item: &FnItem, toks: &'a [Tok]) -> Option<FnSig<'a>> {
    let i = skip_bal(toks, item.sig_pos, toks.len(), "<", ">");
    if !matches!(toks.get(i), Some(Tok::Sym("("))) { return None; }
    let pend = skip_bal(toks, i, toks.len(), "(", ")"); let (mut has_self, mut params) = (false, Vec::new());
    for seg in split_top_commas(toks.get(i + 1..pend.saturating_sub(1)).unwrap_or(&[]), true) {
        let mut s = 0usize; while matches!(seg.get(s), Some(Tok::Sym("#"))) { s = skip_bal(seg, s + 1, seg.len(), "[", "]"); }
        let seg = seg.get(s..).unwrap_or(&[]);
        if seg.iter().take(4).any(|t| matches!(t, Tok::Ident(w) if w == "self")) { has_self = true; }
        else if let Some(cp) = seg.iter().position(|t| matches!(t, Tok::Sym(":"))) {
            let nm = seg.get(..cp).and_then(|l| l.iter().rev().find_map(|t| if let Tok::Ident(w) = t { (w != "mut" && w != "ref").then(|| w.clone()) } else { None })).unwrap_or_else(|| "_".to_string());
            params.push((nm, seg.get(cp + 1..).unwrap_or(&[]))); } }
    let ret = if matches!(toks.get(pend), Some(Tok::Sym("->"))) { toks.get(pend + 1..item.body.0.saturating_sub(1)).unwrap_or(&[]) } else { &[] };
    Some((has_self, params, ret, toks.get(item.body.0..item.body.1).unwrap_or(&[]))) }
fn strip_parens(mut sl: &[Tok]) -> &[Tok] {
    while matches!(sl.first(), Some(Tok::Sym("("))) && skip_bal(sl, 0, sl.len(), "(", ")") == sl.len() { sl = sl.get(1..sl.len().saturating_sub(1)).unwrap_or(&[]); }
    sl }
fn find_top_sym(sl: &[Tok], sym: &str) -> Option<usize> {
    let mut i = 0usize;
    while i < sl.len() {
        match sl.get(i) {
            Some(Tok::Sym(s)) if *s == sym => return Some(i),
            Some(Tok::Sym("(")) => i = skip_bal(sl, i, sl.len(), "(", ")"),
            Some(Tok::Sym("[")) => i = skip_bal(sl, i, sl.len(), "[", "]"),
            Some(Tok::Sym("{")) => i = skip_bal(sl, i, sl.len(), "{", "}"),
            _ => i += 1, } }
    None }
fn split_stmts(sl: &[Tok]) -> Vec<&[Tok]> {
    let (mut out, mut i, mut s) = (Vec::new(), 0usize, 0usize);
    while i < sl.len() {
        match sl.get(i) {
            Some(Tok::Sym(";")) => { if s < i { out.push(sl.get(s..i).unwrap_or(&[])); } i += 1; s = i; }
            Some(Tok::Sym("(")) => i = skip_bal(sl, i, sl.len(), "(", ")"),
            Some(Tok::Sym("[")) => i = skip_bal(sl, i, sl.len(), "[", "]"),
            Some(Tok::Sym("{")) => {
                i = skip_bal(sl, i, sl.len(), "{", "}");
                if matches!(sl.get(s), Some(Tok::Ident(w)) if matches!(w.as_str(), "if" | "while" | "for" | "loop" | "match")) && !matches!(sl.get(i), Some(Tok::Ident(w)) if w == "else") && !matches!(sl.get(i), Some(Tok::Sym(";" | "." | "&&" | "||"))) { out.push(sl.get(s..i).unwrap_or(&[])); s = i; }
            }
            _ => i += 1, } }
    if s < sl.len() { out.push(sl.get(s..).unwrap_or(&[])); }
    out }
fn is_ascii_lit(t: &Tok) -> bool { matches!(t, Tok::Int(v, _) if (0..128).contains(v)) || matches!(t, Tok::Sym("@c")) }
fn is_ascii_pat(pat: &[Tok]) -> bool {
    let (mut s, mut any) = (0usize, false);
    for i in 0..=pat.len() {
        if i == pat.len() || matches!(pat.get(i), Some(Tok::Sym("|"))) {
            any = true;
            let ok = match strip_parens(pat.get(s..i).unwrap_or(&[])) {
                [t] => is_ascii_lit(t),
                [Tok::Int(lo, _), Tok::Sym("..="), Tok::Int(hi, _)] => (0..128).contains(lo) && (0..128).contains(hi),
                [Tok::Int(lo, _), Tok::Sym(".."), Tok::Int(hi, _)] => (0..128).contains(lo) && (1..=128).contains(hi),
                _ => false, };
            if !ok { return false; }
            s = i + 1; } }
    any }
fn ascii_guarded_expr<'a>(sl: &'a [Tok], preds: &BTreeSet<String>) -> Option<&'a [Tok]> {
    let sl = strip_parens(sl);
    if let Some(p) = find_top_sym(sl, "||") {
        let (a, b) = (ascii_guarded_expr(sl.get(..p).unwrap_or(&[]), preds)?, ascii_guarded_expr(sl.get(p + 1..).unwrap_or(&[]), preds)?);
        return (strip_parens(a) == strip_parens(b)).then_some(a);
    }
    match sl {
        [x @ .., Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if !x.is_empty() && m.starts_with("is_ascii") => Some(x),
        [x @ .., Tok::Sym("=="), t] | [t, Tok::Sym("=="), x @ ..] if !x.is_empty() && is_ascii_lit(t) => Some(x),
        [x @ .., Tok::Sym("<"), Tok::Int(v, _)] if !x.is_empty() && (1..=128).contains(v) => Some(x),
        [x @ .., Tok::Sym("<="), Tok::Int(v, _)] if !x.is_empty() && (0..128).contains(v) => Some(x),
        [Tok::Ident(p), Tok::Sym("("), x @ .., Tok::Sym(")")] if !x.is_empty() && preds.contains(p) && skip_bal(sl, 1, sl.len(), "(", ")") == sl.len() => Some(x),
        [Tok::Ident(m), Tok::Sym("!"), Tok::Sym("("), rest @ .., Tok::Sym(")")] if m == "matches" && skip_bal(sl, 2, sl.len(), "(", ")") == sl.len() => find_top_sym(rest, ",").filter(|&cp| is_ascii_pat(rest.get(cp + 1..).unwrap_or(&[]))).and_then(|cp| rest.get(..cp)),
        [Tok::Sym("("), Tok::Int(lo, _), Tok::Sym(op @ ("..=" | "..")), Tok::Int(hi, _), Tok::Sym(")"), Tok::Sym("."), Tok::Ident(c), Tok::Sym("("), Tok::Sym("&"), x @ .., Tok::Sym(")")] if c == "contains" && !x.is_empty() && (0..128).contains(lo) && if *op == "..=" { (0..128).contains(hi) } else { (1..=128).contains(hi) } => Some(x),
        _ => None, } }
fn is_ascii_byte_expr(sl: &[Tok], bvar: &str, preds: &BTreeSet<String>) -> bool {
    let sl = strip_parens(sl);
    if let Some(p) = find_top_sym(sl, "||") { return is_ascii_byte_expr(sl.get(..p).unwrap_or(&[]), bvar, preds) && is_ascii_byte_expr(sl.get(p + 1..).unwrap_or(&[]), bvar, preds); }
    if let Some(p) = find_top_sym(sl, "&&") { return is_ascii_byte_expr(sl.get(..p).unwrap_or(&[]), bvar, preds) || is_ascii_byte_expr(sl.get(p + 1..).unwrap_or(&[]), bvar, preds); }
    ascii_guarded_expr(sl, preds).is_some_and(|x| matches!(strip_parens(x), [Tok::Ident(b)] if b == bvar)) }
fn is_ascii_iter_pred(arg: &[Tok], preds: &BTreeSet<String>) -> bool {
    matches!(arg, [Tok::Ident(u), Tok::Sym("::"), Tok::Ident(f)] if u == "u8" && f.starts_with("is_ascii"))
        || matches!(arg, [Tok::Sym("|"), Tok::Ident(b), Tok::Sym("|"), body @ ..] if is_ascii_byte_expr(body, b, preds))
        || matches!(arg, [Tok::Ident(p)] if preds.contains(p)) }
fn collect_ascii_byte_preds(file: &FileIndex, toks: &[Tok], out: &mut BTreeSet<String>) {
    for f in &file.fns {
        if f.self_ty.is_some() || f.in_mod { continue; }
        if let Some((_, [(nm, [Tok::Ident(ty)])], _, body)) = fn_sig_params(f, toks).as_ref().map(|(s, p, r, b)| (*s, p.as_slice(), *r, *b)) { if ty == "u8" && is_ascii_byte_expr(body, nm, out) { out.insert(f.short_name.clone()); } }
    } }
#[derive(Clone, Debug)]
pub(crate) struct BoundaryMorphism { bytes_param: usize, req_plus1: Option<usize>, req_ascii: Option<usize>, req_safe: Option<usize>, ret_opt: bool, ret_plus1: bool, ret_minus1: bool }
struct BmCtx<'a> {
    bn: &'a str, u8_p: BTreeMap<String, usize>, us_p: BTreeMap<String, usize>, preds: &'a BTreeSet<String>,
    quote_src: BTreeMap<String, usize>, base_param: BTreeMap<String, usize>,
    req_plus1: Option<usize>, req_ascii: Option<usize>, req_safe: Option<usize>,
    ret_opt: bool, saw_val: bool, ret_plus1: bool, ret_minus1: bool, ok: bool, }
impl<'a> BmCtx<'a> {
    fn guard_byte_idx(&mut self, cond: &[Tok], out: &mut BTreeSet<String>) {
        let cond = strip_parens(cond);
        if let Some(p) = find_top_sym(cond, "&&") { self.guard_byte_idx(cond.get(..p).unwrap_or(&[]), out); self.guard_byte_idx(cond.get(p + 1..).unwrap_or(&[]), out); return; }
        if let Some([Tok::Ident(b), Tok::Sym("["), Tok::Ident(ix), Tok::Sym("]")]) = ascii_guarded_expr(cond, self.preds).map(strip_parens) { if b == self.bn { out.insert(ix.clone()); return; } }
        if let [Tok::Ident(b), Tok::Sym("["), Tok::Ident(ix), Tok::Sym("]"), Tok::Sym("=="), Tok::Ident(q)] = cond {
            if b == self.bn {
                if let Some(&qp) = self.quote_src.get(q) { self.req_plus1 = Some(qp); out.insert(ix.clone()); }
                else if let Some(&dp) = self.u8_p.get(q) { self.req_ascii = Some(dp); out.insert(ix.clone()); } }
        } }
    fn check_ret(&mut self, expr: &[Tok], safe: &BTreeSet<String>, ascii_at: &BTreeSet<String>) {
        let e = strip_parens(expr);
        let core = if self.ret_opt {
            if matches!(e, [Tok::Ident(w)] if w == "None") { return; }
            if matches!(e.first(), Some(Tok::Ident(w)) if w == "Some") && matches!(e.get(1), Some(Tok::Sym("("))) && skip_bal(e, 1, e.len(), "(", ")") == e.len() { strip_parens(e.get(2..e.len().saturating_sub(1)).unwrap_or(&[])) } else { self.ok = false; return; }
        } else { e }; self.saw_val = true;
        match core {
            [Tok::Int(0, _)] if !self.ret_opt => { self.ret_plus1 = false; self.ret_minus1 = false; }
            [Tok::Ident(b), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if !self.ret_opt && b == self.bn && m == "len" => { self.ret_plus1 = false; self.ret_minus1 = false; }
            [Tok::Ident(ix)] if ascii_at.contains(ix) => { self.ret_minus1 = false; }
            [Tok::Ident(ix)] if safe.contains(ix) => { self.ret_plus1 = false; self.ret_minus1 = false; }
            [Tok::Ident(ix), Tok::Sym("+"), Tok::Int(1, _)] if ascii_at.contains(ix) => { self.ret_plus1 = false; }
            _ => self.ok = false, } }
    fn walk_block(&mut self, sl: &[Tok], safe: &mut BTreeSet<String>, ascii_at: &BTreeSet<String>, is_tail: bool) {
        let stmts = split_stmts(sl);
        for (si, &st) in stmts.iter().enumerate() {
            let tail = is_tail && si + 1 == stmts.len() && !matches!(sl.last(), Some(Tok::Sym(";")));
            match st.first() {
                Some(Tok::Ident(w)) if w == "return" => self.check_ret(st.get(1..).unwrap_or(&[]), safe, ascii_at),
                Some(Tok::Ident(w)) if w == "let" => if let Some(eq) = find_top_sym(st, "=") {
                    for (lp, rp) in split_top_commas(strip_parens(st.get(1..eq).unwrap_or(&[])), false).into_iter().zip(split_top_commas(strip_parens(st.get(eq + 1..).unwrap_or(&[])), false)) {
                        if let Some(Tok::Ident(nm)) = lp.iter().rev().find(|t| matches!(t, Tok::Ident(w) if w != "mut")) {
                            match rp {
                                [Tok::Ident(b), Tok::Sym("["), Tok::Ident(q), Tok::Sym("]")] if b == self.bn => if let Some(&qp) = self.us_p.get(q) { self.quote_src.insert(nm.clone(), qp); }
                                [Tok::Ident(q)] => if let Some(&qp) = self.us_p.get(q) { self.base_param.insert(nm.clone(), qp); }
                                _ => {} }
                        } } },
                Some(Tok::Ident(w)) if w == "if" => {
                    let mut cur = st;
                    while let Some(bs) = find_top_sym(cur, "{") {
                        let be = skip_bal(cur, bs, cur.len(), "{", "}"); let mut ta = ascii_at.clone(); self.guard_byte_idx(cur.get(1..bs).unwrap_or(&[]), &mut ta);
                        self.walk_block(cur.get(bs + 1..be.saturating_sub(1)).unwrap_or(&[]), &mut safe.clone(), &ta, tail);
                        if !matches!(cur.get(be), Some(Tok::Ident(e)) if e == "else") { if tail { self.ok = false; } break; }
                        if matches!(cur.get(be + 1), Some(Tok::Ident(e)) if e == "if") { cur = cur.get(be + 1..).unwrap_or(&[]); }
                        else if matches!(cur.get(be + 1), Some(Tok::Sym("{"))) {
                            let ee = skip_bal(cur, be + 1, cur.len(), "{", "}");
                            self.walk_block(cur.get(be + 2..ee.saturating_sub(1)).unwrap_or(&[]), &mut safe.clone(), ascii_at, tail); break;
                        } else { break; } } }
                Some(Tok::Ident(w)) if matches!(w.as_str(), "while" | "for" | "loop") => if let Some(bs) = find_top_sym(st, "{") {
                    let (cond, wb) = (st.get(1..bs).unwrap_or(&[]), st.get(bs + 1..skip_bal(st, bs, st.len(), "{", "}").saturating_sub(1)).unwrap_or(&[]));
                    let mut wa = ascii_at.clone(); if w == "while" { self.guard_byte_idx(cond, &mut wa); }
                    self.walk_block(wb, &mut safe.clone(), &wa, false); let wstmts = split_stmts(wb);
                    for s in &wstmts { if let Some(Tok::Ident(v)) = s.first() { if matches!(s.get(1), Some(Tok::Sym("=" | "+=" | "-="))) && !wa.contains(v) { safe.remove(v); } } }
                    if w == "while" && !wb.is_empty() {
                        for ix in &wa { if wstmts.iter().all(|s| matches!(s, [Tok::Ident(v), Tok::Sym("+="), Tok::Int(1, _)] if v == ix)) { if let Some(&p) = self.us_p.get(ix).or_else(|| self.base_param.get(ix)) { self.req_safe = Some(p); safe.insert(ix.clone()); } } }
                    } },
                Some(Tok::Ident(w)) if w == "match" => if let Some(bs) = find_top_sym(st, "{") {
                    let scrut_iv = match strip_parens(st.get(1..bs).unwrap_or(&[])) { [Tok::Ident(b), Tok::Sym("["), Tok::Ident(ix), Tok::Sym("]")] if b == self.bn => Some(ix.clone()), _ => None };
                    let (arms, mut k) = (st.get(bs + 1..skip_bal(st, bs, st.len(), "{", "}").saturating_sub(1)).unwrap_or(&[]), 0usize);
                    while let Some(fa) = find_top_sym(arms.get(k..).unwrap_or(&[]), "=>").map(|o| k + o) {
                        let (pat, as_, is_blk) = (arms.get(k..fa).unwrap_or(&[]), fa + 1, matches!(arms.get(fa + 1), Some(Tok::Sym("{"))));
                        let ae = if is_blk { skip_bal(arms, as_, arms.len(), "{", "}") } else { find_top_sym(arms.get(as_..).unwrap_or(&[]), ",").map_or(arms.len(), |o| as_ + o) };
                        let mut aa = ascii_at.clone(); if let Some(ref ix) = scrut_iv { if is_ascii_pat(pat) { aa.insert(ix.clone()); } }
                        if is_blk { self.walk_block(arms.get(as_ + 1..ae.saturating_sub(1)).unwrap_or(&[]), &mut safe.clone(), &aa, tail); }
                        else if tail { self.check_ret(arms.get(as_..ae).unwrap_or(&[]), safe, &aa); }
                        else { self.walk_block(arms.get(as_..ae).unwrap_or(&[]), &mut safe.clone(), &aa, false); }
                        k = if matches!(arms.get(ae), Some(Tok::Sym(","))) { ae + 1 } else { ae }; } },
                _ => if tail { self.check_ret(st, safe, ascii_at); }, }
        } } }
fn collect_boundary_morphisms(fidxs: &[FileIndex], all_toks: &[Vec<Tok>], preds: &BTreeSet<String>) -> BTreeMap<String, BoundaryMorphism> {
    let mut out: BTreeMap<String, BoundaryMorphism> = BTreeMap::new();
    for pass in 0..2 {
        for (file, toks) in fidxs.iter().zip(all_toks.iter()) {
            for f in &file.fns {
                if f.self_ty.is_some() || f.in_mod || out.contains_key(&f.short_name) { continue; }
                let Some((_, params, ret, body)) = fn_sig_params(f, toks) else { continue; };
                let Some((bp, (bn, _))) = params.iter().enumerate().find(|(_, (_, ty))| matches!(ty, [Tok::Sym("&"), Tok::Sym("["), Tok::Ident(u), Tok::Sym("]")] if u == "u8")) else { continue; };
                let ret_opt = matches!(ret, [Tok::Ident(o), Tok::Sym("<"), Tok::Ident(u), Tok::Sym(">")] if o == "Option" && u == "usize");
                if !ret_opt && !matches!(ret, [Tok::Ident(u)] if u == "usize") { continue; }
                if pass == 1 {
                    if !ret_opt { if let [Tok::Ident(cal), Tok::Sym("("), ..] = body {
                        let pe = skip_bal(body, 1, body.len(), "(", ")"); let args = split_top_commas(body.get(2..pe.saturating_sub(1)).unwrap_or(&[]), false);
                        let tail_ok = matches!(body.get(pe..), Some([Tok::Sym("."), Tok::Ident(u), Tok::Sym("("), Tok::Int(0, _), Tok::Sym(")")]) if u == "unwrap_or")
                            || matches!(body.get(pe..), Some([Tok::Sym("."), Tok::Ident(u), Tok::Sym("("), Tok::Ident(b), Tok::Sym("."), Tok::Ident(l), Tok::Sym("("), Tok::Sym(")"), Tok::Sym(")")]) if u == "unwrap_or" && b == bn && l == "len");
                        let map_p = |ai: usize| args.get(ai).and_then(|a| if let [Tok::Ident(v)] = a { params.iter().position(|(pn, _)| pn == v) } else { None });
                        if let Some(m) = out.get(cal).filter(|m| m.ret_opt && tail_ok && map_p(m.bytes_param) == Some(bp)) {
                            out.insert(f.short_name.clone(), BoundaryMorphism { bytes_param: bp, req_plus1: m.req_plus1.and_then(map_p), req_ascii: m.req_ascii.and_then(map_p), req_safe: m.req_safe.and_then(map_p), ret_opt: false, ret_plus1: false, ret_minus1: false });
                        }
                    } }
                    continue; }
                let u8_p = params.iter().enumerate().filter(|(_, (_, ty))| matches!(ty, [Tok::Ident(u)] if u == "u8")).map(|(i, (n, _))| (n.clone(), i)).collect();
                let us_p = params.iter().enumerate().filter(|(_, (_, ty))| matches!(ty, [Tok::Ident(u)] if u == "usize")).map(|(i, (n, _))| (n.clone(), i)).collect();
                let mut ctx = BmCtx { bn, u8_p, us_p, preds, quote_src: BTreeMap::new(), base_param: BTreeMap::new(), req_plus1: None, req_ascii: None, req_safe: None, ret_opt, saw_val: false, ret_plus1: true, ret_minus1: true, ok: true };
                ctx.walk_block(body, &mut BTreeSet::new(), &BTreeSet::new(), true);
                if ctx.ok && ctx.saw_val { out.insert(f.short_name.clone(), BoundaryMorphism { bytes_param: bp, req_plus1: ctx.req_plus1, req_ascii: ctx.req_ascii, req_safe: ctx.req_safe, ret_opt, ret_plus1: ctx.ret_plus1, ret_minus1: ctx.ret_minus1 }); }
            } } }
    out }
#[derive(Clone, Default)]
pub(crate) struct Utf8ParamInit { pub(crate) safe: BTreeSet<String>, pub(crate) plus1: BTreeSet<String>, pub(crate) ascii_str: BTreeSet<String> }
pub(crate) struct Utf8Pending { pub(crate) ridx: usize, pub(crate) fidx: usize, pub(crate) item_idx: usize }
pub(crate) struct Utf8CallWitness { pub(crate) qual: Option<String>, pub(crate) short: String, pub(crate) is_method: bool, pub(crate) arg_safe: Vec<bool>, pub(crate) arg_plus1: Vec<bool>, pub(crate) arg_ascii: Vec<bool> }
type Witness = (String, Option<String>, Option<i64>, Option<i64>);
#[derive(Clone, Copy)]
struct Utf8Ctx<'a> { file: &'a FileIndex, preds: &'a BTreeSet<String>, morphs: &'a BTreeMap<String, BoundaryMorphism> }
#[derive(Clone, Default)]
struct WitnessLattice {
    str_vars: BTreeSet<String>, self_str_fields: BTreeSet<String>, ascii_ok: BTreeSet<String>,
    safe_for: BTreeMap<String, BTreeSet<String>>, safe_plus: BTreeMap<String, BTreeMap<String, BTreeSet<i64>>>,
    safe_minus: BTreeMap<String, BTreeMap<String, BTreeSet<i64>>>, starts: BTreeMap<String, BTreeSet<i64>>,
    ends: BTreeMap<String, BTreeSet<i64>>, sym_bounds: BTreeMap<String, BTreeSet<String>>,
    len_tail_eq: BTreeMap<String, Vec<(String, String)>>, ends_sym: BTreeMap<String, BTreeSet<String>>,
    bytes_of: BTreeMap<String, String>, byte_var: BTreeMap<String, (String, String)>, char_of: BTreeMap<String, (String, String)>,
    rel_of: BTreeMap<String, (String, String, Option<i64>)>, sub_of: BTreeMap<String, (String, String)>,
    local_strs: BTreeMap<String, (usize, bool)>, local_ints: BTreeMap<String, i64>, safe_ranges: BTreeMap<String, String>,
    opt_vars: BTreeSet<String>, poisoned: BTreeSet<String>, }
impl WitnessLattice {
    fn mark_safe(&mut self, recv: &str, var: &str, plus: Option<i64>, minus: Option<i64>) {
        self.poisoned.remove(var);
        self.safe_for.entry(recv.to_string()).or_default().insert(var.to_string());
        if let Some(k) = plus { self.safe_plus.entry(recv.to_string()).or_default().entry(var.to_string()).or_default().insert(k); }
        if let Some(k) = minus { self.safe_minus.entry(recv.to_string()).or_default().entry(var.to_string()).or_default().insert(k); } }
    fn mark_ascii_expr(&mut self, x: &[Tok]) {
        match strip_parens(x) {
            [Tok::Ident(bv), Tok::Sym("["), idx_t, Tok::Sym("]")] => self.mark_byte_idx(bv, idx_t),
            [Tok::Ident(ch)] => for (sv, ix) in [self.char_of.get(ch).cloned(), self.byte_var.get(ch).cloned()].into_iter().flatten() { self.mark_safe(&sv, &ix, Some(1), None); }
            _ => {} } }
    fn merge_mut(&mut self, sub: &Self) {
        for v in &sub.poisoned { self.poisoned.insert(v.clone()); self.opt_vars.remove(v); self.local_ints.remove(v); for s in self.safe_for.values_mut() { s.remove(v); } }
        for (r, vs) in &sub.safe_for { for v in vs { if self.opt_vars.contains(v) && !self.poisoned.contains(v) { self.safe_for.entry(r.clone()).or_default().insert(v.clone()); } } } }
    fn bind_witness(&mut self, dst: &str, (r, bs, pk, mk): Witness) { if let Some(b) = bs { self.rel_of.insert(dst.to_string(), (r, b, pk)); } else { self.mark_safe(&r, dst, pk, mk); } }
    fn mark_byte_idx(&mut self, bv: &str, idx_t: &Tok) {
        if let Some(sv) = self.bytes_of.get(bv).cloned() { match idx_t { Tok::Int(0, _) => { self.starts.entry(sv).or_default().insert(1); } Tok::Ident(ix) => self.mark_safe(&sv, ix, Some(1), None), _ => {} } } }
    fn str_lit_info(&self, tok: Option<&Tok>, file: &FileIndex) -> Option<(usize, bool, Option<String>)> {
        match tok? {
            &Tok::Str(l, a) => Some((l, a, None)), Tok::Sym("@c") => Some((1, true, None)),
            Tok::Ident(c) => self.local_strs.get(c).or_else(|| file.str_consts.get(c)).map(|&(l, a)| (l, a, Some(c.clone()))), _ => None, } }
    fn has_plus1(&self, recv: &str, expr: &[Tok]) -> bool {
        match strip_parens(expr) {
            [Tok::Ident(v)] => self.safe_plus.get(recv).and_then(|m| m.get(v)).is_some_and(|ks| ks.contains(&1)),
            [Tok::Ident(a), Tok::Sym("+"), Tok::Ident(b)] => self.rel_of.get(b).is_some_and(|(r, bs, pk)| r == recv && bs == a && *pk == Some(1)) || self.rel_of.get(a).is_some_and(|(r, bs, pk)| r == recv && bs == b && *pk == Some(1)),
            _ => false, } }
    fn resolve_recv(&self, sl: &[Tok]) -> Option<String> {
        match strip_parens(sl) {
            [Tok::Ident(v)] if self.str_vars.contains(v) => Some(v.clone()),
            [Tok::Ident(sf), Tok::Sym("."), Tok::Ident(f)] if sf == "self" && self.self_str_fields.contains(f) => Some(format!("self.{f}")),
            [Tok::Ident(v), Tok::Sym("["), Tok::Ident(rn), Tok::Sym("."), Tok::Ident(cl), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("]")] if cl == "clone" && self.str_vars.contains(v) && self.safe_ranges.get(rn).map(String::as_str) == Some(v.as_str()) => Some(v.clone()),
            _ => None } }
    fn eval_rel_sum(&self, a: &String, b: &String, need_k: Option<i64>, recv: &str, file: &FileIndex) -> bool {
        [(a, b), (b, a)].into_iter().any(|(x, y)| self.rel_of.get(y).is_some_and(|(r, bs, pk)| r == recv && bs == x && need_k.map_or(true, |k| *pk == Some(k))) && self.eval_bound(&[Tok::Ident(x.clone())], recv, file)) }
    fn eval_bound(&self, sl: &[Tok], recv: &str, file: &FileIndex) -> bool {
        let (sl, st_has) = (strip_parens(sl), |k: i64| k == 0 || self.starts.get(recv).is_some_and(|s| s.contains(&k)));
        match sl {
            [] | [Tok::Int(0, _)] => true,
            [Tok::Int(k, _)] => st_has(*k),
            [Tok::Ident(v)] => self.safe_for.get(recv).is_some_and(|s| s.contains(v)) || self.sym_bounds.get(recv).is_some_and(|s| s.contains(v)) || self.local_ints.get(v).is_some_and(|&k| st_has(k)) || file.consts.get(v).is_some_and(|&(k, _)| st_has(k)),
            [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Int(0, _), Tok::Sym(")")] if m == "unwrap_or" => self.safe_for.get(recv).is_some_and(|s| s.contains(v)),
            [rest @ .., Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "len" && self.resolve_recv(rest).as_deref() == Some(recv) => true,
            [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("-"), Tok::Int(k, _)] if v == recv && m == "len" => self.ends.get(recv).is_some_and(|s| s.contains(k)),
            [Tok::Ident(v), Tok::Sym("+"), Tok::Ident(c), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "len_utf8" && !c.is_empty() => self.safe_for.get(recv).is_some_and(|s| s.contains(v)),
            [Tok::Ident(v), Tok::Sym("+"), Tok::Int(k, _)] => self.safe_plus.get(recv).and_then(|m| m.get(v)).is_some_and(|ks| ks.contains(k)),
            [Tok::Ident(v), Tok::Sym("-"), Tok::Int(k, _)] => self.safe_minus.get(recv).and_then(|m| m.get(v)).is_some_and(|ks| ks.contains(k)),
            [Tok::Ident(a), Tok::Sym("+"), Tok::Ident(b)] => self.eval_rel_sum(a, b, None, recv, file),
            [Tok::Ident(a), Tok::Sym("+"), Tok::Ident(b), Tok::Sym("+"), Tok::Int(k, _)] => self.eval_rel_sum(a, b, Some(*k), recv, file),
            [Tok::Ident(rn), Tok::Sym("."), Tok::Ident(s), Tok::Sym("+"), Tok::Ident(b)] if s == "start" => self.safe_ranges.get(rn).is_some_and(|r| r == recv)
                && (self.safe_for.get(recv).is_some_and(|sf| sf.contains(b)) || self.sub_of.iter().any(|(sub, (p, br))| p == recv && br == rn && self.safe_for.get(sub).is_some_and(|sf| sf.contains(b)))),
            _ => {
                if sl.iter().any(|t| matches!(t, Tok::Ident(w) if w == "floor_char_boundary" || w == "ceil_char_boundary")) { return true; }
                let (core, add_k) = match sl.split_last() { Some((&Tok::Int(k, _), r)) if matches!(r.last(), Some(Tok::Sym("+"))) => (r.get(..r.len().saturating_sub(1)).unwrap_or(&[]), Some(k)), _ => (sl, None) };
                let core = core.strip_suffix(&[Tok::Sym("?")]).unwrap_or(core);
                core.iter().rposition(|t| matches!(t, Tok::Sym("."))).is_some_and(|dp| self.resolve_recv(core.get(..dp).unwrap_or(&[])).as_deref() == Some(recv) && matches!(core.get(dp + 1..), Some([Tok::Ident(m), Tok::Sym("("), needle, Tok::Sym(")")]) if (m == "find" || m == "rfind") && add_k.map_or(true, |k| self.str_lit_info(Some(needle), file).is_some_and(|(l, a, _)| a && l as i64 == k))))
            } } }
    fn apply_cond(&mut self, cond: &[Tok], truth: bool, uc: Utf8Ctx<'_>) {
        let cond = strip_parens(cond);
        if let Some(p) = find_top_sym(cond, "||") {
            if !truth { self.apply_cond(cond.get(..p).unwrap_or(&[]), false, uc); self.apply_cond(cond.get(p + 1..).unwrap_or(&[]), false, uc); }
            else if let Some(x) = ascii_guarded_expr(cond, uc.preds) { self.mark_ascii_expr(x); }
            return; }
        if let Some(p) = find_top_sym(cond, "&&") { if truth { self.apply_cond(cond.get(..p).unwrap_or(&[]), true, uc); self.apply_cond(cond.get(p + 1..).unwrap_or(&[]), true, uc); } return; }
        if let Some(p) = find_top_sym(cond, "!=") { if !truth { let mut eq = cond.get(..p).unwrap_or(&[]).to_vec(); eq.push(Tok::Sym("==")); eq.extend_from_slice(cond.get(p + 1..).unwrap_or(&[])); self.apply_cond(&eq, true, uc); } return; }
        if matches!(cond.first(), Some(Tok::Sym("!"))) { self.apply_cond(cond.get(1..).unwrap_or(&[]), !truth, uc); return; }
        if !truth { return; }
        if let Some(x) = ascii_guarded_expr(cond, uc.preds) { self.mark_ascii_expr(x); }
        if let Some(p) = find_top_sym(cond, "==") {
            let (l, r) = (strip_parens(cond.get(..p).unwrap_or(&[])), strip_parens(cond.get(p + 1..).unwrap_or(&[])));
            for (a, b) in [(l, r), (r, l)] {
                if let ([Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")], [Tok::Ident(x), Tok::Sym("+"), Tok::Ident(sc), Tok::Sym("."), Tok::Ident(l2), Tok::Sym("("), Tok::Sym(")")]) = (a, b) {
                    if m == "len" && l2 == "len" && self.str_vars.contains(v) {
                        if self.ends_sym.get(v).is_some_and(|s| s.contains(sc)) { self.sym_bounds.entry(v.clone()).or_default().insert(x.clone()); }
                        self.len_tail_eq.entry(v.clone()).or_default().push((x.clone(), sc.clone())); } }
                if matches!(b, [Tok::Ident(sm), Tok::Sym("("), Tok::Sym("&"), t, Tok::Sym(")")] if sm == "Some" && is_ascii_lit(t)) {
                    match a {
                        [Tok::Ident(v), Tok::Sym("."), Tok::Ident(ab), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("."), Tok::Ident(g), Tok::Sym("("), Tok::Ident(ix), Tok::Sym(")")] if ab == "as_bytes" && g == "get" && self.str_vars.contains(v) => self.mark_safe(v, ix, Some(1), None),
                        [Tok::Ident(bv), Tok::Sym("."), Tok::Ident(g), Tok::Sym("("), Tok::Ident(ix), Tok::Sym(")")] if g == "get" => if let Some(sv) = self.bytes_of.get(bv).cloned() { self.mark_safe(&sv, ix, Some(1), None); }
                        _ => {} }
                } }
            return; }
        match cond {
            [Tok::Ident(v), Tok::Sym("."), Tok::Ident(bm), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("."), Tok::Ident(am), Tok::Sym("("), rest @ .., Tok::Sym(")")] if self.str_vars.contains(v) && bm == "bytes" && am == "all" && is_ascii_iter_pred(rest, uc.preds) => { self.ascii_ok.insert(v.clone()); }
            [Tok::Ident(v), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), rest @ .., Tok::Sym(")")] if self.str_vars.contains(v) => match m.as_str() {
                "is_ascii" => { self.ascii_ok.insert(v.clone()); }
                "is_char_boundary" => match rest { [Tok::Ident(ix)] => self.mark_safe(v, ix, None, None), [Tok::Int(k, _)] => { self.starts.entry(v.clone()).or_default().insert(*k); } _ => {} }
                "starts_with" => if let Some((l, _, _)) = self.str_lit_info(rest.first(), uc.file) { self.starts.entry(v.clone()).or_default().insert(l as i64); }
                "ends_with" => {
                    let sym_nm = if let Some((l, _, sc)) = self.str_lit_info(rest.first(), uc.file) { self.ends.entry(v.clone()).or_default().insert(l as i64); sc } else if let [Tok::Ident(nm)] = rest { Some(nm.clone()) } else { None };
                    if let Some(nm) = sym_nm {
                        self.ends_sym.entry(v.clone()).or_default().insert(nm.clone());
                        for (x, s2) in self.len_tail_eq.get(v).cloned().unwrap_or_default() { if s2 == nm { self.sym_bounds.entry(v.clone()).or_default().insert(x); } } } }
                "eq_ignore_ascii_case" => if let Some((l, true, _)) = self.str_lit_info(rest.first(), uc.file) { self.starts.entry(v.clone()).or_default().insert(l as i64); self.ascii_ok.insert(v.clone()); }
                _ => {} },
            _ => {} } }
    fn witness_of_expr(&self, rhs: &[Tok], uc: Utf8Ctx<'_>) -> Option<Witness> {
        let mut e = strip_parens(rhs);
        if let [base @ .., Tok::Sym("+"), Tok::Int(k, _)] = e { return self.witness_of_expr(base, uc).and_then(|(r, bs, pk, _)| (pk == Some(*k)).then_some((r, bs, None, Some(*k)))); }
        while matches!(e.last(), Some(Tok::Sym("?"))) { e = e.get(..e.len().saturating_sub(1)).unwrap_or(&[]); }
        if let Some(dp) = e.iter().rposition(|t| matches!(t, Tok::Sym("."))) {
            if let Some([Tok::Ident(m), Tok::Sym("("), ..]) = e.get(dp + 1..) {
                if matches!(m.as_str(), "unwrap" | "expect" | "unwrap_or" | "ok_or" | "ok_or_else") {
                    if m == "unwrap_or" && !matches!(e.get(dp + 3..e.len().saturating_sub(1)), Some([Tok::Int(0, _)])) { return None; }
                    e = strip_parens(e.get(..dp).unwrap_or(&[])); }
            } }
        if let Some(dp) = e.iter().rposition(|t| matches!(t, Tok::Sym("."))) {
            if matches!(e.get(dp + 1..dp + 3), Some([Tok::Ident(m), Tok::Sym("(")]) if m == "map_or") && skip_bal(e, dp + 2, e.len(), "(", ")") == e.len() {
                let args = split_top_commas(e.get(dp + 3..e.len().saturating_sub(1)).unwrap_or(&[]), false);
                if let (Some(&[Tok::Int(0, _)]), Some(&[Tok::Sym("|"), Tok::Ident(ref cp), Tok::Sym("|"), ref cbody @ ..])) = (args.first(), args.get(1)) {
                    if let Some((recv, base, pk, _)) = self.witness_of_expr(e.get(..dp).unwrap_or(&[]), uc) {
                        if matches!(strip_parens(cbody), [Tok::Ident(x)] if x == cp) || matches!(strip_parens(cbody), [Tok::Ident(x), Tok::Sym("+"), Tok::Int(k, _)] if x == cp && pk == Some(*k)) { return Some((recv, base, None, None)); } }
                } } }
        if let [Tok::Ident(v), Tok::Sym("."), Tok::Ident(b), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("."), Tok::Ident(tw), Tok::Sym("("), ..] = e {
            if self.str_vars.contains(v) && b == "bytes" && tw == "take_while" {
                let pe = skip_bal(e, 7, e.len(), "(", ")");
                if matches!(e.get(pe..), Some([Tok::Sym("."), Tok::Ident(c), Tok::Sym("("), Tok::Sym(")")]) if c == "count") && is_ascii_iter_pred(e.get(8..pe.saturating_sub(1)).unwrap_or(&[]), uc.preds) { return Some((v.clone(), None, None, None)); }
            } }
        if let Some(dp) = e.iter().rposition(|t| matches!(t, Tok::Sym("."))) {
            if let Some([Tok::Ident(m), Tok::Sym("("), needle @ .., Tok::Sym(")")]) = e.get(dp + 1..) {
                if m == "find" || m == "rfind" {
                    let pk = match needle {
                        [n] => self.str_lit_info(Some(n), uc.file).and_then(|(l, a, _)| a.then_some(l as i64)),
                        [Tok::Sym("&"), Tok::Sym("["), a @ .., Tok::Sym("]")] | [Tok::Sym("["), a @ .., Tok::Sym("]")] if !a.is_empty() && a.iter().all(|t| matches!(t, Tok::Sym("@c" | ","))) => Some(1),
                        _ => None };
                    let rec_sl = strip_parens(e.get(..dp).unwrap_or(&[]));
                    if let Some(r) = self.resolve_recv(rec_sl) { return Some(self.sub_of.get(&r).filter(|(_, b)| !self.safe_ranges.contains_key(b)).map_or((r, None, pk, None), |(p, b)| (p.clone(), Some(b.clone()), pk, None))); }
                    if let [Tok::Ident(v), Tok::Sym("["), Tok::Ident(bs), Tok::Sym(".."), Tok::Sym("]")] = rec_sl { if self.str_vars.contains(v) { return Some((v.clone(), Some(bs.clone()), pk, None)); } } }
            } }
        if let [Tok::Ident(cal), Tok::Sym("("), ..] = e {
            if skip_bal(e, 1, e.len(), "(", ")") == e.len() {
                if let Some(m) = uc.morphs.get(cal) {
                    let args = split_top_commas(e.get(2..e.len().saturating_sub(1)).unwrap_or(&[]), false);
                    let recv = args.get(m.bytes_param).and_then(|a| match strip_parens(a) { [Tok::Ident(bv)] => self.bytes_of.get(bv).cloned(), _ => None })?;
                    if m.req_plus1.map_or(true, |ai| args.get(ai).is_some_and(|a| self.has_plus1(&recv, a))) && m.req_ascii.map_or(true, |ai| args.get(ai).is_some_and(|a| matches!(strip_parens(a), [t] if is_ascii_lit(t)))) && m.req_safe.map_or(true, |ai| args.get(ai).is_some_and(|a| self.eval_bound(a, &recv, uc.file))) {
                        return Some((recv, None, m.ret_plus1.then_some(1), m.ret_minus1.then_some(1))); }
                } } }
        None }
    fn bind_pat(&mut self, dst: &str, rhs: &[Tok], ty: Option<&[Tok]>, uc: Utf8Ctx<'_>) {
        let rhs = strip_parens(rhs);
        let is_str = ty.is_some_and(|t| matches!(t, [Tok::Sym("&"), Tok::Ident(s)] | [Tok::Ident(s)] if s == "str" || s == "String"))
            || (matches!(rhs.last(), Some(Tok::Sym("]"))) && matches!(rhs, [Tok::Sym("&"), Tok::Ident(v), Tok::Sym("["), ..] | [Tok::Ident(v), Tok::Sym("["), ..] if self.str_vars.contains(v)))
            || rhs.windows(2).any(|w| matches!(w, [Tok::Sym("."), Tok::Ident(m)] if m == "as_str"))
            || matches!(rhs.first(), Some(Tok::Ident(v)) if self.str_vars.contains(v) && matches!(rhs.get(1..3), Some([Tok::Sym("."), Tok::Ident(m)]) if matches!(m.as_str(), "trim" | "trim_start" | "trim_end")));
        if is_str {
            self.str_vars.insert(dst.to_string()); self.ascii_ok.remove(dst); self.starts.remove(dst); self.ends.remove(dst);
            if let [Tok::Sym("&"), Tok::Ident(v), Tok::Sym("["), Tok::Ident(bs), Tok::Sym(".."), Tok::Sym("]")] | [Tok::Ident(v), Tok::Sym("["), Tok::Ident(bs), Tok::Sym(".."), Tok::Sym("]")] = rhs { if self.str_vars.contains(v) { self.sub_of.insert(dst.to_string(), (v.clone(), bs.clone())); } }
            else if let [Tok::Sym("&"), Tok::Ident(v), Tok::Sym("["), Tok::Ident(rn), Tok::Sym("."), Tok::Ident(cl), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("]")] | [Tok::Ident(v), Tok::Sym("["), Tok::Ident(rn), Tok::Sym("."), Tok::Ident(cl), Tok::Sym("("), Tok::Sym(")"), Tok::Sym("]")] = rhs { if cl == "clone" && self.str_vars.contains(v) { self.sub_of.insert(dst.to_string(), (v.clone(), rn.clone())); } }
            let src = match rhs { [Tok::Ident(s), Tok::Sym("."), ..] | [Tok::Sym("&"), Tok::Ident(s), Tok::Sym("["), ..] => Some(s), _ => None };
            if src.is_some_and(|s| self.ascii_ok.contains(s)) { self.ascii_ok.insert(dst.to_string()); }
            return; }
        let was_str = self.str_vars.remove(dst); self.ascii_ok.remove(dst); self.starts.remove(dst); self.ends.remove(dst); self.sub_of.remove(dst); self.char_of.remove(dst); self.byte_var.remove(dst);
        match rhs {
            [Tok::Ident(sv), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "as_bytes" && (self.str_vars.contains(sv) || (sv == dst && was_str)) => { self.bytes_of.insert(dst.to_string(), sv.clone()); return; }
            [Tok::Ident(sf), Tok::Sym("."), Tok::Ident(f), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if sf == "self" && m == "as_bytes" && self.self_str_fields.contains(f) => { self.bytes_of.insert(dst.to_string(), format!("self.{f}")); return; }
            [Tok::Ident(bv), Tok::Sym("["), Tok::Ident(ix), Tok::Sym("]")] => if let Some(sv) = self.bytes_of.get(bv).cloned() { self.byte_var.insert(dst.to_string(), (sv, ix.clone())); return; }
            [Tok::Ident(sc), Tok::Sym("."), Tok::Ident(m), Tok::Sym("("), Tok::Sym(")")] if m == "len" => if let Some((l, _, _)) = self.str_lit_info(Some(&Tok::Ident(sc.clone())), uc.file) { self.local_ints.insert(dst.to_string(), l as i64); return; }
            [Tok::Int(v, _)] => { self.local_ints.insert(dst.to_string(), *v); return; }
            [Tok::Ident(n)] if n == "None" => { self.opt_vars.insert(dst.to_string()); return; }
            _ => {} }
        if let Some(w) = self.witness_of_expr(rhs, uc) { self.bind_witness(dst, w); return; }
        match rhs {
            [Tok::Ident(src)] => for (r, pk) in self.safe_for.iter().filter(|(_, s)| s.contains(src)).map(|(r, _)| (r.clone(), self.safe_plus.get(r).and_then(|m| m.get(src)).cloned())).collect::<Vec<_>>() {
                self.mark_safe(&r, dst, None, None); if let Some(ks) = pk { self.safe_plus.entry(r).or_default().entry(dst.to_string()).or_default().extend(ks); } },
            [Tok::Ident(src), Tok::Sym("+"), Tok::Int(k, _)] => for r in self.safe_plus.iter().filter(|(_, m)| m.get(src).is_some_and(|ks| ks.contains(k))).map(|(r, _)| r.clone()).collect::<Vec<_>>() { self.mark_safe(&r, dst, None, None); },
            [Tok::Ident(a), Tok::Sym("+"), Tok::Ident(b)] => if let Some((r, bs, pk)) = self.rel_of.get(b).filter(|(_, bs, _)| bs == a).map(|(r, _, pk)| (r.clone(), a, *pk)).or_else(|| self.rel_of.get(a).filter(|(_, bs, _)| bs == b).map(|(r, _, pk)| (r.clone(), b, *pk))) {
                if self.eval_bound(&[Tok::Ident(bs.clone())], &r, uc.file) { self.mark_safe(&r, dst, pk, None); } },
            [Tok::Ident(rn), Tok::Sym("."), Tok::Ident(s), Tok::Sym("+"), Tok::Ident(rel)] if s == "start" => if let Some(r) = self.safe_ranges.get(rn).cloned() {
                if self.safe_for.get(&r).is_some_and(|sf| sf.contains(rel)) { let pk = self.safe_plus.get(&r).and_then(|m| m.get(rel)).and_then(|ks| ks.iter().next().copied()); self.mark_safe(&r, dst, pk, None); } },
            _ => {} } }
    fn audit_expr(&mut self, sl: &[Tok], uc: Utf8Ctx<'_>, calls: &mut Option<&mut Vec<Utf8CallWitness>>) -> Result<(), VerifyError> {
        let sl = strip_parens(sl);
        if let Some(p) = find_top_sym(sl, "&&") {
            let (l, r) = (sl.get(..p).unwrap_or(&[]), sl.get(p + 1..).unwrap_or(&[]));
            self.audit_expr(l, uc, calls)?; let mut lat2 = self.clone(); lat2.apply_cond(l, true, uc); return lat2.audit_expr(r, uc, calls); }
        let mut i = 0usize;
        while i < sl.len() {
            if matches!(sl.get(i), Some(Tok::Sym("."))) && matches!(sl.get(i + 1), Some(Tok::Ident(m)) if matches!(m.as_str(), "and_then" | "map" | "map_or" | "map_or_else" | "is_some_and")) && matches!(sl.get(i + 2), Some(Tok::Sym("("))) {
                let pe = skip_bal(sl, i + 2, sl.len(), "(", ")");
                if let Some(&[Tok::Sym("|"), Tok::Ident(ref cp), Tok::Sym("|"), ref cbody @ ..]) = split_top_commas(sl.get(i + 3..pe.saturating_sub(1)).unwrap_or(&[]), false).last() {
                    let mut c_lat = self.clone();
                    if let Some(w) = self.witness_of_expr(sl.get(..i).unwrap_or(&[]), uc) { c_lat.bind_witness(cp, w); }
                    c_lat.audit_expr(cbody, uc, calls)?; i = pe; continue; } }
            if matches!(sl.get(i), Some(Tok::Sym("|"))) {
                let mut p2 = i + 1; while p2 < sl.len() && matches!(sl.get(p2), Some(Tok::Ident(_) | Tok::Sym("," | ":" | "&"))) { p2 += 1; }
                if matches!(sl.get(p2..p2 + 2), Some([Tok::Sym("|"), Tok::Sym("{")])) {
                    let be = skip_bal(sl, p2 + 1, sl.len(), "{", "}"); let mut cl = self.clone();
                    cl.audit_block(sl.get(p2 + 2..be.saturating_sub(1)).unwrap_or(&[]), uc, calls)?; self.merge_mut(&cl); i = be; continue; } }
            if let Some(Tok::Ident(v)) = sl.get(i) {
                let is_self_f = i >= 2 && matches!(sl.get(i - 2..i), Some([Tok::Ident(sf), Tok::Sym(".")]) if sf == "self") && self.self_str_fields.contains(v);
                let recv = if is_self_f { Some(format!("self.{v}")) } else if !matches!(sl.get(i.saturating_sub(1)), Some(Tok::Sym("." | "::"))) && self.str_vars.contains(v) { Some(v.clone()) } else { None };
                if let Some(ref rk) = recv {
                    if matches!(sl.get(i + 1), Some(Tok::Sym("["))) {
                        let rng = sl.get(i + 2..skip_bal(sl, i + 1, sl.len(), "[", "]").saturating_sub(1)).unwrap_or(&[]);
                        if let [Tok::Ident(rn), Tok::Sym("."), Tok::Ident(cl), Tok::Sym("("), Tok::Sym(")")] = rng { if cl == "clone" { self.safe_ranges.insert(rn.clone(), rk.clone()); } }
                        else if !self.ascii_ok.contains(rk) { if let Some(rp) = find_top_sym(rng, "..").or_else(|| find_top_sym(rng, "..=")) { if !self.eval_bound(rng.get(..rp).unwrap_or(&[]), rk, uc.file) || !self.eval_bound(rng.get(rp + 1..).unwrap_or(&[]), rk, uc.file) { return Err(VerifyError::Utf8CharBoundary { detail: format!("unchecked &str slice on `{v}` without char-boundary/ASCII proof") }); } } }
                    } else if matches!(sl.get(i + 1..i + 4), Some([Tok::Sym("."), Tok::Ident(m), Tok::Sym("(")]) if m == "split_at") {
                        let arg = sl.get(i + 4..skip_bal(sl, i + 3, sl.len(), "(", ")").saturating_sub(1)).unwrap_or(&[]);
                        if !self.ascii_ok.contains(rk) && !self.eval_bound(arg, rk, uc.file) { return Err(VerifyError::Utf8CharBoundary { detail: format!("unchecked `{v}.split_at(...)` without char-boundary/ASCII proof") }); } } }
                if let Some(ref mut out) = calls {
                    if matches!(sl.get(i + 1), Some(Tok::Sym("("))) && !matches!(v.as_str(), "Some" | "Ok" | "Err" | "if" | "while" | "match" | "for") {
                        let pe = skip_bal(sl, i + 1, sl.len(), "(", ")"); let is_method = matches!(sl.get(i.saturating_sub(1)), Some(Tok::Sym(".")));
                        let qual = if i >= 2 && matches!(sl.get(i - 1), Some(Tok::Sym("::"))) { if let Some(Tok::Ident(q)) = sl.get(i - 2) { Some(q.clone()) } else { None } } else { None };
                        let (mut arg_safe, mut arg_plus1, mut arg_ascii) = (Vec::new(), Vec::new(), Vec::new());
                        for a in split_top_commas(sl.get(i + 2..pe.saturating_sub(1)).unwrap_or(&[]), false) {
                            let a = strip_parens(a); arg_safe.push(matches!(a, [Tok::Int(0, _)]) || self.str_vars.iter().any(|sv| self.eval_bound(a, sv, uc.file)));
                            arg_plus1.push(self.str_vars.iter().any(|sv| self.has_plus1(sv, a)));
                            arg_ascii.push(matches!(a, [Tok::Str(_, true)]) || matches!(a, [Tok::Ident(sv)] if self.ascii_ok.contains(sv))); }
                        out.push(Utf8CallWitness { qual, short: v.clone(), is_method, arg_safe, arg_plus1, arg_ascii }); }
                } }
            i += 1; }
        Ok(()) }
    fn audit_block(&mut self, sl: &[Tok], uc: Utf8Ctx<'_>, calls: &mut Option<&mut Vec<Utf8CallWitness>>) -> Result<(), VerifyError> {
        let diverges = |b: &[Tok]| split_stmts(b).last().is_some_and(|s| matches!(s.first(), Some(Tok::Ident(w)) if matches!(w.as_str(), "return" | "break" | "continue" | "panic" | "unreachable")));
        for st in split_stmts(sl) {
            match st.first() {
                Some(Tok::Ident(w)) if w == "const" => if let (Some(Tok::Ident(nm)), Some(eq)) = (st.get(1), find_top_sym(st, "=")) {
                    match st.get(eq + 1..) { Some(&[Tok::Str(l, a)]) => { self.local_strs.insert(nm.clone(), (l, a)); } Some(&[Tok::Int(v, _)]) => { self.local_ints.insert(nm.clone(), v); } _ => {} } },
                Some(Tok::Ident(w)) if w == "let" => if let Some(eq) = find_top_sym(st, "=") {
                    let (lhs, raw_rhs) = (st.get(1..eq).unwrap_or(&[]), st.get(eq + 1..).unwrap_or(&[]));
                    let (rhs, els_b) = find_top_sym(raw_rhs, "{").filter(|&ep| matches!(raw_rhs.get(ep.saturating_sub(1)), Some(Tok::Ident(e)) if e == "else")).map_or((raw_rhs, None), |ep| (raw_rhs.get(..ep - 1).unwrap_or(&[]), Some(raw_rhs.get(ep + 1..raw_rhs.len().saturating_sub(1)).unwrap_or(&[]))));
                    self.audit_expr(rhs, uc, calls)?;
                    if let Some(eb) = els_b { self.clone().audit_block(eb, uc, calls)?; }
                    let (l_clean, ty) = find_top_sym(lhs, ":").map_or((strip_parens(lhs), None), |cp| (strip_parens(lhs.get(..cp).unwrap_or(&[])), Some(lhs.get(cp + 1..).unwrap_or(&[]))));
                    if let [Tok::Ident(sm), Tok::Sym("("), Tok::Ident(nm), Tok::Sym(")")] = l_clean { if sm == "Some" || sm == "Ok" { self.bind_pat(nm, rhs, None, uc); continue; } }
                    let lp = split_top_commas(l_clean, false);
                    if lp.len() == 2 { if let Some(dp) = rhs.iter().rposition(|t| matches!(t, Tok::Sym("."))) {
                        if matches!(rhs.get(dp + 1..dp + 3), Some([Tok::Ident(m), Tok::Sym("(")]) if m == "split_at") {
                            if let (Some(rk), Some(Tok::Ident(a)), Some(Tok::Ident(b))) = (self.resolve_recv(rhs.get(..dp).unwrap_or(&[])), lp.first().and_then(|s| s.last()), lp.get(1).and_then(|s| s.last())) {
                                let arg = rhs.get(dp + 3..skip_bal(rhs, dp + 2, rhs.len(), "(", ")").saturating_sub(1)).unwrap_or(&[]);
                                let (p1, ac) = (self.has_plus1(&rk, arg), self.ascii_ok.contains(&rk)); self.str_vars.insert(a.clone()); self.str_vars.insert(b.clone());
                                if ac { self.ascii_ok.insert(a.clone()); self.ascii_ok.insert(b.clone()); }
                                if p1 { self.starts.entry(b.clone()).or_default().insert(1); }
                                continue; } }
                    } }
                    if lp.len() > 1 && matches!(rhs.first(), Some(Tok::Sym("("))) {
                        for (l_i, r_i) in lp.into_iter().zip(split_top_commas(strip_parens(rhs), false)) { if let Some(Tok::Ident(nm)) = l_i.iter().rev().find(|t| matches!(t, Tok::Ident(w) if w != "mut")) { self.bind_pat(nm, r_i, None, uc); } }
                    } else if let Some(Tok::Ident(nm)) = l_clean.iter().rev().find(|t| matches!(t, Tok::Ident(w) if w != "mut")) { self.bind_pat(nm, rhs, ty, uc); } },
                Some(Tok::Ident(w)) if w == "if" => if let Some(bs) = find_top_sym(st, "{") {
                    let be = skip_bal(st, bs, st.len(), "{", "}");
                    let (cond, tb, mut tl) = (st.get(1..bs).unwrap_or(&[]), st.get(bs + 1..be.saturating_sub(1)).unwrap_or(&[]), self.clone());
                    let is_let = matches!(cond.first(), Some(Tok::Ident(k)) if k == "let");
                    if is_let { if let Some(eq) = find_top_sym(cond, "=") {
                        let rhs = cond.get(eq + 1..).unwrap_or(&[]); self.audit_expr(rhs, uc, calls)?;
                        if let [Tok::Ident(sm), Tok::Sym("("), Tok::Ident(nm), Tok::Sym(")")] = strip_parens(cond.get(1..eq).unwrap_or(&[])) { if sm == "Some" || sm == "Ok" { tl.bind_pat(nm, rhs, None, uc); } }
                    } } else { self.audit_expr(cond, uc, calls)?; tl.apply_cond(cond, true, uc); }
                    let mut el = self.clone();
                    tl.audit_block(tb, uc, calls)?; self.merge_mut(&tl);
                    if !matches!(st.get(be), Some(Tok::Ident(e)) if e == "else") { if !is_let && diverges(tb) { self.apply_cond(cond, false, uc); } }
                    else {
                        if !is_let { el.apply_cond(cond, false, uc); }
                        if matches!(st.get(be + 1), Some(Tok::Ident(e)) if e == "if") { let old = std::mem::replace(self, el); let r = self.audit_block(st.get(be + 1..).unwrap_or(&[]), uc, calls); let after = std::mem::replace(self, old); self.merge_mut(&after); r?; }
                        else if matches!(st.get(be + 1), Some(Tok::Sym("{"))) {
                            let eb = st.get(be + 2..skip_bal(st, be + 1, st.len(), "{", "}").saturating_sub(1)).unwrap_or(&[]); el.audit_block(eb, uc, calls)?; self.merge_mut(&el);
                            if !is_let { if diverges(tb) && !diverges(eb) { self.apply_cond(cond, false, uc); } else if diverges(eb) && !diverges(tb) { self.apply_cond(cond, true, uc); } } }
                    } },
                Some(Tok::Ident(w)) if matches!(w.as_str(), "while" | "for" | "loop") => if let Some(bs) = find_top_sym(st, "{") {
                    let (hdr, lb) = (st.get(1..bs).unwrap_or(&[]), st.get(bs + 1..skip_bal(st, bs, st.len(), "{", "}").saturating_sub(1)).unwrap_or(&[]));
                    let mut ll = if w == "while" { self.audit_expr(hdr, uc, calls)?; let mut l = self.clone(); l.apply_cond(hdr, true, uc); l }
                    else if w == "for" {
                        if let Some(inp) = hdr.iter().position(|t| matches!(t, Tok::Ident(k) if k == "in")) {
                            let (pat, it) = (strip_parens(hdr.get(..inp).unwrap_or(&[])), hdr.get(inp + 1..).unwrap_or(&[])); self.audit_expr(it, uc, calls)?;
                            let mut l = self.clone();
                            if let ([Tok::Ident(rel), Tok::Sym(","), Tok::Ident(ch)], Some(dp)) = (pat, it.iter().rposition(|t| matches!(t, Tok::Sym(".")))) {
                                if matches!(it.get(dp + 1..dp + 3), Some([Tok::Ident(m), Tok::Sym("(")]) if m == "char_indices") { if let Some(rk) = self.resolve_recv(it.get(..dp).unwrap_or(&[])) { l.mark_safe(&rk, rel, None, None); l.char_of.insert(ch.clone(), (rk, rel.clone())); } }
                            } l
                        } else { self.clone() }
                    } else { self.clone() };
                    ll.audit_block(lb, uc, calls)?; self.merge_mut(&ll); },
                Some(Tok::Ident(w)) if w == "match" => if let Some(bs) = find_top_sym(st, "{") {
                    let scrut = strip_parens(st.get(1..bs).unwrap_or(&[])); self.audit_expr(scrut, uc, calls)?;
                    let scrut_byte = match scrut { [Tok::Ident(bv), Tok::Sym("["), Tok::Ident(ix), Tok::Sym("]")] => self.bytes_of.get(bv).cloned().map(|sv| (sv, ix.clone())), [Tok::Ident(cv)] => self.byte_var.get(cv).cloned(), _ => None };
                    let (arms, mut k) = (st.get(bs + 1..skip_bal(st, bs, st.len(), "{", "}").saturating_sub(1)).unwrap_or(&[]), 0usize);
                    while let Some(fa) = find_top_sym(arms.get(k..).unwrap_or(&[]), "=>").map(|o| k + o) {
                        let (pat, as_, is_blk) = (arms.get(k..fa).unwrap_or(&[]), fa + 1, matches!(arms.get(fa + 1), Some(Tok::Sym("{"))));
                        let ae = if is_blk { skip_bal(arms, as_, arms.len(), "{", "}") } else { find_top_sym(arms.get(as_..).unwrap_or(&[]), ",").map_or(arms.len(), |o| as_ + o) };
                        let mut al = self.clone(); if let Some((ref sv, ref ix)) = scrut_byte { if is_ascii_pat(pat) { al.mark_safe(sv, ix, Some(1), None); } }
                        if is_blk { al.audit_block(arms.get(as_ + 1..ae.saturating_sub(1)).unwrap_or(&[]), uc, calls)?; } else { al.audit_expr(arms.get(as_..ae).unwrap_or(&[]), uc, calls)?; }
                        self.merge_mut(&al); k = if matches!(arms.get(ae), Some(Tok::Sym(","))) { ae + 1 } else { ae }; } },
                _ => if let [Tok::Ident(dst), Tok::Sym("="), rhs @ ..] = st {
                    self.audit_expr(rhs, uc, calls)?;
                    if self.str_vars.contains(dst) { self.bind_pat(dst, rhs, Some(&[Tok::Ident("str".to_string())]), uc); }
                    else if let Some(w) = self.witness_of_expr(rhs, uc) { self.bind_witness(dst, w); }
                    else if let [Tok::Ident(sm), Tok::Sym("("), inner @ .., Tok::Sym(")")] = strip_parens(rhs) {
                        if sm == "Some" {
                            let ok_rs: Vec<String> = self.str_vars.iter().cloned().chain(self.self_str_fields.iter().map(|f| format!("self.{f}"))).filter(|r| self.eval_bound(inner, r, uc.file)).collect();
                            if ok_rs.is_empty() { self.poisoned.insert(dst.clone()); } else { for r in ok_rs { self.mark_safe(&r, dst, None, None); } } }
                    } else if self.opt_vars.contains(dst) || self.local_ints.contains_key(dst) {
                        let ok_rs: Vec<String> = self.str_vars.iter().cloned().chain(self.self_str_fields.iter().map(|f| format!("self.{f}"))).filter(|r| self.eval_bound(rhs, r, uc.file)).collect();
                        if ok_rs.is_empty() { self.poisoned.insert(dst.clone()); self.local_ints.remove(dst); for s in self.safe_for.values_mut() { s.remove(dst); } } else { for r in ok_rs { self.mark_safe(&r, dst, None, None); } } }
                } else { self.audit_expr(st, uc, calls)?; } } }
        Ok(()) } }
fn run_utf8_audit(item: &FnItem, file: &FileIndex, toks: &[Tok], preds: &BTreeSet<String>, morphs: &BTreeMap<String, BoundaryMorphism>, init: &Utf8ParamInit, mut calls: Option<&mut Vec<Utf8CallWitness>>) -> Option<VerifyError> {
    let (_, params, _, body) = fn_sig_params(item, toks)?; let mut lat = WitnessLattice::default();
    for (nm, ty) in &params { if matches!(ty, [Tok::Sym("&"), Tok::Ident(s)] | [Tok::Ident(s)] if s == "str" || s == "String") && !nm.is_empty() { lat.str_vars.insert(nm.clone()); } }
    if let Some(st) = item.self_ty.as_deref().and_then(|n| file.structs.get(n)) { for (f, t) in &st.fields { if matches!(t, FieldTy::Str) { lat.self_str_fields.insert(f.clone()); } } }
    for s in &init.ascii_str { lat.ascii_ok.insert(s.clone()); }
    let str_keys: Vec<String> = lat.str_vars.iter().cloned().chain(lat.self_str_fields.iter().map(|f| format!("self.{f}"))).collect();
    for p in &init.safe { let p1 = init.plus1.contains(p).then_some(1); for sv in &str_keys { lat.mark_safe(sv, p, p1, None); } }
    if lat.str_vars.is_empty() && lat.self_str_fields.is_empty() && calls.is_none() { return None; }
    lat.audit_block(body, Utf8Ctx { file, preds, morphs }, &mut calls).err() }
pub(crate) fn audit_utf8_item(item: &FnItem, file: &FileIndex, toks: &[Tok], preds: &BTreeSet<String>, morphs: &BTreeMap<String, BoundaryMorphism>, init: &Utf8ParamInit) -> Option<VerifyError> { run_utf8_audit(item, file, toks, preds, morphs, init, None) }
pub(crate) fn collect_utf8_call_witnesses(item: &FnItem, file: &FileIndex, toks: &[Tok], preds: &BTreeSet<String>, morphs: &BTreeMap<String, BoundaryMorphism>, init: &Utf8ParamInit) -> Vec<Utf8CallWitness> { let mut out = Vec::new(); let _ = run_utf8_audit(item, file, toks, preds, morphs, init, Some(&mut out)); out }
fn parse_rust_with_poc_params(src: &str, opts: RustFeOptions) -> ParsedPocEntries {
    let (toks, mut entries, mut skipped_raw, mut inlined) = (tokenize_rust(src), Vec::new(), Vec::new(), BTreeSet::new()); let file = scan_file(&toks);
    for item in &file.fns {
        if item.in_mod || is_intrinsic(&item.name) || (opts.skip_cfg_test && item.is_test) { continue; }
        if let Some(p) = lower_fn_item(item, &file, &toks, &mut inlined, opts) { entries.push(p); } else { skipped_raw.push(item.name.clone()); } }
    (file, entries, skipped_raw.into_iter().filter(|n| !inlined.contains(n)).collect()) }
/// Parse Safe-Rust functions from raw `.rs` source into `Program` IR using explicit `RustFeOptions`.
#[must_use] pub fn parse_rust_programs_with_opts(src: &str, opts: RustFeOptions) -> ParsedRustUnit {
    let (_, entries, skipped_non_kernel_fns) = parse_rust_with_poc_params(src, opts); ParsedRustUnit { programs: entries.into_iter().map(|lf| lf.prog).collect(), skipped_non_kernel_fns } }
/// Parse Safe-Rust functions from raw `.rs` source into `Program` IR with default kernel options.
#[must_use] pub fn parse_rust_programs(src: &str) -> ParsedRustUnit { parse_rust_programs_with_opts(src, RustFeOptions::default()) }
fn verify_rust_unit_toks(ridx: usize, file: &str, fidx: &FileIndex, toks: &[Tok], run: (ArchProfile, RefineConfig, RustFeOptions), utf8: (&BTreeSet<String>, &BTreeMap<String, BoundaryMorphism>)) -> (RustProofReport, Vec<(usize, usize, LoweredFn)>, Vec<Utf8Pending>) {
    let ((profile, cfg, opts), (preds, morphs)) = (run, utf8); let (mut entries, mut skipped_raw, mut inlined) = (Vec::new(), Vec::new(), BTreeSet::new());
    for item in &fidx.fns {
        if item.in_mod || is_intrinsic(&item.name) || (opts.skip_cfg_test && item.is_test) { continue; }
        if let Some(p) = lower_fn_item(item, fidx, toks, &mut inlined, opts) { entries.push(p); } else { skipped_raw.push(item.name.clone()); } }
    let skipped_non_kernel_fns: Vec<String> = skipped_raw.into_iter().filter(|n| !inlined.contains(n)).collect();
    let (mut proven, mut failed, mut failed_lf, mut utf8_pend) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for lf in entries {
        let name = lf.prog.name.clone();
        match verify_program(&lf.prog, profile, cfg) {
            Ok(rep) => proven.push((name, rep)),
            Err(error) => {
                let poc_test = extract_poc(&lf, fidx, &error, cfg); failed_lf.push((ridx, failed.len(), lf));
                failed.push(RustFnFailure { fn_name: name, error, poc_test, entrypoint_trace: None }); }
        } }
    if !opts.enforce_reg_budget {
        let skipped_set: BTreeSet<&str> = skipped_non_kernel_fns.iter().map(String::as_str).collect(); let empty = Utf8ParamInit::default();
        for (item_idx, item) in fidx.fns.iter().enumerate() {
            if item.in_mod || item.is_test || !skipped_set.contains(item.name.as_str()) { continue; }
            if let Some(err) = audit_utf8_item(item, fidx, toks, preds, morphs, &empty) {
                utf8_pend.push(Utf8Pending { ridx, fidx: failed.len(), item_idx });
                failed.push(RustFnFailure { fn_name: item.name.clone(), error: err, poc_test: None, entrypoint_trace: None }); }
        } }
    (RustProofReport { file: file.to_string(), proven, failed, suppressed_guarded: Vec::new(), skipped_non_kernel_fns }, failed_lf, utf8_pend) }
/// Parse and formally verify every supported function in a raw `.rs` source string using explicit `RustFeOptions`.
#[must_use] pub fn verify_rust_functions_with_opts(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig, opts: RustFeOptions) -> RustProofReport {
    let mut all_toks = vec![tokenize_rust(src)]; let fidxs = vec![all_toks.first().map_or_else(FileIndex::default, |t| scan_file(t))];
    let (Some(t0), Some(f0)) = (all_toks.first(), fidxs.first()) else { return RustProofReport { file: file.to_string(), proven: Vec::new(), failed: Vec::new(), suppressed_guarded: Vec::new(), skipped_non_kernel_fns: Vec::new() }; };
    let mut preds = BTreeSet::new(); if !opts.enforce_reg_budget { collect_ascii_byte_preds(f0, t0, &mut preds); }
    let morphs = if !opts.enforce_reg_budget { collect_boundary_morphisms(&fidxs, &all_toks, &preds) } else { BTreeMap::new() };
    let (mut rep, fl, utf8_pend) = verify_rust_unit_toks(0, file, f0, t0, (profile, cfg, opts), (&preds, &morphs));
    if opts.interprocedural_reachability && (!fl.is_empty() || !utf8_pend.is_empty()) {
        crate::callgraph::apply_interprocedural_reachability(
            crate::callgraph::CgAuditCtx { dir: None, files: &[], fidxs: &fidxs, failed_lowered: &fl, utf8_pending: &utf8_pend, preds: &preds, morphs: &morphs, skip: &[], skip_cfg_test: opts.skip_cfg_test, profile, cfg },
            &mut all_toks, std::slice::from_mut(&mut rep),); }
    rep }
/// Parse and formally verify every supported function in a raw `.rs` source string.
#[must_use] pub fn verify_rust_functions(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> RustProofReport { verify_rust_functions_with_opts(file, src, profile, cfg, RustFeOptions::default()) }
/// Parse and verify all supported functions across a `.rs` file or crate directory using explicit `RustFeOptions`.
pub fn verify_crate_functions_with_opts(dir: &Path, profile: ArchProfile, cfg: RefineConfig, skip: &[String], opts: RustFeOptions) -> Result<Vec<RustProofReport>, VerifyError> {
    let mut files = Vec::new(); crate::lint_rs::collect_rs_files_opts(dir, skip, opts.skip_cfg_test, &mut files)?; files.sort();
    let (mut all_toks, mut fidxs, mut preds) = (Vec::with_capacity(files.len()), Vec::with_capacity(files.len()), BTreeSet::new());
    for p in &files {
        let src = std::fs::read_to_string(p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?; let toks = tokenize_rust(&src); let fidx = scan_file(&toks);
        if !opts.enforce_reg_budget { collect_ascii_byte_preds(&fidx, &toks, &mut preds); }
        all_toks.push(toks); fidxs.push(fidx); }
    let morphs = if !opts.enforce_reg_budget { collect_boundary_morphisms(&fidxs, &all_toks, &preds) } else { BTreeMap::new() };
    let (mut reports, mut fl_all, mut utf8_all) = (Vec::with_capacity(files.len()), Vec::new(), Vec::new());
    for (ridx, ((p, fidx), toks)) in files.iter().zip(fidxs.iter()).zip(all_toks.iter()).enumerate() {
        let (rep, fl, up) = verify_rust_unit_toks(ridx, &p.display().to_string(), fidx, toks, (profile, cfg, opts), (&preds, &morphs));
        fl_all.extend(fl); utf8_all.extend(up); reports.push(rep); }
    if opts.interprocedural_reachability && (!fl_all.is_empty() || !utf8_all.is_empty()) {
        crate::callgraph::apply_interprocedural_reachability(
            crate::callgraph::CgAuditCtx { dir: Some(dir), files: &files, fidxs: &fidxs, failed_lowered: &fl_all, utf8_pending: &utf8_all, preds: &preds, morphs: &morphs, skip, skip_cfg_test: opts.skip_cfg_test, profile, cfg },
            &mut all_toks, &mut reports,); }
    Ok(reports) }
/// Parse and verify all supported functions across a `.rs` file or crate directory.
pub fn verify_crate_functions(dir: &Path, profile: ArchProfile, cfg: RefineConfig) -> Result<Vec<RustProofReport>, VerifyError> { verify_crate_functions_skip(dir, profile, cfg, &[]) }
/// Parse and verify all supported functions across a `.rs` file or crate directory, skipping named entries.
pub fn verify_crate_functions_skip(dir: &Path, profile: ArchProfile, cfg: RefineConfig, skip: &[String]) -> Result<Vec<RustProofReport>, VerifyError> { verify_crate_functions_with_opts(dir, profile, cfg, skip, RustFeOptions::default()) }
