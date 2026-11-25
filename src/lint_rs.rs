use std::collections::BTreeMap;
use std::{fs, path::{Path, PathBuf}};
use crate::abstract_eval::VerifyError;
#[cfg(not(miri))] fn clock_start() -> std::time::Instant { std::time::Instant::now() }
#[cfg(not(miri))] fn clock_us(t0: std::time::Instant) -> u64 { t0.elapsed().as_micros() as u64 }
#[cfg(miri)] fn clock_start() -> u64 { 0 }
#[cfg(miri)] fn clock_us(_t0: u64) -> u64 { 0 }
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)] pub struct LintOptions { pub exclude_cfg_test: bool, pub audit_external: bool }
impl LintOptions { #[must_use] pub const fn external_audit() -> Self { Self { exclude_cfg_test: true, audit_external: true } } }
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum Severity { Error, Warning }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LintKind { UnsafeBlock, RawPtrProvenance, Transmute, UncheckedIndex, UninitAccess, ClampCall, AllowAttr, ExpectAttr, UnfinishedMacro, ShiftOverflow, DivByZero, NonAscii, UnguardedIndex, UnusedProp, PanicCall, NegLitUsizeCast }
#[derive(Clone, Debug, PartialEq, Eq)] pub struct LintFinding { pub file: String, pub line: usize, pub col: usize, pub severity: Severity, pub kind: LintKind, pub snippet: String }
#[derive(Clone, Debug, Default)] pub struct LintReport { pub files_scanned: usize, pub lines_scanned: usize, pub bytes_scanned: usize, pub elapsed_us: u64, pub findings: Vec<LintFinding> }
impl LintReport {
    #[must_use] pub fn error_count(&self) -> usize { self.findings.iter().filter(|f| f.severity == Severity::Error).count() }
    #[must_use] pub fn warning_count(&self) -> usize { self.findings.iter().filter(|f| f.severity == Severity::Warning).count() }
    #[must_use] pub fn is_clean(&self) -> bool { self.error_count() == 0 }
}
#[inline] fn is_ident_byte(b: u8) -> bool { b.is_ascii_alphanumeric() || b == b'_' }
/// Replace comments, string literals, raw strings, and char literals with spaces, preserving `\n`.
fn mask_rust_source(bytes: &[u8]) -> Vec<u8> {
    let (n, mut out, mut i) = (bytes.len(), bytes.to_vec(), 0usize);
    while i < n {
        if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'/' { while i < n && bytes[i] != b'\n' { out[i] = b' '; i += 1; } }
        else if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            let mut depth = 1usize; out[i] = b' '; out[i + 1] = b' '; i += 2;
            while i < n && depth > 0 {
                if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'*' { depth += 1; out[i] = b' '; out[i + 1] = b' '; i += 2; }
                else if i + 1 < n && bytes[i] == b'*' && bytes[i + 1] == b'/' { depth -= 1; out[i] = b' '; out[i + 1] = b' '; i += 2; }
                else { if bytes[i] != b'\n' { out[i] = b' '; } i += 1; } }
        } else if bytes[i] == b'r' && (i == 0 || !is_ident_byte(bytes[i - 1]) || (matches!(bytes[i - 1], b'b' | b'c') && (i < 2 || !is_ident_byte(bytes[i - 2])))) {
            let mut j = i + 1; while j < n && bytes[j] == b'#' { j += 1; }
            if j < n && bytes[j] == b'"' {
                let hashes = j - (i + 1); for s in &mut out[i..=j] { *s = b' '; } i = j + 1;
                while i < n {
                    if bytes[i] != b'\n' { out[i] = b' '; }
                    if bytes[i] == b'"' && i + hashes < n && bytes[i + 1..=i + hashes].iter().all(|&c| c == b'#') { for s in &mut out[i + 1..=i + hashes] { *s = b' '; } i += hashes + 1; break; }
                    i += 1; }
            } else { i += 1; }
        } else if bytes[i] == b'"' {
            out[i] = b' '; i += 1;
            while i < n {
                if bytes[i] == b'\\' && i + 1 < n { out[i] = b' '; if bytes[i + 1] != b'\n' { out[i + 1] = b' '; } i += 2; }
                else { let end = bytes[i] == b'"'; if bytes[i] != b'\n' { out[i] = b' '; } i += 1; if end { break; } }
            }
        } else if bytes[i] == b'\'' {
            if i + 1 < n && bytes[i + 1] == b'\\' {
                out[i] = b' '; out[i + 1] = b' '; i += 2; if i < n && bytes[i] != b'\n' { out[i] = b' '; i += 1; }
                while i < n && bytes[i] != b'\'' && bytes[i] != b'\n' { out[i] = b' '; i += 1; }
                if i < n && bytes[i] == b'\'' { out[i] = b' '; i += 1; }
            } else if i + 2 < n && bytes[i + 1] != b'\'' && bytes[i + 1] != b'\n' && bytes[i + 2] == b'\'' { out[i] = b' '; out[i + 1] = b' '; out[i + 2] = b' '; i += 3; }
            else { i += 1; }
        } else { i += 1; } }
    out }
fn prev_non_ws(b: &[u8], mut i: usize) -> Option<(usize, u8)> { while i > 0 { i -= 1; if !b[i].is_ascii_whitespace() { return Some((i, b[i])); } } None }
fn next_non_ws(b: &[u8], mut i: usize) -> Option<(usize, u8)> { while i < b.len() { if !b[i].is_ascii_whitespace() { return Some((i, b[i])); } i += 1; } None }
fn is_attr_prefix(b: &[u8], ident_start: usize) -> bool {
    let Some((lb, b'[')) = prev_non_ws(b, ident_start) else { return false; };
    match prev_non_ws(b, lb) { Some((_, b'#')) => true, Some((bang, b'!')) => matches!(prev_non_ws(b, bang), Some((_, b'#'))), _ => false } }
fn ident_width_in(lines: &[&str], tok: &str) -> Option<u64> {
    for &l in lines {
        let mut r = l;
        while let Some(p) = r.find(tok) {
            let a = &r[p + tok.len()..];
            if (p == 0 || !is_ident_byte(r.as_bytes()[p - 1])) && !a.as_bytes().first().is_some_and(|&c| is_ident_byte(c)) {
                if let Some(ac) = a.trim_start().strip_prefix(':').filter(|s| !s.starts_with(':')) {
                    let ty = ac.trim_start().trim_start_matches('&').trim_start().trim_start_matches("mut").trim_start();
                    match &ty[..ty.bytes().take_while(|&c| is_ident_byte(c)).count()] {
                        "u128" | "i128" => return Some(128), "u64" | "i64" | "usize" | "isize" => return Some(64),
                        "u32" | "i32" => return Some(32), "u16" | "i16" => return Some(16), "u8" | "i8" => return Some(8), _ => {} }
                } }
            r = a; } }
    None }
fn lhs_bit_width(mlines: &[&str], line_idx: usize, op_col: usize) -> u64 {
    let b = mlines[line_idx].as_bytes(); let Some((mut end, mut last)) = prev_non_ws(b, op_col) else { return 64; };
    if last == b']' {
        let (mut d, mut p) = (1usize, end); while p > 0 && d > 0 { p -= 1; if b[p] == b']' { d += 1; } else if b[p] == b'[' { d -= 1; } }
        let Some((ne, nl)) = prev_non_ws(b, p) else { return 64; }; end = ne; last = nl; }
    let mut fn_s = line_idx; while fn_s > 0 && line_idx - fn_s < 80 && !mlines[fn_s].contains("fn ") { fn_s -= 1; }
    let (win, has128) = (&mlines[fn_s..(line_idx + 40).min(mlines.len())], |s: &str| s.contains("u128") || s.contains("i128"));
    let ws = [("u128", 128), ("i128", 128), ("u64", 64), ("i64", 64), ("usize", 64), ("isize", 64), ("u32", 32), ("i32", 32), ("u16", 16), ("i16", 16), ("u8", 8), ("i8", 8)];
    if last == b')' {
        let (p, pt) = (&mlines[line_idx][..=end], mlines[line_idx][..=end].trim_end_matches(')').trim_end());
        for (s, w) in ws { if pt.ends_with(s) && pt[..pt.len() - s.len()].trim_end().ends_with("as") { return w; } }
        return if has128(p) || win.iter().any(|l| has128(l)) { 128 } else { 64 }; }
    let mut start = end + 1; while start > 0 && is_ident_byte(b[start - 1]) { start -= 1; }
    if start > end { return 64; }
    let tok = &mlines[line_idx][start..=end]; for (s, w) in ws { if tok.ends_with(s) { return w; } }
    if tok.as_bytes()[0].is_ascii_digit() { return if has128(mlines[line_idx]) { 128 } else { 64 }; }
    if let Some(w) = ident_width_in(win, tok) { return w; }
    if win.iter().any(|l| has128(l)) || mlines.iter().any(|p| p.contains(tok) && has128(p)) { 128 } else { 64 } }
fn has_nearby_guard(mlines: &[&str], line_idx: usize) -> bool {
    mlines[line_idx.saturating_sub(15)..=line_idx].iter().any(|l| l.contains(".len()") || l.contains("assert") || l.contains("0..") || l.contains(".get(") || l.contains(".min(") || l.contains("if ") || l.contains("while ")) }
fn is_neg_lit_unsigned_cast(ml: &str, as_start: usize, as_end: usize) -> bool {
    let b = ml.as_bytes(); let Some((ts, tc)) = next_non_ws(b, as_end) else { return false; }; if !tc.is_ascii_alphabetic() { return false; }
    let mut te = ts; while te < b.len() && is_ident_byte(b[te]) { te += 1; }
    if !matches!(&ml[ts..te], "usize" | "u64") { return false; }
    let Some((mut p, mut ch)) = prev_non_ws(b, as_start) else { return false; }; let mut parens = 0usize;
    while ch == b')' { parens += 1; let Some((np, nc)) = prev_non_ws(b, p) else { return false; }; p = np; ch = nc; }
    if !is_ident_byte(ch) { return false; }
    let mut ls = p; while ls > 0 && is_ident_byte(b[ls - 1]) { ls -= 1; }
    if !b[ls].is_ascii_digit() || matches!(prev_non_ws(b, ls), Some((_, b'.'))) { return false; }
    let mut body = &ml[ls..=p]; for suf in ["isize", "i128", "i64", "i32", "i16", "i8"] { if let Some(s) = body.strip_suffix(suf) { body = s; break; } }
    let (is_hex, digits) = if let Some(d) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) { (true, d) }
        else { (false, body.strip_prefix("0b").or_else(|| body.strip_prefix("0B")).or_else(|| body.strip_prefix("0o")).or_else(|| body.strip_prefix("0O")).unwrap_or(body)) };
    let ok_d = |c: u8| if is_hex { c.is_ascii_hexdigit() } else { c.is_ascii_digit() };
    if digits.is_empty() || !digits.bytes().all(|c| ok_d(c) || c == b'_') || !digits.bytes().any(|c| ok_d(c) && c != b'0') { return false; }
    let Some((mut anchor, b'-')) = prev_non_ws(b, ls) else { return false; }; for _ in 0..parens { let Some((lp, b'(')) = prev_non_ws(b, anchor) else { return false; }; anchor = lp; }
    let Some((q, qc)) = prev_non_ws(b, anchor) else { return true; }; if matches!(qc, b')' | b']') { return false; }
    if is_ident_byte(qc) { let mut ws = q; while ws > 0 && is_ident_byte(b[ws - 1]) { ws -= 1; } return matches!(&ml[ws..=q], "return" | "else" | "in" | "match" | "if" | "while" | "break"); }
    true }
fn mark_cfg_test_lines(mlines: &[&str]) -> Vec<bool> {
    let (mut out, mut pending, mut depth, mut delim) = (vec![false; mlines.len()], false, 0usize, 0usize);
    for (slot, &ml) in out.iter_mut().zip(mlines) {
        if depth == 0 && (ml.contains("#[test]") || (ml.contains('#') && (ml.contains("cfg(test)") || ml.contains("cfg(kani)") || ml.contains("cfg(all(test")))) { pending = true; }
        if pending || depth > 0 { *slot = true; }
        for &c in ml.as_bytes() {
            if depth > 0 { if c == b'{' { depth += 1; } else if c == b'}' { depth -= 1; } }
            else if pending { match c { b'(' | b'[' => delim += 1, b')' | b']' => delim = delim.saturating_sub(1), b'{' if delim == 0 => { depth = 1; pending = false; } b';' if delim == 0 => pending = false, _ => {} } } } }
    out }
struct ScanCtx<'a> { file: &'a str, mlines: &'a [&'a str], test_lines: &'a [bool], opts: LintOptions, out: Vec<LintFinding> }
impl<'a> ScanCtx<'a> {
    fn push(&mut self, line: usize, col: usize, severity: Severity, kind: LintKind, raw: &str) {
        if self.opts.audit_external && !matches!(kind, LintKind::ShiftOverflow | LintKind::DivByZero | LintKind::NegLitUsizeCast) { return; }
        self.out.push(LintFinding { file: self.file.to_string(), line, col: col + 1, severity, kind, snippet: raw.trim().chars().take(96).collect() }); }
    fn scan_ident(&mut self, tok: &str, start: usize, end: usize, line_idx: usize, raw: &str) {
        let (ml, b, line_no, in_test) = (self.mlines[line_idx], self.mlines[line_idx].as_bytes(), line_idx + 1, self.test_lines.get(line_idx).copied().unwrap_or(false));
        match tok {
            "unsafe" if matches!(next_non_ws(b, end), Some((_, b'{' | b'f' | b'i' | b't' | b'e'))) => self.push(line_no, start, Severity::Error, LintKind::UnsafeBlock, raw),
            "transmute" | "transmute_copy" => self.push(line_no, start, Severity::Error, LintKind::Transmute, raw),
            "from_raw_parts" | "from_raw_parts_mut" | "addr_of_mut" | "drop_in_place" | "from_raw" => self.push(line_no, start, Severity::Error, LintKind::RawPtrProvenance, raw),
            "read" | "write" | "copy" | "copy_nonoverlapping" if ml[..start].trim_end().ends_with("ptr::") => self.push(line_no, start, Severity::Error, LintKind::RawPtrProvenance, raw),
            "get_unchecked" | "get_unchecked_mut" => self.push(line_no, start, Severity::Error, LintKind::UncheckedIndex, raw),
            "assume_init" | "assume_init_read" | "assume_init_ref" | "assume_init_mut" | "uninitialized" | "set_len" => self.push(line_no, start, Severity::Error, LintKind::UninitAccess, raw),
            "clamp" if (matches!(prev_non_ws(b, start), Some((_, b'.'))) || matches!(prev_non_ws(b, start), Some((c, b':')) if matches!(prev_non_ws(b, c), Some((_, b':'))))) && matches!(next_non_ws(b, end), Some((_, b'('))) => self.push(line_no, start, Severity::Error, LintKind::ClampCall, raw),
            "allow" if is_attr_prefix(b, start) && matches!(next_non_ws(b, end), Some((_, b'('))) => self.push(line_no, start, Severity::Error, LintKind::AllowAttr, raw),
            "expect" if is_attr_prefix(b, start) && matches!(next_non_ws(b, end), Some((_, b'('))) => self.push(line_no, start, Severity::Error, LintKind::ExpectAttr, raw),
            "unwrap" | "expect" if !in_test && matches!(prev_non_ws(b, start), Some((_, b'.'))) && matches!(next_non_ws(b, end), Some((_, b'('))) => self.push(line_no, start, Severity::Warning, LintKind::PanicCall, raw),
            "panic" | "unreachable" if !in_test && matches!(next_non_ws(b, end), Some((bang, b'!')) if matches!(next_non_ws(b, bang + 1), Some((_, b'(')))) => self.push(line_no, start, Severity::Warning, LintKind::PanicCall, raw),
            "todo" | "unimplemented" if matches!(next_non_ws(b, end), Some((bang, b'!')) if matches!(next_non_ws(b, bang + 1), Some((_, b'(')))) => self.push(line_no, start, Severity::Error, LintKind::UnfinishedMacro, raw),
            "as" => {
                if let Some((star, b'*')) = next_non_ws(b, end) {
                    let rest = ml[star + 1..].trim_start();
                    if rest.starts_with("const") || rest.starts_with("mut") { self.push(line_no, start, Severity::Error, LintKind::RawPtrProvenance, raw); }
                } else if is_neg_lit_unsigned_cast(ml, start, end) { self.push(line_no, start, Severity::Error, LintKind::NegLitUsizeCast, raw); } }
            _ => {
                let kw = matches!(tok, "let" | "const" | "static" | "type" | "struct" | "enum" | "fn" | "pub" | "mut" | "return" | "if" | "else" | "match" | "in" | "where" | "as" | "vec" | "Some" | "Ok" | "Err");
                if !in_test && end < b.len() && b[end] == b'[' && !kw {
                    if let Some(rel) = ml[end + 1..].find(']') {
                        let inner = ml[end + 1..end + 1 + rel].trim(); let wrap_idx = inner.contains("wrapping_sub(") && !inner.contains('&') && !inner.contains('%');
                        let simple = inner.is_empty() || inner.contains(';') || inner.contains("..") || inner.contains('&') || inner.contains('%') || inner.bytes().all(|c| c.is_ascii_digit() || c == b'_') || inner.bytes().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_');
                        if wrap_idx || (!simple && !has_nearby_guard(self.mlines, line_idx)) { self.push(line_no, start, Severity::Warning, LintKind::UnguardedIndex, raw); } }
                } }
        } }
    fn scan_line(&mut self, line_idx: usize, raw: &str) {
        let line_no = line_idx + 1; if let Some(col) = raw.as_bytes().iter().position(|&c| c >= 0x80) { self.push(line_no, col, Severity::Error, LintKind::NonAscii, raw); }
        let (ml, b, n, mut i) = (self.mlines[line_idx], self.mlines[line_idx].as_bytes(), self.mlines[line_idx].len(), 0usize);
        while i < n {
            if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let start = i; while i < n && is_ident_byte(b[i]) { i += 1; }
                self.scan_ident(&ml[start..i], start, i, line_idx, raw);
            } else if i + 1 < n && ((b[i] == b'<' && b[i + 1] == b'<') || (b[i] == b'>' && b[i + 1] == b'>')) {
                let op_col = i; i += 2 + usize::from(i + 2 < n && b[i + 2] == b'=');
                if let Some((d0, c)) = next_non_ws(b, i) { if c.is_ascii_digit() {
                    let mut d1 = d0; while d1 < n && b[d1].is_ascii_digit() { d1 += 1; }
                    if (d1 == n || !matches!(b[d1], b'x' | b'X' | b'b' | b'B' | b'o' | b'O' | b'.')) && ml[d0..d1].parse::<u64>().is_ok_and(|sh| sh >= lhs_bit_width(self.mlines, line_idx, op_col)) { self.push(line_no, op_col, Severity::Error, LintKind::ShiftOverflow, raw); }
                } }
            } else if b[i] == b'/' || b[i] == b'%' {
                let op_col = i; i += 1 + usize::from(i + 1 < n && b[i + 1] == b'=');
                if let Some((z, b'0')) = next_non_ws(b, i) {
                    if match b.get(z + 1).copied() { None | Some(b'i' | b'u') => true, Some(c) => !c.is_ascii_alphanumeric() && c != b'_' && c != b'.' } { self.push(line_no, op_col, Severity::Error, LintKind::DivByZero, raw); } }
            } else { i += 1; } }
    } }
fn scan_unused_props(raw_lines: &[&str], mlines: &[&str], ctx: &mut ScanCtx<'_>) {
    let (mut stats, mut decls) = (BTreeMap::<&str, (usize, usize)>::new(), Vec::new());
    for (line_idx, &ml) in mlines.iter().enumerate() {
        if ctx.test_lines.get(line_idx).copied().unwrap_or(false) || !ml.contains('_') { continue; }
        let (b, n, mut i, mut prev2, mut prev1) = (ml.as_bytes(), ml.len(), 0usize, "", "");
        while i < n {
            if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let s = i; while i < n && is_ident_byte(b[i]) { i += 1; }
                let tok = &ml[s..i];
                if tok.len() > 1 && tok.starts_with('_') && !tok.starts_with("__") { let e = stats.entry(tok).or_insert((0, 0)); e.0 += 1; if prev1 == "let" || (prev1 == "mut" && prev2 == "let") { e.1 += 1; decls.push((line_idx, s, tok)); } }
                prev2 = prev1; prev1 = tok;
            } else { if !b[i].is_ascii_whitespace() { prev2 = ""; prev1 = ""; } i += 1; } } }
    for (line_idx, col, tok) in decls { if stats.get(tok).is_some_and(|&(tot, dec)| tot <= dec) { ctx.push(line_idx + 1, col, Severity::Warning, LintKind::UnusedProp, raw_lines[line_idx]); } } }
/// Scan a single Rust source string in a single linear pass with explicit mode options.
#[must_use] pub fn scan_rust_source_with_opts(file: &str, src: &str, opts: LintOptions) -> LintReport {
    let (t0, masked_bytes) = (clock_start(), mask_rust_source(src.as_bytes())); let masked = String::from_utf8_lossy(&masked_bytes);
    let (raw_lines, mlines): (Vec<&str>, Vec<&str>) = (src.lines().collect(), masked.lines().collect());
    let (test_lines, skip_tests) = (mark_cfg_test_lines(&mlines), opts.exclude_cfg_test || opts.audit_external);
    let mut ctx = ScanCtx { file, mlines: &mlines, test_lines: &test_lines, opts, out: Vec::new() };
    for (idx, &raw) in raw_lines.iter().enumerate().take(mlines.len()) { if !(skip_tests && test_lines[idx]) { ctx.scan_line(idx, raw); } }
    if !opts.audit_external { scan_unused_props(&raw_lines, &mlines, &mut ctx); }
    LintReport { files_scanned: 1, lines_scanned: raw_lines.len(), bytes_scanned: src.len(), elapsed_us: clock_us(t0), findings: ctx.out } }
#[must_use] pub fn scan_rust_source(file: &str, src: &str) -> LintReport { scan_rust_source_with_opts(file, src, LintOptions::default()) }
fn is_skipped(p: &Path, skip: &[String]) -> bool { skip.iter().any(|s| p.file_name().and_then(|n| n.to_str()) == Some(s.as_str()) || p.ends_with(s)) }
pub(crate) fn collect_rs_files_opts(dir: &Path, skip: &[String], exclude_tests_dir: bool, out: &mut Vec<PathBuf>) -> Result<(), VerifyError> {
    if dir.is_file() { if !is_skipped(dir, skip) { out.push(dir.to_path_buf()); } return Ok(()); }
    for entry in fs::read_dir(dir).map_err(|e| VerifyError::Io(format!("{}: {e}", dir.display())))? {
        let path = entry.map_err(|e| VerifyError::Io(e.to_string()))?.path(); let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if path.is_dir() {
            if !(matches!(name, "target" | ".git") || (exclude_tests_dir && name == "tests")) { collect_rs_files_opts(&path, skip, exclude_tests_dir, out)?; }
        } else if path.extension().and_then(|s| s.to_str()) == Some("rs") && !is_skipped(&path, skip) { out.push(path); } }
    Ok(()) }
/// Promote kernel-mode panic hazards (`LintKind::PanicCall`) from Warning to hard Error.
pub fn promote_kernel_strict(report: &mut LintReport) { for f in &mut report.findings { if f.kind == LintKind::PanicCall { f.severity = Severity::Error; } } }
/// Recursively scan all `.rs` files under `dir` (or a single `.rs` file) with explicit mode options.
pub fn scan_crate_dir_with_opts(dir: &Path, skip: &[String], opts: LintOptions) -> Result<LintReport, VerifyError> {
    let (t0, mut files, mut report) = (clock_start(), Vec::new(), LintReport::default()); collect_rs_files_opts(dir, skip, opts.exclude_cfg_test || opts.audit_external, &mut files)?;
    files.sort();
    for path in files {
        let text = fs::read_to_string(&path).map_err(|e| VerifyError::Io(format!("{}: {e}", path.display())))?; let sub = scan_rust_source_with_opts(&path.display().to_string(), &text, opts);
        report.files_scanned += sub.files_scanned; report.lines_scanned += sub.lines_scanned; report.bytes_scanned += sub.bytes_scanned; report.findings.extend(sub.findings); }
    report.elapsed_us = clock_us(t0); Ok(report) }
pub fn scan_crate_dir(dir: &Path) -> Result<LintReport, VerifyError> { scan_crate_dir_skip(dir, &[]) }
pub fn scan_crate_dir_skip(dir: &Path, skip: &[String]) -> Result<LintReport, VerifyError> { scan_crate_dir_with_opts(dir, skip, LintOptions::default()) }
