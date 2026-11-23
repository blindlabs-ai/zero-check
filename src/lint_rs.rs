use std::collections::BTreeMap;
use std::{fs, path::{Path, PathBuf}};
use crate::abstract_eval::VerifyError;

#[cfg(not(miri))] fn clock_start() -> std::time::Instant { std::time::Instant::now() }
#[cfg(not(miri))] fn clock_us(t0: std::time::Instant) -> u64 { t0.elapsed().as_micros() as u64 }
#[cfg(miri)] fn clock_start() -> u64 { 0 }
#[cfg(miri)] fn clock_us(_t0: u64) -> u64 { 0 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity { Error, Warning }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LintKind {
    UnsafeBlock, RawPtrProvenance, Transmute, UncheckedIndex, UninitAccess, ClampCall,
    AllowAttr, ExpectAttr, UnfinishedMacro, ShiftOverflow, DivByZero, NonAscii, UnguardedIndex, UnusedProp, PanicCall,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LintFinding { pub file: String, pub line: usize, pub col: usize, pub severity: Severity, pub kind: LintKind, pub snippet: String }
#[derive(Clone, Debug, Default)]
pub struct LintReport { pub files_scanned: usize, pub lines_scanned: usize, pub bytes_scanned: usize, pub elapsed_us: u64, pub findings: Vec<LintFinding> }
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
        if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            while i < n && bytes[i] != b'\n' { out[i] = b' '; i += 1; }
        } else if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            let mut depth = 1usize; out[i] = b' '; out[i + 1] = b' '; i += 2;
            while i < n && depth > 0 {
                if i + 1 < n && bytes[i] == b'/' && bytes[i + 1] == b'*' { depth += 1; out[i] = b' '; out[i + 1] = b' '; i += 2; }
                else if i + 1 < n && bytes[i] == b'*' && bytes[i + 1] == b'/' { depth -= 1; out[i] = b' '; out[i + 1] = b' '; i += 2; }
                else { if bytes[i] != b'\n' { out[i] = b' '; } i += 1; }
            }
        } else if bytes[i] == b'r' && (i == 0 || !is_ident_byte(bytes[i - 1]) || (matches!(bytes[i - 1], b'b' | b'c') && (i < 2 || !is_ident_byte(bytes[i - 2])))) {
            let mut j = i + 1; while j < n && bytes[j] == b'#' { j += 1; }
            if j < n && bytes[j] == b'"' {
                let hashes = j - (i + 1); for s in &mut out[i..=j] { *s = b' '; } i = j + 1;
                while i < n {
                    if bytes[i] != b'\n' { out[i] = b' '; }
                    if bytes[i] == b'"' && i + hashes < n && bytes[i + 1..=i + hashes].iter().all(|&c| c == b'#') {
                        for s in &mut out[i + 1..=i + hashes] { *s = b' '; } i += hashes + 1; break;
                    }
                    i += 1;
                }
            } else { i += 1; }
        } else if bytes[i] == b'"' {
            out[i] = b' '; i += 1;
            while i < n {
                if bytes[i] == b'\\' && i + 1 < n { out[i] = b' '; if bytes[i + 1] != b'\n' { out[i + 1] = b' '; } i += 2; }
                else { let end = bytes[i] == b'"'; if bytes[i] != b'\n' { out[i] = b' '; } i += 1; if end { break; } }
            }
        } else if bytes[i] == b'\'' {
            if i + 1 < n && bytes[i + 1] == b'\\' {
                out[i] = b' '; out[i + 1] = b' '; i += 2;
                if i < n && bytes[i] != b'\n' { out[i] = b' '; i += 1; }
                while i < n && bytes[i] != b'\'' && bytes[i] != b'\n' { out[i] = b' '; i += 1; }
                if i < n && bytes[i] == b'\'' { out[i] = b' '; i += 1; }
            } else if i + 2 < n && bytes[i + 1] != b'\'' && bytes[i + 1] != b'\n' && bytes[i + 2] == b'\'' {
                out[i] = b' '; out[i + 1] = b' '; out[i + 2] = b' '; i += 3;
            } else { i += 1; }
        } else { i += 1; }
    }
    out
}

fn prev_non_ws(b: &[u8], mut i: usize) -> Option<(usize, u8)> { while i > 0 { i -= 1; if !b[i].is_ascii_whitespace() { return Some((i, b[i])); } } None }
fn next_non_ws(b: &[u8], mut i: usize) -> Option<(usize, u8)> { while i < b.len() { if !b[i].is_ascii_whitespace() { return Some((i, b[i])); } i += 1; } None }

fn is_attr_prefix(b: &[u8], ident_start: usize) -> bool {
    let Some((lb, b'[')) = prev_non_ws(b, ident_start) else { return false; };
    match prev_non_ws(b, lb) { Some((_, b'#')) => true, Some((bang, b'!')) => matches!(prev_non_ws(b, bang), Some((_, b'#'))), _ => false }
}

fn lhs_bit_width(mlines: &[&str], line_idx: usize, op_col: usize) -> u64 {
    let b = mlines[line_idx].as_bytes();
    let Some((mut end, last)) = prev_non_ws(b, op_col) else { return 64; };
    if last == b')' { let p = &mlines[line_idx][..=end]; return if p.contains("u128") || p.contains("i128") { 128 } else { 64 }; }
    let mut start = end + 1; while start > 0 && is_ident_byte(b[start - 1]) { start -= 1; }
    if start > end { return 64; }
    end += 1;
    let tok = &mlines[line_idx][start..end];
    for (suf, w) in [("u128", 128), ("i128", 128), ("u32", 32), ("i32", 32), ("u16", 16), ("i16", 16), ("u8", 8), ("i8", 8)] {
        if tok.ends_with(suf) { return w; }
    }
    if mlines[line_idx.saturating_sub(20)..=line_idx].iter().any(|p| p.contains(tok) && (p.contains("u128") || p.contains("i128"))) { 128 } else { 64 }
}

fn has_nearby_guard(mlines: &[&str], line_idx: usize) -> bool {
    mlines[line_idx.saturating_sub(15)..=line_idx].iter().any(|l| {
        l.contains(".len()") || l.contains("assert") || l.contains("0..") || l.contains(".get(") || l.contains(".min(") || l.contains("if ") || l.contains("while ")
    })
}

struct ScanCtx<'a> { file: &'a str, mlines: &'a [&'a str], out: Vec<LintFinding> }
impl<'a> ScanCtx<'a> {
    fn push(&mut self, line: usize, col: usize, severity: Severity, kind: LintKind, raw: &str) {
        self.out.push(LintFinding { file: self.file.to_string(), line, col: col + 1, severity, kind, snippet: raw.trim().chars().take(96).collect() });
    }
    fn scan_ident(&mut self, tok: &str, start: usize, end: usize, line_idx: usize, raw: &str) {
        let (ml, b, line_no) = (self.mlines[line_idx], self.mlines[line_idx].as_bytes(), line_idx + 1);
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
            "unwrap" | "expect" if matches!(prev_non_ws(b, start), Some((_, b'.'))) && matches!(next_non_ws(b, end), Some((_, b'('))) => self.push(line_no, start, Severity::Warning, LintKind::PanicCall, raw),
            "panic" | "unreachable" if matches!(next_non_ws(b, end), Some((bang, b'!')) if matches!(next_non_ws(b, bang + 1), Some((_, b'(')))) => self.push(line_no, start, Severity::Warning, LintKind::PanicCall, raw),
            "todo" | "unimplemented" if matches!(next_non_ws(b, end), Some((bang, b'!')) if matches!(next_non_ws(b, bang + 1), Some((_, b'(')))) => self.push(line_no, start, Severity::Error, LintKind::UnfinishedMacro, raw),
            "as" => if let Some((star, b'*')) = next_non_ws(b, end) {
                let rest = ml[star + 1..].trim_start();
                if rest.starts_with("const") || rest.starts_with("mut") { self.push(line_no, start, Severity::Error, LintKind::RawPtrProvenance, raw); }
            },
            _ => {
                let kw = matches!(tok, "let" | "const" | "static" | "type" | "struct" | "enum" | "fn" | "pub" | "mut" | "return" | "if" | "else" | "match" | "in" | "where" | "as" | "vec" | "Some" | "Ok" | "Err");
                if end < b.len() && b[end] == b'[' && !kw {
                    if let Some(rel) = ml[end + 1..].find(']') {
                        let inner = ml[end + 1..end + 1 + rel].trim();
                        let simple = inner.is_empty() || inner.contains(';') || inner.contains("..") || inner.contains('&') || inner.contains('%')
                            || inner.bytes().all(|c| c.is_ascii_digit() || c == b'_') || inner.bytes().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_');
                        if !simple && !has_nearby_guard(self.mlines, line_idx) { self.push(line_no, start, Severity::Warning, LintKind::UnguardedIndex, raw); }
                    }
                }
            }
        }
    }
    fn scan_line(&mut self, line_idx: usize, raw: &str) {
        let line_no = line_idx + 1;
        if let Some(col) = raw.as_bytes().iter().position(|&c| c >= 0x80) { self.push(line_no, col, Severity::Error, LintKind::NonAscii, raw); }
        let (ml, b, n, mut i) = (self.mlines[line_idx], self.mlines[line_idx].as_bytes(), self.mlines[line_idx].len(), 0usize);
        while i < n {
            if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let start = i; while i < n && is_ident_byte(b[i]) { i += 1; }
                self.scan_ident(&ml[start..i], start, i, line_idx, raw);
            } else if i + 1 < n && ((b[i] == b'<' && b[i + 1] == b'<') || (b[i] == b'>' && b[i + 1] == b'>')) {
                let op_col = i; i += 2 + usize::from(i + 2 < n && b[i + 2] == b'=');
                if let Some((d0, c)) = next_non_ws(b, i) {
                    if c.is_ascii_digit() {
                        let mut d1 = d0; while d1 < n && b[d1].is_ascii_digit() { d1 += 1; }
                        if (d1 == n || !matches!(b[d1], b'x' | b'X' | b'b' | b'B' | b'o' | b'O' | b'.')) && ml[d0..d1].parse::<u64>().is_ok_and(|sh| sh >= lhs_bit_width(self.mlines, line_idx, op_col)) {
                            self.push(line_no, op_col, Severity::Error, LintKind::ShiftOverflow, raw);
                        }
                    }
                }
            } else if b[i] == b'/' || b[i] == b'%' {
                let op_col = i; i += 1 + usize::from(i + 1 < n && b[i + 1] == b'=');
                if let Some((z, b'0')) = next_non_ws(b, i) {
                    let is_zero = match b.get(z + 1).copied() { None | Some(b'i' | b'u') => true, Some(c) => !c.is_ascii_alphanumeric() && c != b'_' && c != b'.' };
                    if is_zero { self.push(line_no, op_col, Severity::Error, LintKind::DivByZero, raw); }
                }
            } else { i += 1; }
        }
    }
}

fn scan_unused_props(raw_lines: &[&str], mlines: &[&str], ctx: &mut ScanCtx<'_>) {
    let (mut stats, mut decls) = (BTreeMap::<&str, (usize, usize)>::new(), Vec::new());
    for (line_idx, &ml) in mlines.iter().enumerate() {
        let (b, n, mut i, mut prev2, mut prev1) = (ml.as_bytes(), ml.len(), 0usize, "", "");
        while i < n {
            if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let s = i; while i < n && is_ident_byte(b[i]) { i += 1; }
                let tok = &ml[s..i];
                if tok.len() > 1 && tok.starts_with('_') && !tok.starts_with("__") {
                    let e = stats.entry(tok).or_insert((0, 0)); e.0 += 1;
                    if prev1 == "let" || (prev1 == "mut" && prev2 == "let") { e.1 += 1; decls.push((line_idx, s, tok)); }
                }
                prev2 = prev1; prev1 = tok;
            } else { if !b[i].is_ascii_whitespace() { prev2 = ""; prev1 = ""; } i += 1; }
        }
    }
    for (line_idx, col, tok) in decls {
        if stats.get(tok).is_some_and(|&(tot, dec)| tot <= dec) { ctx.push(line_idx + 1, col, Severity::Warning, LintKind::UnusedProp, raw_lines[line_idx]); }
    }
}

/// Scan a single Rust source string in a single linear pass.
#[must_use] pub fn scan_rust_source(file: &str, src: &str) -> LintReport {
    let t0 = clock_start();
    let masked_bytes = mask_rust_source(src.as_bytes());
    let masked = String::from_utf8_lossy(&masked_bytes);
    let (raw_lines, mlines): (Vec<&str>, Vec<&str>) = (src.lines().collect(), masked.lines().collect());
    let mut ctx = ScanCtx { file, mlines: &mlines, out: Vec::new() };
    for (idx, &raw) in raw_lines.iter().enumerate().take(mlines.len()) { ctx.scan_line(idx, raw); }
    scan_unused_props(&raw_lines, &mlines, &mut ctx);
    LintReport { files_scanned: 1, lines_scanned: raw_lines.len(), bytes_scanned: src.len(), elapsed_us: clock_us(t0), findings: ctx.out }
}

pub(crate) fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), VerifyError> {
    if dir.is_file() { out.push(dir.to_path_buf()); return Ok(()); }
    for entry in fs::read_dir(dir).map_err(|e| VerifyError::Io(format!("{}: {e}", dir.display())))? {
        let path = entry.map_err(|e| VerifyError::Io(e.to_string()))?.path();
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if path.is_dir() { if !matches!(name, "target" | ".git") { collect_rs_files(&path, out)?; } }
        else if path.extension().and_then(|s| s.to_str()) == Some("rs") { out.push(path); }
    }
    Ok(())
}

/// Promote kernel-mode panic hazards (`LintKind::PanicCall`) from Warning to hard Error.
pub fn promote_kernel_strict(report: &mut LintReport) {
    for f in &mut report.findings { if f.kind == LintKind::PanicCall { f.severity = Severity::Error; } }
}

/// Recursively scan all `.rs` files under `dir` (or a single `.rs` file) deterministically.
pub fn scan_crate_dir(dir: &Path) -> Result<LintReport, VerifyError> {
    let t0 = clock_start();
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files)?;
    files.sort();
    let mut report = LintReport::default();
    for path in files {
        let text = fs::read_to_string(&path).map_err(|e| VerifyError::Io(format!("{}: {e}", path.display())))?;
        let sub = scan_rust_source(&path.display().to_string(), &text);
        report.files_scanned += sub.files_scanned; report.lines_scanned += sub.lines_scanned;
        report.bytes_scanned += sub.bytes_scanned; report.findings.extend(sub.findings);
    }
    report.elapsed_us = clock_us(t0);
    Ok(report)
}
