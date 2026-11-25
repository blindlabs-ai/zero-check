use std::collections::BTreeSet;
use std::{fs, path::Path};
use crate::abstract_eval::VerifyError;
const SVO_WORDS: &[&str] = &["the", "is", "are", "was", "were", "this", "that", "should", "must", "we", "our"];
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum Ntf1Kind { Forward, Retro, Airlock, Pipe }
#[derive(Clone, Debug, PartialEq, Eq)] pub struct Ntf1Stmt { pub line: usize, pub kind: Ntf1Kind, pub lhs: Vec<String>, pub rhs: Vec<String> }
#[derive(Clone, Debug, PartialEq, Eq)] pub struct Ntf1Doc { pub module: Option<String>, pub stmts: Vec<Ntf1Stmt> }
crate::define_errors!(pub Ntf1Error {
    NonAscii { line: usize, col: usize } => ("ntf1 non-ASCII byte at {line}:{col}"),
    MissingHeader => ("ntf1 missing NTF1 header"),
    SvoTax { line: usize, word: String } => ("ntf1 SVO grammar tax at line {line}: '{word}'"),
    Syntax { line: usize, detail: String } => ("ntf1 syntax error at line {line}: {detail}"),
    DanglingMorphism { line: usize } => ("ntf1 dangling morphism at line {line}"),
    UncoveredFault { fault: String } => ("ntf1 uncovered fault without -t trap: {fault}"),
    BrokenAirlock { line: usize, detail: String } => ("ntf1 broken 0t airlock at line {line}: {detail}"),
    EmptySpec => ("ntf1 spec contains zero statements"),
});
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ntf1Report { pub file: String, pub module: Option<String>, pub forward_count: usize, pub retro_count: usize, pub airlock_count: usize, pub pipe_count: usize, pub faults_covered: usize, pub canonical_idempotent: bool }
fn is_valid_atom(s: &str) -> bool {
    !s.is_empty() && !matches!(s, "+t" | "-t" | "0t" | "->" | "<-" | "><" | "|>")
        && ((s.len() >= 2 && s.starts_with('"') && s.ends_with('"')) || s.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b':' | b'/' | b'@' | b'=' | b'-'))) }
/// Reject English SVO filler words outside `"..."` literals (including inside `#` comments).
pub fn check_svo_tax(src: &str) -> Result<(), Ntf1Error> {
    for (idx, raw) in src.lines().enumerate() {
        let (b, n, mut i, mut q) = (raw.as_bytes(), raw.len(), 0usize, false);
        while i < n {
            if q { if b[i] == b'\\' && i + 1 < n { i += 2; continue; } else if b[i] == b'"' { q = false; } i += 1; }
            else if b[i] == b'"' { q = true; i += 1; }
            else if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let s = i; while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; }
                if SVO_WORDS.contains(&raw[s..i].to_ascii_lowercase().as_str()) { return Err(Ntf1Error::SvoTax { line: idx + 1, word: raw[s..i].to_string() }); }
            } else { i += 1; } } }
    Ok(()) }
fn split_line_stmts(raw: &str) -> Vec<&str> {
    let (b, n, mut i, mut q, mut seg_s, mut out) = (raw.as_bytes(), raw.len(), 0usize, false, 0usize, Vec::new());
    while i < n {
        if q { if b[i] == b'\\' && i + 1 < n { i += 2; continue; } else if b[i] == b'"' { q = false; } }
        else if b[i] == b'"' { q = true; } else if b[i] == b'#' { break; }
        else if b[i] == b';' { out.push(raw[seg_s..i].trim()); seg_s = i + 1; }
        i += 1; }
    out.push(raw[seg_s..i].trim()); out }
fn tokenize_seg(seg: &str, line: usize) -> Result<Vec<String>, Ntf1Error> {
    let (b, n, mut i, mut toks) = (seg.as_bytes(), seg.len(), 0usize, Vec::new());
    while i < n {
        while i < n && b[i].is_ascii_whitespace() { i += 1; }
        if i >= n { break; }
        let s = i;
        if b[i] == b'"' {
            i += 1; while i < n && b[i] != b'"' { i += if b[i] == b'\\' && i + 1 < n { 2 } else { 1 }; }
            if i >= n { return Err(Ntf1Error::Syntax { line, detail: "unterminated quote".into() }); }
            i += 1;
        } else { while i < n && !b[i].is_ascii_whitespace() { i += 1; } }
        toks.push(seg[s..i].to_string()); }
    Ok(toks) }
fn parse_pipe(toks: &[String], line: usize) -> Result<Vec<String>, Ntf1Error> {
    if toks.is_empty() || toks.len() % 2 == 0 { return Err(Ntf1Error::Syntax { line, detail: "malformed pipeline".into() }); }
    let mut out = Vec::with_capacity(toks.len().div_ceil(2));
    for (idx, t) in toks.iter().enumerate() {
        if idx % 2 == 0 {
            if !is_valid_atom(t) { return Err(Ntf1Error::Syntax { line, detail: format!("invalid atom '{t}'") }); }
            out.push(t.clone());
        } else if t != "|>" { return Err(Ntf1Error::Syntax { line, detail: format!("expected '|>' got '{t}'") }); } }
    Ok(out) }
/// Parse 7-bit ASCII NTF1 v1 source into a validated AST.
pub fn parse_ntf1(src: &str) -> Result<Ntf1Doc, Ntf1Error> {
    for (idx, raw) in src.lines().enumerate() { if let Some(col) = raw.as_bytes().iter().position(|&c| c >= 0x80) { return Err(Ntf1Error::NonAscii { line: idx + 1, col: col + 1 }); } }
    check_svo_tax(src)?; let (mut saw_header, mut module, mut stmts) = (false, None, Vec::new());
    for (idx, raw) in src.lines().enumerate() {
        let line = idx + 1;
        for seg in split_line_stmts(raw) {
            if seg.is_empty() { continue; }
            let toks = tokenize_seg(seg, line)?;
            if !saw_header {
                if toks.first().map(String::as_str) != Some("NTF1") || toks.len() > 2 { return Err(Ntf1Error::MissingHeader); }
                if let Some(m) = toks.get(1) { if !is_valid_atom(m) { return Err(Ntf1Error::Syntax { line, detail: format!("bad header '{m}'") }); } module = Some(m.clone()); }
                saw_header = true; continue; }
            match toks[0].as_str() {
                "+t" | "-t" | "0t" => {
                    let (kind, sep) = match toks[0].as_str() { "+t" => (Ntf1Kind::Forward, "->"), "-t" => (Ntf1Kind::Retro, "<-"), _ => (Ntf1Kind::Airlock, "><") };
                    let mk_err = || if kind == Ntf1Kind::Airlock { Ntf1Error::BrokenAirlock { line, detail: "0t requires ><".into() } } else { Ntf1Error::DanglingMorphism { line } };
                    let pos = toks[1..].iter().position(|t| t == sep).ok_or_else(mk_err)?; let (lt, rt) = (&toks[1..1 + pos], &toks[2 + pos..]);
                    if lt.is_empty() || rt.is_empty() { return Err(mk_err()); }
                    stmts.push(Ntf1Stmt { line, kind, lhs: parse_pipe(lt, line)?, rhs: parse_pipe(rt, line)? }); }
                _ => {
                    let stages = parse_pipe(&toks, line)?; if stages.len() < 2 { return Err(Ntf1Error::Syntax { line, detail: "standalone atom needs |>".into() }); }
                    stmts.push(Ntf1Stmt { line, kind: Ntf1Kind::Pipe, lhs: stages, rhs: Vec::new() }); }
            } } }
    if !saw_header { return Err(Ntf1Error::MissingHeader); }
    Ok(Ntf1Doc { module, stmts }) }
/// Emit canonical NTF1 v1 text (idempotent fixed-point under `parse_ntf1`).
#[must_use] pub fn emit_ntf1(doc: &Ntf1Doc) -> String {
    let mut out = doc.module.as_ref().map_or_else(|| String::from("NTF1\n"), |m| format!("NTF1 {m}\n"));
    for s in &doc.stmts {
        let (l, r) = (s.lhs.join(" |> "), s.rhs.join(" |> "));
        let row = match s.kind { Ntf1Kind::Forward => format!("+t {l} -> {r}\n"), Ntf1Kind::Retro => format!("-t {l} <- {r}\n"), Ntf1Kind::Airlock => format!("0t {l} >< {r}\n"), Ntf1Kind::Pipe => format!("{l}\n") };
        out.push_str(&row); }
    out }
/// Fail-closed NTF1 v1 verifier: syntax, SVO tax, retro-causal completeness, 0t grounding, and canonical idempotence.
pub fn verify_ntf1_source(file: &str, src: &str) -> Result<Ntf1Report, Ntf1Error> {
    let doc = parse_ntf1(src)?; if doc.stmts.is_empty() { return Err(Ntf1Error::EmptySpec); }
    let (mut grounded, mut faults_seen, mut faults_guarded) = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new()); let (mut fwd, mut ret, mut air, mut pip) = (0usize, 0usize, 0usize, 0usize);
    for s in &doc.stmts {
        for a in s.lhs.iter().chain(s.rhs.iter()) { if a.starts_with("Fault.") { faults_seen.insert(a.as_str()); } }
        match s.kind {
            Ntf1Kind::Forward => { fwd += 1; grounded.extend(s.lhs.iter().chain(s.rhs.iter()).map(String::as_str)); }
            Ntf1Kind::Retro => { ret += 1; faults_guarded.extend(s.lhs.iter().map(String::as_str)); grounded.extend(s.lhs.iter().chain(s.rhs.iter()).map(String::as_str)); }
            Ntf1Kind::Pipe => { pip += 1; grounded.extend(s.lhs.iter().map(String::as_str)); }
            Ntf1Kind::Airlock => { air += 1; } } }
    for f in &faults_seen { if !faults_guarded.contains(f) { return Err(Ntf1Error::UncoveredFault { fault: (*f).to_string() }); } }
    for s in &doc.stmts {
        if s.kind == Ntf1Kind::Airlock && s.lhs != s.rhs && (!s.lhs.iter().all(|a| grounded.contains(a.as_str())) || !s.rhs.iter().all(|a| grounded.contains(a.as_str()))) {
            return Err(Ntf1Error::BrokenAirlock { line: s.line, detail: "ungrounded airlock endpoint".into() }); } }
    let reparsed = parse_ntf1(&emit_ntf1(&doc))?;
    let same = reparsed.module == doc.module && reparsed.stmts.len() == doc.stmts.len() && reparsed.stmts.iter().zip(&doc.stmts).all(|(a, b)| a.kind == b.kind && a.lhs == b.lhs && a.rhs == b.rhs);
    if !same { return Err(Ntf1Error::BrokenAirlock { line: 1, detail: "non-idempotent canonical emit".into() }); }
    Ok(Ntf1Report { file: file.to_string(), module: doc.module, forward_count: fwd, retro_count: ret, airlock_count: air, pipe_count: pip, faults_covered: faults_seen.len(), canonical_idempotent: same }) }
/// Read and verify an `.ntf1` spec file on disk.
pub fn verify_ntf1_file(path: &Path) -> Result<Ntf1Report, VerifyError> {
    let text = fs::read_to_string(path).map_err(|e| VerifyError::Io(format!("{}: {e}", path.display())))?;
    verify_ntf1_source(&path.display().to_string(), &text).map_err(|e| VerifyError::Ntf1Violation(e.to_string())) }
