use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};
use crate::abstract_eval::VerifyError;
use crate::lint_rs::collect_rs_files_opts;
pub const DEFAULT_AMD_ZEN_EPYC_SPEC: &str = include_str!("../specs/amd_zen_epyc.spec");
#[cfg(not(miri))] fn perf_clock_start() -> std::time::Instant { std::time::Instant::now() }
#[cfg(not(miri))] fn perf_clock_us(t0: std::time::Instant) -> u64 { t0.elapsed().as_micros() as u64 }
#[cfg(miri)] fn perf_clock_start() -> u64 { 0 }
#[cfg(miri)] fn perf_clock_us(_t0: u64) -> u64 { 0 }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CpuProfile {
    pub name: String, pub family: u32, pub models: Vec<(u32, u32)>,
    pub l1d_kib: usize, pub l1d_ways: usize, pub l2_kib: usize,
    pub l3_ccx_mib: usize, pub l3_3dv_mib: usize, pub ccx_cores: usize,
    pub line_bytes: usize, pub simd: String, pub vec_regs: usize,
    pub vec_bits: usize, pub native_pipe_bits: usize,
}
impl CpuProfile {
    #[must_use] pub fn l1d_bytes(&self) -> usize { self.l1d_kib.saturating_mul(1024) }
    #[must_use] pub fn l2_bytes(&self) -> usize { self.l2_kib.saturating_mul(1024) }
    #[must_use] pub fn l3_ccx_bytes(&self) -> usize { self.l3_ccx_mib.saturating_mul(1024 * 1024) }
    #[must_use] pub fn matches_family_model(&self, family: u32, model: u32) -> bool {
        self.family == family && self.models.iter().any(|&(lo, hi)| model >= lo && model <= hi)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PerfRule { Perf01, Perf02, Perf03, Perf04, Perf05, Perf06 }
impl PerfRule {
    #[must_use] pub const fn code(self) -> &'static str {
        match self {
            Self::Perf01 => "PERF-01", Self::Perf02 => "PERF-02", Self::Perf03 => "PERF-03",
            Self::Perf04 => "PERF-04", Self::Perf05 => "PERF-05", Self::Perf06 => "PERF-06",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PerfSeverity { Low, Medium, High }
impl PerfSeverity {
    #[must_use] pub const fn as_str(self) -> &'static str {
        match self { Self::Low => "LOW", Self::Medium => "MEDIUM", Self::High => "HIGH" }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PerfOptions { pub exclude_cfg_test: bool }
impl Default for PerfOptions {
    fn default() -> Self { Self { exclude_cfg_test: true } }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerfFinding {
    pub file: String, pub line: usize, pub fn_name: String, pub rule: PerfRule,
    pub severity: PerfSeverity, pub cache_bytes: usize, pub impact_score: u64,
    pub compounding_path: String, pub detail: String, pub fix: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProfileResidencyRow {
    pub profile_name: String, pub l1d_kib: usize, pub l2_kib: usize,
    pub l1d_cliffs: usize, pub l2_overflows: usize,
}

#[derive(Clone, Debug)]
pub struct PerfReport {
    pub profile: CpuProfile, pub files_scanned: usize, pub lines_scanned: usize,
    pub fns_scanned: usize, pub edges_scanned: usize, pub elapsed_us: u64,
    pub findings: Vec<PerfFinding>, pub profile_comparison: Vec<ProfileResidencyRow>,
    pub bench_telemetry: Vec<String>,
}

impl PerfReport {
    #[must_use] pub fn high_count(&self) -> usize {
        self.findings.iter().filter(|f| f.severity == PerfSeverity::High).count()
    }
    #[must_use] pub fn format_report(&self, max_hotspots: usize) -> String {
        let mut s = String::new();
        let _ = writeln!(
            s,
            "[PERF-CPU] profile={} family={} l1d={}KiB({}w) l2={}KiB l3_ccx={}MiB line={}B simd={} vec={}x{}b pipe={}b",
            self.profile.name, self.profile.family, self.profile.l1d_kib, self.profile.l1d_ways,
            self.profile.l2_kib, self.profile.l3_ccx_mib, self.profile.line_bytes, self.profile.simd,
            self.profile.vec_regs, self.profile.vec_bits, self.profile.native_pipe_bits
        );
        for f in &self.findings {
            let _ = writeln!(
                s, "  [{}][{}] {}:{} fn={} cache={}B score={} path={} | {} | fix: {}",
                f.rule.code(), f.severity.as_str(), f.file, f.line, f.fn_name,
                f.cache_bytes, f.impact_score, f.compounding_path, f.detail, f.fix
            );
        }
        let _ = writeln!(
            s, "[PERF-06] Top Compounding Hotspots (total={} high={} fns={} edges={} wall={:.3}ms):",
            self.findings.len(), self.high_count(), self.fns_scanned, self.edges_scanned,
            (self.elapsed_us as f64) / 1000.0
        );
        for (idx, f) in self.findings.iter().take(max_hotspots).enumerate() {
            let l1_pct = f.cache_bytes.saturating_mul(100) / self.profile.l1d_bytes().max(1);
            let l2_pct = f.cache_bytes.saturating_mul(100) / self.profile.l2_bytes().max(1);
            let _ = writeln!(
                s, "  #{:02} {} [{}] score={} {}:{} fn={} path={} est_l1_l2={}B({}%L1D/{}%L2) fix={}",
                idx + 1, f.rule.code(), f.severity.as_str(), f.impact_score, f.file, f.line,
                f.fn_name, f.compounding_path, f.cache_bytes, l1_pct, l2_pct, f.fix
            );
        }
        if !self.profile_comparison.is_empty() {
            let parts: Vec<String> = self.profile_comparison.iter().map(|r| {
                format!("{}({}K/{}K):l1_cliffs={},l2_spill={}", r.profile_name, r.l1d_kib, r.l2_kib, r.l1d_cliffs, r.l2_overflows)
            }).collect();
            let _ = writeln!(s, "[PERF-PROFILE-CMP] {}", parts.join(" | "));
        }
        for line in &self.bench_telemetry { let _ = writeln!(s, "[PERF-BENCH] {line}"); }
        s
    }
}

fn parse_models(v: &str) -> Result<Vec<(u32, u32)>, VerifyError> {
    let mut out = Vec::new();
    for part in v.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        if let Some((a, b)) = part.split_once("..") {
            let lo = a.trim().parse::<u32>().map_err(|e| VerifyError::Io(format!("bad model lo '{a}': {e}")))?;
            let hi = b.trim().parse::<u32>().map_err(|e| VerifyError::Io(format!("bad model hi '{b}': {e}")))?;
            out.push((lo.min(hi), lo.max(hi)));
        } else {
            let m = part.parse::<u32>().map_err(|e| VerifyError::Io(format!("bad model '{part}': {e}")))?;
            out.push((m, m));
        }
    }
    Ok(out)
}

fn finish_profile(name: String, kv: &BTreeMap<String, String>) -> Result<CpuProfile, VerifyError> {
    let gu = |k: &str| -> Result<usize, VerifyError> {
        kv.get(k)
            .ok_or_else(|| VerifyError::Io(format!("profile '{name}' missing '{k}'")))?
            .parse::<usize>()
            .map_err(|e| VerifyError::Io(format!("profile '{name}' bad '{k}': {e}")))
    };
    let p = CpuProfile {
        family: gu("family")? as u32, models: parse_models(kv.get("models").map_or("", String::as_str))?,
        l1d_kib: gu("l1d_kib")?, l1d_ways: gu("l1d_ways")?, l2_kib: gu("l2_kib")?,
        l3_ccx_mib: gu("l3_ccx_mib")?, l3_3dv_mib: gu("l3_3dv_mib")?, ccx_cores: gu("ccx_cores")?,
        line_bytes: gu("line_bytes")?,
        simd: kv.get("simd").cloned().ok_or_else(|| VerifyError::Io(format!("profile '{name}' missing 'simd'")))?,
        vec_regs: gu("vec_regs")?, vec_bits: gu("vec_bits")?, native_pipe_bits: gu("native_pipe_bits")?, name,
    };
    if p.l1d_kib == 0 || p.l2_kib == 0 || p.line_bytes == 0 {
        return Err(VerifyError::Io(format!("profile '{}' has zero cache parameter", p.name)));
    }
    Ok(p)
}

pub fn parse_cpu_spec(src: &str) -> Result<Vec<CpuProfile>, VerifyError> {
    let (mut out, mut cur, mut kv) = (Vec::new(), None::<String>, BTreeMap::new());
    for raw in src.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() { continue; }
        if let Some(sec) = line.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            if let Some(prev) = cur.take() { out.push(finish_profile(prev, &kv)?); kv.clear(); }
            cur = Some(sec.trim().to_string());
        } else if let Some((k, v)) = line.split_once('=') {
            kv.insert(k.trim().to_string(), v.trim().to_string());
        }
    }
    if let Some(prev) = cur { out.push(finish_profile(prev, &kv)?); }
    if out.is_empty() { return Err(VerifyError::Io("empty cpu spec".to_string())); }
    Ok(out)
}

fn parse_size_kib(raw: &str) -> Option<usize> {
    let s = raw.trim();
    if let Some(k) = s.strip_suffix('K') { k.trim().parse().ok() }
    else if let Some(m) = s.strip_suffix('M') { m.trim().parse::<usize>().ok().map(|v| v.saturating_mul(1024)) }
    else { s.parse::<usize>().ok().map(|v| v / 1024) }
}

#[must_use]
pub fn detect_host_cpu_profile(profiles: &[CpuProfile]) -> CpuProfile {
    let (mut fam, mut model) = (None::<u32>, None::<u32>);
    if let Ok(info) = fs::read_to_string("/proc/cpuinfo") {
        for line in info.lines() {
            if let Some((k, v)) = line.split_once(':') {
                let (kt, vt) = (k.trim(), v.trim());
                if fam.is_none() && kt == "cpu family" { fam = vt.parse().ok(); }
                else if model.is_none() && kt == "model" { model = vt.parse().ok(); }
                if fam.is_some() && model.is_some() { break; }
            }
        }
    }
    let (mut l1d_kib, mut l1d_ways, mut l2_kib, mut line_bytes) = (None, None, None, None);
    for idx in 0..8 {
        let base = format!("/sys/devices/system/cpu/cpu0/cache/index{idx}");
        let Ok(lvl) = fs::read_to_string(format!("{base}/level")) else { continue; };
        let ty = fs::read_to_string(format!("{base}/type")).unwrap_or_default();
        let sz = fs::read_to_string(format!("{base}/size")).ok().and_then(|s| parse_size_kib(&s));
        let ways = fs::read_to_string(format!("{base}/ways_of_associativity")).ok().and_then(|s| s.trim().parse().ok());
        let lb = fs::read_to_string(format!("{base}/coherency_line_size")).ok().and_then(|s| s.trim().parse().ok());
        if lvl.trim() == "1" && ty.trim() == "Data" { l1d_kib = sz; l1d_ways = ways; line_bytes = lb; }
        else if lvl.trim() == "2" { l2_kib = sz; }
    }
    let mut best = fam
        .zip(model)
        .and_then(|(f, m)| profiles.iter().find(|p| p.matches_family_model(f, m)).cloned())
        .or_else(|| l1d_kib.zip(l2_kib).and_then(|(l1, l2)| profiles.iter().find(|p| p.l1d_kib == l1 && p.l2_kib == l2).cloned()))
        .or_else(|| profiles.iter().find(|p| p.name == "zen2_rome").cloned())
        .or_else(|| profiles.first().cloned())
        .unwrap_or(CpuProfile {
            name: "zen2_rome".to_string(), family: 23, models: vec![(113, 113)], l1d_kib: 32, l1d_ways: 8,
            l2_kib: 512, l3_ccx_mib: 16, l3_3dv_mib: 0, ccx_cores: 4, line_bytes: 64,
            simd: "avx2".to_string(), vec_regs: 16, vec_bits: 256, native_pipe_bits: 256,
        });
    if let Some(v) = l1d_kib.filter(|&v| v > 0) { best.l1d_kib = v; }
    if let Some(v) = l1d_ways.filter(|&v| v > 0) { best.l1d_ways = v; }
    if let Some(v) = l2_kib.filter(|&v| v > 0) { best.l2_kib = v; }
    if let Some(v) = line_bytes.filter(|&v| v > 0) { best.line_bytes = v; }
    best
}

pub fn resolve_cpu_profile(cpu: &str, spec_path: Option<&Path>) -> Result<(CpuProfile, Vec<CpuProfile>), VerifyError> {
    let src = match spec_path {
        Some(p) => fs::read_to_string(p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?,
        None => DEFAULT_AMD_ZEN_EPYC_SPEC.to_string(),
    };
    let profiles = parse_cpu_spec(&src)?;
    let chosen = if cpu == "auto" { detect_host_cpu_profile(&profiles) } else {
        profiles.iter().find(|p| p.name == cpu).cloned().ok_or_else(|| {
            let names: Vec<&str> = profiles.iter().map(|p| p.name.as_str()).collect();
            VerifyError::Io(format!("unknown cpu profile '{cpu}' (expected auto or one of: {})", names.join(", ")))
        })?
    };
    Ok((chosen, profiles))
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TK { Id(String), Int(u64, Option<usize>), Sym(&'static str) }
#[derive(Clone, Debug)]
struct LT { k: TK, line: usize }

fn prim_size_align(name: &str) -> Option<(usize, usize)> {
    Some(match name {
        "bool" | "u8" | "i8" => (1, 1), "u16" | "i16" => (2, 2), "u32" | "i32" | "f32" | "char" => (4, 4),
        "u64" | "i64" | "f64" | "usize" | "isize" => (8, 8), "u128" | "i128" => (16, 16), _ => return None,
    })
}

fn lex_rust_lines(src: &str) -> Vec<LT> {
    const MULTI: &[&str] = &[
        "..=", "<<=", ">>=", "..", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=", "/=", "%=", "::",
    ];
    const SINGLE: &[&str] = &["(", ")", "{", "}", "[", "]", ",", ":", ";", "=", "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "!", ".", "#"];
    let (b, n, mut i, mut line, mut out) = (src.as_bytes(), src.len(), 0usize, 1usize, Vec::new());
    while i < n {
        let c = b.get(i).copied().unwrap_or(0);
        if c == b'\n' { line += 1; i += 1; continue; }
        if c.is_ascii_whitespace() { i += 1; continue; }
        let rest = b.get(i..).unwrap_or(&[]);
        if rest.starts_with(b"//") { while i < n && b.get(i) != Some(&b'\n') { i += 1; } continue; }
        if rest.starts_with(b"/*") {
            let mut d = 1usize; i += 2;
            while i < n && d > 0 {
                let sub = b.get(i..).unwrap_or(&[]);
                if b.get(i) == Some(&b'\n') { line += 1; i += 1; }
                else if sub.starts_with(b"/*") { d += 1; i += 2; }
                else if sub.starts_with(b"*/") { d -= 1; i += 2; }
                else { i += 1; }
            }
            continue;
        }
        if c == b'r' && matches!(b.get(i + 1), Some(&b'"' | &b'#')) {
            let (mut k, mut h) = (i + 1, 0usize);
            while b.get(k) == Some(&b'#') { h += 1; k += 1; }
            if b.get(k) == Some(&b'"') {
                k += 1;
                while k < n {
                    if b.get(k) == Some(&b'\n') { line += 1; }
                    if b.get(k) == Some(&b'"') && b.get(k + 1..k + 1 + h).is_some_and(|s| s.iter().all(|&x| x == b'#')) { k += 1 + h; break; }
                    k += 1;
                }
                i = k; continue;
            }
        }
        if c == b'"' || (c == b'b' && b.get(i + 1) == Some(&b'"')) {
            i += 1 + usize::from(c == b'b');
            while i < n {
                let ch = b.get(i).copied().unwrap_or(0);
                if ch == b'\n' { line += 1; i += 1; } else if ch == b'\\' { i = (i + 2).min(n); } else { i += 1; if ch == b'"' { break; } }
            }
            out.push(LT { k: TK::Sym("@"), line }); continue;
        }
        if c == b'\'' || (c == b'b' && b.get(i + 1) == Some(&b'\'')) {
            let p = i + 1 + usize::from(c == b'b');
            if b.get(p) == Some(&b'\\') {
                let mut k = (p + 2).min(n);
                while k < n && !matches!(b.get(k), Some(&b'\'' | &b'\n')) { k += 1; }
                i = if b.get(k) == Some(&b'\'') { k + 1 } else { k };
                out.push(LT { k: TK::Int(0, Some(1)), line }); continue;
            } else if b.get(p + 1) == Some(&b'\'') {
                i = p + 2; out.push(LT { k: TK::Int(0, Some(1)), line }); continue;
            }
            i += 1;
            while i < n && b.get(i).is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'_') { i += 1; }
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let s = i;
            while i < n && b.get(i).is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'_') { i += 1; }
            if let Some(id) = src.get(s..i) { out.push(LT { k: TK::Id(id.to_string()), line }); }
            continue;
        }
        if c.is_ascii_digit() {
            let s = i;
            while i < n && b.get(i).is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'_') { i += 1; }
            if b.get(i) == Some(&b'.') && b.get(i + 1).is_some_and(u8::is_ascii_digit) {
                i += 1;
                while i < n && b.get(i).is_some_and(|x| x.is_ascii_alphanumeric() || *x == b'_') { i += 1; }
                let lit = src.get(s..i).unwrap_or("");
                out.push(LT { k: TK::Int(0, Some(if lit.ends_with("f32") { 4 } else { 8 })), line }); continue;
            }
            let clean: String = src.get(s..i).unwrap_or("").chars().filter(|&ch| ch != '_').collect();
            let (rad, body) = [("0x", 16), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)]
                .into_iter().find_map(|(p, r)| clean.strip_prefix(p).map(|x| (r, x))).unwrap_or((10, clean.as_str()));
            let end = body.find(|ch: char| !ch.is_digit(rad)).unwrap_or(body.len());
            let (digits, suffix) = (body.get(..end).unwrap_or(""), body.get(end..).unwrap_or(""));
            out.push(LT { k: TK::Int(u64::from_str_radix(digits, rad).unwrap_or(0), prim_size_align(suffix).map(|x| x.0)), line });
            continue;
        }
        if let Some(&m) = MULTI.iter().find(|&&m| rest.starts_with(m.as_bytes())) {
            out.push(LT { k: TK::Sym(m), line }); i += m.len();
        } else {
            let sym = SINGLE.iter().copied().find(|x| x.as_bytes().first() == Some(&c)).unwrap_or("@");
            out.push(LT { k: TK::Sym(sym), line }); i += 1;
        }
    }
    out
}

fn skip_pair(toks: &[LT], mut i: usize, open: &str, close: &str) -> usize {
    if !matches!(toks.get(i).map(|t| &t.k), Some(TK::Sym(s)) if *s == open) { return i; }
    let (mut d, is_ang) = (1usize, close == ">"); i += 1;
    while i < toks.len() && d > 0 {
        match toks.get(i).map(|t| &t.k) {
            Some(TK::Sym(s)) if *s == open => d += 1, Some(TK::Sym(s)) if *s == close => d = d.saturating_sub(1),
            Some(TK::Sym(">>")) if is_ang => d = d.saturating_sub(2), _ => {}
        }
        i += 1;
    }
    i
}

fn find_top_sym(toks: &[LT], s: usize, e: usize, target: &str) -> Option<usize> {
    let mut d = 0usize;
    for k in s..e {
        match toks.get(k).map(|x| &x.k) {
            Some(TK::Sym("[" | "(" | "<" | "{")) => d += 1,
            Some(TK::Sym("]" | ")" | ">" | "}")) => d = d.saturating_sub(1),
            Some(TK::Sym(">>")) => d = d.saturating_sub(2),
            Some(TK::Sym(sym)) if d == 0 && *sym == target => return Some(k),
            _ => {}
        }
    }
    None
}

fn eval_const(toks: &[LT], s: usize, e: usize, consts: &BTreeMap<String, (u64, usize)>) -> Option<u64> {
    let mut i = s;
    let atom = |pos: &mut usize| -> Option<u64> {
        match toks.get(*pos).map(|t| &t.k)? {
            TK::Sym("(") => {
                let pe = skip_pair(toks, *pos, "(", ")");
                let v = eval_const(toks, *pos + 1, pe.saturating_sub(1), consts)?;
                *pos = pe; Some(v)
            }
            TK::Int(v, _) => { *pos += 1; Some(*v) }
            TK::Id(nm) => { *pos += 1; consts.get(nm).map(|&(v, _)| v) }
            _ => None,
        }
    };
    let mut acc = atom(&mut i)?;
    while i < e {
        if matches!(toks.get(i).map(|t| &t.k), Some(TK::Id(w)) if w == "as") { i = (i + 2).min(e); continue; }
        let Some(TK::Sym(op)) = toks.get(i).map(|t| &t.k) else { break; };
        if !matches!(*op, "+" | "-" | "*" | "/" | "<<" | ">>") { break; }
        i += 1;
        let rhs = atom(&mut i)?;
        acc = match *op {
            "+" => acc.checked_add(rhs)?, "-" => acc.checked_sub(rhs)?, "*" => acc.checked_mul(rhs)?,
            "/" => acc.checked_div(rhs)?,
            "<<" => u32::try_from(rhs).ok().filter(|&sh| sh < 64).and_then(|sh| acc.checked_shl(sh))?,
            ">>" => u32::try_from(rhs).ok().filter(|&sh| sh < 64).and_then(|sh| acc.checked_shr(sh))?,
            _ => return None,
        };
    }
    Some(acc)
}

fn layout_fields(fields: &[(usize, usize)], repr_c: bool, repr_packed: bool, explicit_align: usize) -> (usize, usize) {
    let mut ordered = fields.to_vec();
    if !repr_c && !repr_packed { ordered.sort_by(|a, b| b.1.cmp(&a.1)); }
    let (mut off, mut max_al) = (0usize, explicit_align.max(1));
    for (sz, al) in ordered {
        let ea = if repr_packed { 1 } else { al.max(1) };
        max_al = max_al.max(ea);
        let r = off.checked_rem(ea).unwrap_or(0);
        if r != 0 { off = off.saturating_add(ea - r); }
        off = off.saturating_add(sz);
    }
    let total = if repr_packed { off } else { let r = off.checked_rem(max_al).unwrap_or(0); if r == 0 { off } else { off.saturating_add(max_al - r) } };
    (total, max_al)
}

fn infer_val_layout(toks: &[LT], pos: usize, consts: &BTreeMap<String, (u64, usize)>, structs: &BTreeMap<String, (usize, usize, bool)>) -> Option<(usize, usize, bool)> {
    match toks.get(pos).map(|t| &t.k)? {
        TK::Int(_, Some(sz)) => Some((*sz, *sz, true)),
        TK::Id(nm) => consts.get(nm).map(|&(_, sz)| (sz, sz, true)).or_else(|| structs.get(nm).copied()),
        _ => None,
    }
}

fn parse_ty_layout(toks: &[LT], s: usize, e: usize, consts: &BTreeMap<String, (u64, usize)>, structs: &BTreeMap<String, (usize, usize, bool)>) -> Option<(usize, usize, bool)> {
    match &toks.get(s)?.k {
        TK::Sym("[") => {
            let pe = skip_pair(toks, s, "[", "]");
            let sc = find_top_sym(toks, s + 1, pe.saturating_sub(1), ";")?;
            let (es, ea, epod) = parse_ty_layout(toks, s + 1, sc, consts, structs)?;
            let cnt = eval_const(toks, sc + 1, pe.saturating_sub(1), consts)? as usize;
            Some((es.saturating_mul(cnt), ea, epod))
        }
        TK::Sym("(") => {
            let pe = skip_pair(toks, s, "(", ")");
            let (mut cur, mut elems, mut pod) = (s + 1, Vec::new(), true);
            while cur < pe.saturating_sub(1) {
                let nxt = find_top_sym(toks, cur, pe.saturating_sub(1), ",").unwrap_or(pe.saturating_sub(1));
                if cur < nxt {
                    let (sz, al, p) = parse_ty_layout(toks, cur, nxt, consts, structs).or_else(|| infer_val_layout(toks, cur, consts, structs))?;
                    elems.push((sz, al)); pod &= p;
                }
                cur = nxt + 1;
            }
            if elems.is_empty() { return Some((0, 1, true)); }
            let (sz, al) = layout_fields(&elems, false, false, 1);
            Some((sz, al, pod))
        }
        TK::Sym("&") => Some((16, 8, false)),
        TK::Id(nm) => {
            if let Some((sz, al)) = prim_size_align(nm) { return Some((sz, al, true)); }
            if matches!(nm.as_str(), "Vec" | "String" | "Box" | "HashMap" | "BTreeMap" | "Mutex" | "RefCell" | "OnceLock" | "File" | "Arc" | "Rc") {
                return Some((24, 8, false));
            }
            if nm == "Option" && s + 1 < e && matches!(toks.get(s + 1).map(|x| &x.k), Some(TK::Sym("<"))) {
                let ae = skip_pair(toks, s + 1, "<", ">");
                let (is_, ia, ipod) = parse_ty_layout(toks, s + 2, ae.saturating_sub(1), consts, structs)?;
                return Some((is_.saturating_add(ia), ia, ipod));
            }
            structs.get(nm).copied()
        }
        _ => None,
    }
}

#[derive(Clone)]
struct StructRec { file_idx: usize, line: usize, name: String, repr_c: bool, repr_packed: bool, explicit_align: usize, field_spans: Vec<(usize, usize)> }
struct FnRec { file_idx: usize, line: usize, full_name: String, short_name: String, self_ty: Option<String>, is_const: bool, body: (usize, usize), top_allocs: Vec<(usize, String)> }
struct CallRec { caller: usize, file_idx: usize, qual: Option<String>, short: String, is_self: bool, loop_depth: usize }
struct WorksetRec { file_idx: usize, line: usize, fn_name: String, loop_depth: usize, bytes: usize, elem_bytes: usize, desc: String }

fn is_test_attr(toks: &[LT], s: usize, e: usize) -> bool {
    let sl = toks.get(s..e).unwrap_or(&[]);
    matches!(sl.first().map(|t| &t.k), Some(TK::Id(w)) if w == "test")
        || (matches!(sl.first().map(|t| &t.k), Some(TK::Id(w)) if w == "cfg")
            && sl.iter().any(|t| matches!(&t.k, TK::Id(w) if w == "test" || w == "kani")))
}

fn parse_repr_attr(toks: &[LT], s: usize, e: usize, repr_c: &mut bool, repr_packed: &mut bool, align: &mut usize) {
    let sl = toks.get(s..e).unwrap_or(&[]);
    if !matches!(sl.first().map(|t| &t.k), Some(TK::Id(w)) if w == "repr") { return; }
    for (idx, t) in sl.iter().enumerate() {
        if let TK::Id(w) = &t.k {
            if w == "C" { *repr_c = true; } else if w == "packed" { *repr_packed = true; }
            else if w == "align" { if let Some(TK::Int(v, _)) = sl.get(idx + 2).map(|x| &x.k) { *align = (*align).max(*v as usize); } }
        }
    }
}

fn skip_to_body_or_semi(toks: &[LT], mut j: usize, end: usize) -> usize {
    while j < end {
        match toks.get(j).map(|t| &t.k) {
            Some(TK::Sym("{" | ";")) => break,
            Some(TK::Sym("(")) => j = skip_pair(toks, j, "(", ")"),
            Some(TK::Sym("[")) => j = skip_pair(toks, j, "[", "]"),
            Some(TK::Sym("<")) => j = skip_pair(toks, j, "<", ">"),
            _ => j += 1,
        }
    }
    j
}

fn collect_file_items(
    file_idx: usize, toks: &[LT], skip_tests: bool,
    consts: &mut BTreeMap<String, (u64, usize)>, structs: &mut Vec<StructRec>, fns: &mut Vec<FnRec>,
) {
    fn walk(
        file_idx: usize, toks: &[LT], mut i: usize, end: usize, skip_tests: bool, self_ty: Option<&str>,
        consts: &mut BTreeMap<String, (u64, usize)>, structs: &mut Vec<StructRec>, fns: &mut Vec<FnRec>,
    ) {
        let (mut test_flag, mut rc, mut rp, mut al) = (false, false, false, 0usize);
        while i < end {
            if matches!(toks.get(i).map(|t| &t.k), Some(TK::Sym("#"))) {
                let b = i + 1 + usize::from(matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Sym("!"))));
                if matches!(toks.get(b).map(|t| &t.k), Some(TK::Sym("["))) {
                    let be = skip_pair(toks, b, "[", "]");
                    if b == i + 1 {
                        test_flag |= is_test_attr(toks, b + 1, be.saturating_sub(1));
                        parse_repr_attr(toks, b + 1, be.saturating_sub(1), &mut rc, &mut rp, &mut al);
                    }
                    i = be; continue;
                }
            }
            let kw = match toks.get(i).map(|t| &t.k) { Some(TK::Id(w)) => w.as_str(), _ => "" };
            if matches!(kw, "pub" | "crate" | "unsafe" | "async") {
                i += 1; if matches!(toks.get(i).map(|t| &t.k), Some(TK::Sym("("))) { i = skip_pair(toks, i, "(", ")"); } continue;
            }
            if kw == "mod" || kw == "impl" {
                let (mut j, mut ty_name) = (i + 1, None::<String>);
                if kw == "impl" {
                    if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("<"))) { j = skip_pair(toks, j, "<", ">"); }
                    while j < end && !matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("{"))) {
                        if let Some(TK::Id(w)) = toks.get(j).map(|t| &t.k) { if w != "for" && w != "where" { ty_name = Some(w.clone()); } }
                        j = if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("<"))) { skip_pair(toks, j, "<", ">") } else { j + 1 };
                    }
                } else { j = skip_to_body_or_semi(toks, j, end); }
                if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("{"))) {
                    let be = skip_pair(toks, j, "{", "}");
                    if !(skip_tests && test_flag) { walk(file_idx, toks, j + 1, be.saturating_sub(1), skip_tests, ty_name.as_deref(), consts, structs, fns); }
                    i = be;
                } else { i = (j + 1).min(end); }
                test_flag = false; rc = false; rp = false; al = 0; continue;
            }
            if kw == "const" && !matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Id(w)) if w == "fn") {
                if let Some(TK::Id(nm)) = toks.get(i + 1).map(|t| &t.k) {
                    let (mut j, mut sz) = (i + 2, 8usize);
                    if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym(":"))) {
                        if let Some(TK::Id(tn)) = toks.get(j + 1).map(|t| &t.k) { sz = prim_size_align(tn).map_or(8, |x| x.0); }
                    }
                    while j < end && !matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("=" | ";"))) {
                        j = if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("["))) { skip_pair(toks, j, "[", "]") } else { j + 1 };
                    }
                    if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("="))) {
                        let se = skip_to_body_or_semi(toks, j + 1, end);
                        if let Some(v) = eval_const(toks, j + 1, se, consts) { consts.insert(nm.clone(), (v, sz)); }
                        i = (se + 1).min(end); test_flag = false; rc = false; rp = false; al = 0; continue;
                    }
                }
            }
            if kw == "struct" {
                let line = toks.get(i).map_or(1, |t| t.line);
                if let Some(TK::Id(nm)) = toks.get(i + 1).map(|t| &t.k) {
                    let j = skip_to_body_or_semi(toks, i + 2, end);
                    if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("{"))) {
                        let be = skip_pair(toks, j, "{", "}");
                        if !(skip_tests && test_flag) {
                            let (mut fields, mut k) = (Vec::new(), j + 1);
                            while k < be.saturating_sub(1) {
                                if matches!(toks.get(k).map(|t| &t.k), Some(TK::Sym("#"))) { k = skip_pair(toks, k + 1, "[", "]"); continue; }
                                if matches!(toks.get(k).map(|t| &t.k), Some(TK::Sym(":"))) {
                                    let ts = k + 1;
                                    let te = find_top_sym(toks, ts, be.saturating_sub(1), ",").unwrap_or(be.saturating_sub(1));
                                    if ts < te { fields.push((ts, te)); }
                                    k = te + 1; continue;
                                }
                                k += 1;
                            }
                            structs.push(StructRec { file_idx, line, name: nm.clone(), repr_c: rc, repr_packed: rp, explicit_align: al, field_spans: fields });
                        }
                        i = be; test_flag = false; rc = false; rp = false; al = 0; continue;
                    }
                }
            }
            let is_const_fn = kw == "const" && matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Id(w)) if w == "fn");
            if kw == "fn" || is_const_fn {
                let fi_pos = i + usize::from(is_const_fn);
                let line = toks.get(fi_pos).map_or(1, |t| t.line);
                if let Some(TK::Id(short)) = toks.get(fi_pos + 1).map(|t| &t.k) {
                    let j = skip_to_body_or_semi(toks, fi_pos + 2, end);
                    if matches!(toks.get(j).map(|t| &t.k), Some(TK::Sym("{"))) {
                        let be = skip_pair(toks, j, "{", "}");
                        if !(skip_tests && test_flag) {
                            let full_name = self_ty.map_or_else(|| short.clone(), |st| format!("{st}::{short}"));
                            fns.push(FnRec { file_idx, line, full_name, short_name: short.clone(), self_ty: self_ty.map(str::to_string), is_const: is_const_fn, body: (j + 1, be.saturating_sub(1)), top_allocs: Vec::new() });
                        }
                        i = be; test_flag = false; rc = false; rp = false; al = 0; continue;
                    }
                }
            }
            i = if matches!(toks.get(i).map(|t| &t.k), Some(TK::Sym("{"))) { skip_pair(toks, i, "{", "}") } else { i + 1 };
            if matches!(toks.get(i.saturating_sub(1)).map(|t| &t.k), Some(TK::Sym(";" | "}"))) { test_flag = false; rc = false; rp = false; al = 0; }
        }
    }
    walk(file_idx, toks, 0, toks.len(), skip_tests, None, consts, structs, fns);
}

fn loop_mult(depth: usize) -> u64 { match depth { 0 => 1, 1 => 10, 2 => 100, _ => 1000 } }

fn mk_finding(file: &str, line: usize, fn_name: String, rule: PerfRule, severity: PerfSeverity, cache_bytes: usize, impact_score: u64, compounding_path: String, detail: String, fix: String) -> PerfFinding {
    PerfFinding { file: file.to_string(), line, fn_name, rule, severity, cache_bytes, impact_score, compounding_path, detail, fix }
}

fn is_serial_bit_loop(toks: &[LT], s: usize, e: usize) -> bool {
    let sl = toks.get(s..e).unwrap_or(&[]);
    sl.windows(3).any(|w| matches!((&w[0].k, &w[1].k, &w[2].k), (TK::Int(0, _), TK::Sym(".."), TK::Int(8, _)) | (TK::Int(0, _), TK::Sym("..="), TK::Int(7, _))))
        || sl.windows(3).any(|w| matches!((&w[0].k, &w[1].k, &w[2].k), (TK::Id(v), TK::Sym("<"), TK::Int(8, _)) if v.contains("bit") || v == "b"))
}

fn is_pow2_or_const_denom(toks: &[LT], rhs: usize, consts: &BTreeMap<String, (u64, usize)>) -> bool {
    let p = rhs + usize::from(matches!(toks.get(rhs).map(|t| &t.k), Some(TK::Sym("("))));
    match toks.get(p).map(|t| &t.k) {
        Some(TK::Int(v, _)) => *v > 0 && (*v == 1 || v.is_power_of_two() || toks.get(p + 1).is_none_or(|t| !matches!(t.k, TK::Sym("*" | "+" | "-")))),
        Some(TK::Id(nm)) => consts.get(nm).is_some_and(|&(v, _)| v > 0 && v.is_power_of_two()),
        _ => false,
    }
}

fn scan_fn_body(
    fidx: usize, f: &mut FnRec, file: &str, toks: &[LT],
    consts: &BTreeMap<String, (u64, usize)>, structs: &BTreeMap<String, (usize, usize, bool)>,
    worksets: &mut Vec<WorksetRec>, calls: &mut Vec<CallRec>, findings: &mut Vec<PerfFinding>,
) {
    let (s, e) = f.body;
    let has_prefetch = toks.get(s..e).unwrap_or(&[]).iter().any(|t| matches!(&t.k, TK::Id(w) if w.contains("prefetch")));
    let (mut i, mut loop_depth, mut brace_loops, mut pending_loop) = (s, 0usize, Vec::<bool>::new(), false);
    let (mut seen_p4, mut seen_p5, mut seen_p1) = (BTreeSet::<usize>::new(), BTreeSet::<usize>::new(), BTreeSet::<usize>::new());
    while i < e {
        let line = toks.get(i).map_or(f.line, |t| t.line);
        match toks.get(i).map(|t| &t.k) {
            Some(TK::Id(w)) if matches!(w.as_str(), "for" | "while" | "loop") => {
                let mut hb = i + 1;
                while hb < e && !matches!(toks.get(hb).map(|t| &t.k), Some(TK::Sym("{"))) { hb += 1; }
                if !f.is_const && loop_depth >= 1 && is_serial_bit_loop(toks, i + 1, hb) && seen_p4.insert(line) {
                    findings.push(mk_finding(
                        file, line, f.full_name.clone(), PerfRule::Perf04, PerfSeverity::High, 0,
                        loop_mult(loop_depth + 1).saturating_mul(180),
                        format!("{} (loop depth {} -> serial 8-bit loop)", f.full_name, loop_depth),
                        "8-step serial inner bit loop inside outer loop".to_string(),
                        "Replace with 4-bit nibble 16-symbol CDF (2 steps/byte) or LUT".to_string(),
                    ));
                }
                pending_loop = true; i += 1;
            }
            Some(TK::Sym("{")) => { brace_loops.push(pending_loop); if pending_loop { loop_depth += 1; pending_loop = false; } i += 1; }
            Some(TK::Sym("}")) => { if brace_loops.pop().unwrap_or(false) { loop_depth = loop_depth.saturating_sub(1); } i += 1; }
            Some(TK::Sym("[")) => {
                let pe = skip_pair(toks, i, "[", "]");
                if let Some(sc) = find_top_sym(toks, i + 1, pe.saturating_sub(1), ";") {
                    let elem_sz = parse_ty_layout(toks, i + 1, sc, consts, structs)
                        .or_else(|| infer_val_layout(toks, i + 1, consts, structs)).map_or(4, |x| x.0);
                    if let Some(cnt) = eval_const(toks, sc + 1, pe.saturating_sub(1), consts) {
                        let bytes = elem_sz.saturating_mul(cnt as usize);
                        if bytes >= 16_384 && seen_p1.insert(line) {
                            worksets.push(WorksetRec { file_idx: f.file_idx, line, fn_name: f.full_name.clone(), loop_depth, bytes, elem_bytes: elem_sz, desc: format!("[{elem_sz}B; {cnt}]") });
                        }
                    }
                } else if !f.is_const && !has_prefetch && loop_depth >= 2 && matches!(toks.get(i.saturating_sub(1)).map(|t| &t.k), Some(TK::Id(_))) {
                    let arr = match toks.get(i.saturating_sub(1)).map(|t| &t.k) { Some(TK::Id(n)) => n.as_str(), _ => "" };
                    let nested = (i + 1..pe.saturating_sub(1)).any(|k| {
                        matches!(toks.get(k).map(|t| &t.k), Some(TK::Sym("["))) && matches!(toks.get(k.saturating_sub(1)).map(|t| &t.k), Some(TK::Id(_)))
                    });
                    if (nested || arr.contains("prev") || arr.contains("chain") || arr.contains("next")) && seen_p5.insert(line) {
                        findings.push(mk_finding(
                            file, line, f.full_name.clone(), PerfRule::Perf05, PerfSeverity::High, 0,
                            loop_mult(loop_depth).saturating_mul(200),
                            format!("{} (loop depth {} -> indirect/chain '{}')", f.full_name, loop_depth, arr),
                            format!("indirect pointer-chase or chain walk on '{}' at loop depth {}", arr, loop_depth),
                            "Use inline 2-slot buckets (head: Vec<[u32; 2]>), interior-match skip, or lookahead prefetcht0".to_string(),
                        ));
                    }
                }
                i += 1;
            }
            Some(TK::Sym("/" | "%" | "/=" | "%=")) if !f.is_const && loop_depth >= 1 => {
                let prev_val = matches!(toks.get(i.saturating_sub(1)).map(|t| &t.k), Some(TK::Id(_) | TK::Int(_, _) | TK::Sym(")" | "]")));
                let is_sh = matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Sym("(")))
                    && matches!(toks.get(i + 2).map(|t| &t.k), Some(TK::Int(1, _)))
                    && matches!(toks.get(i + 3).map(|t| &t.k), Some(TK::Sym("<<")));
                if prev_val && !is_sh && !is_pow2_or_const_denom(toks, i + 1, consts) && seen_p4.insert(line) {
                    findings.push(mk_finding(
                        file, line, f.full_name.clone(), PerfRule::Perf04, PerfSeverity::High, 0,
                        loop_mult(loop_depth).saturating_mul(120),
                        format!("{} (loop depth {} -> runtime div/mod)", f.full_name, loop_depth),
                        "runtime division/modulo by non-const non-pow2 denominator in loop".to_string(),
                        "Replace with Granlund-Montgomery reciprocal multiply-shift (Recip12) or pow2 mask".to_string(),
                    ));
                }
                i += 1;
            }
            Some(TK::Id(w)) => {
                let ak = if w == "vec" && matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Sym("!"))) && matches!(toks.get(i + 2).map(|t| &t.k), Some(TK::Sym("["))) {
                    Some("vec![..]")
                } else if matches!(w.as_str(), "Vec" | "Box" | "String") && matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Sym("::")))
                    && matches!(toks.get(i + 2).map(|t| &t.k), Some(TK::Id(m)) if matches!(m.as_str(), "new" | "with_capacity")) {
                    Some(if w == "Vec" { "Vec::alloc" } else if w == "Box" { "Box::new" } else { "String::alloc" })
                } else if matches!(w.as_str(), "to_vec" | "clone") && matches!(toks.get(i.saturating_sub(1)).map(|t| &t.k), Some(TK::Sym(".")))
                    && matches!(toks.get(i + 1).map(|t| &t.k), Some(TK::Sym("("))) {
                    Some(if w == "to_vec" { ".to_vec()" } else { ".clone()" })
                } else { None };
                if let Some(ak) = ak {
                    if loop_depth >= 1 {
                        findings.push(mk_finding(
                            file, line, f.full_name.clone(), PerfRule::Perf03, PerfSeverity::High, 0,
                            loop_mult(loop_depth).saturating_mul(250),
                            format!("{} (loop depth {}) -> {}", f.full_name, loop_depth, ak),
                            format!("heap allocation ({ak}) inside loop depth {loop_depth}"),
                            "Reuse RTOS scratch arena (&mut Scratch / thread_local! + .clear())".to_string(),
                        ));
                    } else if ak != ".clone()" { f.top_allocs.push((line, ak.to_string())); }
                }
                let mut ci = i + 1;
                if matches!(toks.get(ci).map(|t| &t.k), Some(TK::Sym("::"))) && matches!(toks.get(ci + 1).map(|t| &t.k), Some(TK::Sym("<"))) {
                    ci = skip_pair(toks, ci + 1, "<", ">");
                }
                if !matches!(w.as_str(), "if" | "else" | "while" | "for" | "match" | "loop" | "return" | "let" | "Some" | "Ok" | "Err")
                    && matches!(toks.get(ci).map(|t| &t.k), Some(TK::Sym("("))) {
                    let is_m = i > s && matches!(toks.get(i - 1).map(|t| &t.k), Some(TK::Sym(".")));
                    let is_self = is_m && i >= s + 2 && matches!(toks.get(i - 2).map(|t| &t.k), Some(TK::Id(x)) if x == "self");
                    let qual = (!is_m && i >= s + 2 && matches!(toks.get(i - 1).map(|t| &t.k), Some(TK::Sym("::"))))
                        .then(|| match toks.get(i - 2).map(|t| &t.k) { Some(TK::Id(q)) => Some(q.clone()), _ => None }).flatten();
                    calls.push(CallRec { caller: fidx, file_idx: f.file_idx, qual, short: w.clone(), is_self, loop_depth });
                }
                i += 1;
            }
            _ => i += 1,
        }
    }
}

fn eval_workset_finding(w: &WorksetRec, file: &str, profile: &CpuProfile) -> Option<PerfFinding> {
    let (l1, l2) = (profile.l1d_bytes().max(1), profile.l2_bytes().max(1));
    if w.bytes.saturating_mul(4) < l1.saturating_mul(3) { return None; }
    let (l1_pct, l2_pct) = (
        w.bytes.saturating_mul(100).checked_div(l1).unwrap_or(0),
        w.bytes.saturating_mul(100).checked_div(l2).unwrap_or(0),
    );
    let (sev, pen, fix) = if w.bytes > l2 {
        (PerfSeverity::High, 200 + (l2_pct as u64).saturating_mul(2),
         format!("Cap table to <= {} KiB via ZenTuningPlan or tile into l1_tile_bytes chunks", profile.l2_kib / 2))
    } else if w.bytes >= l1 {
        let f = if w.elem_bytes >= 8 && w.bytes <= l1.saturating_mul(2) {
            "Shrink element type (e.g. [u32; N] + lzcnt) to fit <= 50% L1D".to_string()
        } else { format!("Tile working set into l1_tile_bytes (<= {} KiB) chunks", profile.l1d_kib / 2) };
        (PerfSeverity::High, 100 + l1_pct as u64, f)
    } else {
        (PerfSeverity::Medium, 60 + l1_pct as u64, format!("Keep table <= {} KiB (50% L1D) via narrower elements or tiling", profile.l1d_kib / 2))
    };
    Some(mk_finding(
        file, w.line, w.fn_name.clone(), PerfRule::Perf01, sev, w.bytes,
        loop_mult(w.loop_depth).saturating_mul(pen),
        format!("{} (working set {} = {}B)", w.fn_name, w.desc, w.bytes),
        format!("working set {} = {} B ({}% of {} KiB L1D, {}% of {} KiB L2)", w.desc, w.bytes, l1_pct, profile.l1d_kib, l2_pct, profile.l2_kib),
        fix,
    ))
}

fn analyze_sources(files: &[(String, String)], profile: &CpuProfile, all_profiles: &[CpuProfile], opts: PerfOptions) -> PerfReport {
    let t0 = perf_clock_start();
    let (mut all_toks, mut total_lines) = (Vec::with_capacity(files.len()), 0usize);
    for (_, src) in files { total_lines += src.lines().count(); all_toks.push(lex_rust_lines(src)); }
    let (mut consts, mut struct_recs, mut fns) = (BTreeMap::new(), Vec::new(), Vec::new());
    for (fi, toks) in all_toks.iter().enumerate() { collect_file_items(fi, toks, opts.exclude_cfg_test, &mut consts, &mut struct_recs, &mut fns); }
    let (mut ds, mut df) = (Vec::new(), Vec::new());
    for (fi, toks) in all_toks.iter().enumerate() { collect_file_items(fi, toks, opts.exclude_cfg_test, &mut consts, &mut ds, &mut df); }
    let mut layouts = BTreeMap::<String, (usize, usize, bool)>::new();
    for _ in 0..2 {
        for sr in &struct_recs {
            let Some(toks) = all_toks.get(sr.file_idx) else { continue; };
            let (mut fields, mut all_pod) = (Vec::new(), !sr.field_spans.is_empty());
            for &(ts, te) in &sr.field_spans {
                if let Some((sz, al, pod)) = parse_ty_layout(toks, ts, te, &consts, &layouts) { fields.push((sz, al)); all_pod &= pod; }
                else { all_pod = false; }
            }
            if !all_pod { continue; }
            let (total, max_al) = layout_fields(&fields, sr.repr_c, sr.repr_packed, sr.explicit_align);
            layouts.insert(sr.name.clone(), (total, max_al, true));
        }
    }
    let (mut findings, mut worksets, mut calls, lb) = (Vec::new(), Vec::new(), Vec::new(), profile.line_bytes.max(1));
    for sr in &struct_recs {
        let Some(&(sz, al, true)) = layouts.get(&sr.name) else { continue; };
        if sr.field_spans.len() >= 2 && sz > 16 && sr.explicit_align == 0 && lb % sz != 0 && sz % lb != 0 {
            let target = if sz <= 40 { 32 } else { ((sz + lb - 1) / lb).saturating_mul(lb) };
            let lines_t = (sz + lb - 1) / lb + 1;
            let file = files.get(sr.file_idx).map_or("", |x| x.0.as_str());
            findings.push(mk_finding(
                file, sr.line, format!("struct {}", sr.name), PerfRule::Perf02,
                if sz > lb { PerfSeverity::High } else { PerfSeverity::Medium }, sz,
                40 + (lines_t as u64).saturating_mul(25),
                format!("struct {} ({}B, align {}B, straddles up to {} cache lines)", sr.name, sz, al, lines_t),
                format!("struct '{}' is {} B (neither divisor nor multiple of {} B cache line)", sr.name, sz, lb),
                format!("Pack/pad to {target} B with #[repr(C, align({}))]", if target <= 32 { 32 } else { lb }),
            ));
        }
    }
    for (fidx, f) in fns.iter_mut().enumerate() {
        if let Some(toks) = all_toks.get(f.file_idx) {
            scan_fn_body(fidx, f, files.get(f.file_idx).map_or("", |x| x.0.as_str()), toks, &consts, &layouts, &mut worksets, &mut calls, &mut findings);
        }
    }
    for w in &worksets {
        if let Some(pf) = eval_workset_finding(w, files.get(w.file_idx).map_or("", |x| x.0.as_str()), profile) { findings.push(pf); }
    }
    let (mut incoming, mut edges_scanned): (Vec<Vec<(usize, usize)>>, usize) = (vec![Vec::new(); fns.len()], 0);
    for c in &calls {
        let c_self = fns.get(c.caller).and_then(|x| x.self_ty.as_deref());
        let tgt = fns.iter().enumerate().find(|&(fid, tf)| {
            fid != c.caller && tf.short_name == c.short && (if c.is_self { tf.self_ty.as_deref() == c_self }
                else if let Some(ref q) = c.qual { tf.self_ty.as_deref() == Some(if q == "Self" { c_self.unwrap_or(q.as_str()) } else { q.as_str() }) }
                else { tf.file_idx == c.file_idx || tf.self_ty.is_none() })
        }).map(|(fid, _)| fid);
        if let Some(tid) = tgt {
            if let Some(slot) = incoming.get_mut(tid) {
                if !slot.iter().any(|&(s, d)| s == c.caller && d >= c.loop_depth) { slot.push((c.caller, c.loop_depth)); edges_scanned += 1; }
            }
        }
    }
    let best_chain = |start: usize| -> Option<(usize, String)> {
        let (mut best_d, mut best_p, mut stack) = (0usize, String::new(), vec![(start, 0usize, vec![start])]);
        while let Some((cur, acc_d, path)) = stack.pop() {
            if path.len() > 5 { continue; }
            for &(caller, ed) in incoming.get(cur).map_or(&[][..], Vec::as_slice) {
                if path.contains(&caller) { continue; }
                let nd = acc_d.saturating_add(ed);
                let mut np = path.clone(); np.push(caller);
                if nd > best_d {
                    best_d = nd;
                    best_p = np.iter().rev().filter_map(|&id| fns.get(id).map(|x| x.full_name.as_str())).collect::<Vec<_>>().join(" -> ");
                }
                stack.push((caller, nd, np));
            }
        }
        (best_d > 0).then_some((best_d, best_p))
    };
    for (fid, f) in fns.iter().enumerate() {
        if f.top_allocs.is_empty() { continue; }
        let Some((d, chain)) = best_chain(fid) else { continue; };
        let file = files.get(f.file_idx).map_or("", |x| x.0.as_str());
        for (aline, ak) in &f.top_allocs {
            findings.push(mk_finding(
                file, *aline, f.full_name.clone(), PerfRule::Perf03, PerfSeverity::High, 0,
                loop_mult(d).saturating_mul(250),
                format!("{chain} (caller loop depth {d}, alloc {ak})"),
                format!("callee '{}' allocates ({ak}) on hot caller loop path", f.full_name),
                "Pass reusable RTOS scratch arena (&mut Scratch / thread_local! + .clear()) into callee".to_string(),
            ));
        }
    }
    let fn_idx: BTreeMap<&str, usize> = fns.iter().enumerate().map(|(i, f)| (f.full_name.as_str(), i)).collect();
    for pf in &mut findings {
        if pf.rule == PerfRule::Perf02 || pf.compounding_path.contains(" -> ") { continue; }
        if let Some(&fid) = fn_idx.get(pf.fn_name.as_str()) {
            if let Some((d, chain)) = best_chain(fid) {
                pf.impact_score = pf.impact_score.saturating_mul(loop_mult(d));
                pf.compounding_path = format!("{chain} (caller loop depth {d})");
            }
        }
    }
    findings.sort_by(|a, b| {
        b.impact_score.cmp(&a.impact_score).then_with(|| b.severity.cmp(&a.severity))
            .then_with(|| a.file.cmp(&b.file)).then_with(|| a.line.cmp(&b.line)).then_with(|| a.rule.cmp(&b.rule))
    });
    findings.dedup_by(|a, b| a.rule == b.rule && a.file == b.file && a.line == b.line && a.fn_name == b.fn_name);
    let profile_comparison: Vec<ProfileResidencyRow> = ["zen2_rome", "zen4_genoa", "zen5_turin"]
        .into_iter().filter_map(|cn| all_profiles.iter().find(|x| x.name == cn)).map(|p| ProfileResidencyRow {
            profile_name: p.name.clone(), l1d_kib: p.l1d_kib, l2_kib: p.l2_kib,
            l1d_cliffs: worksets.iter().filter(|w| w.bytes.saturating_mul(4) >= p.l1d_bytes().saturating_mul(3)).count(),
            l2_overflows: worksets.iter().filter(|w| w.bytes > p.l2_bytes()).count(),
        }).collect();
    PerfReport {
        profile: profile.clone(), files_scanned: files.len(), lines_scanned: total_lines,
        fns_scanned: fns.len(), edges_scanned, elapsed_us: perf_clock_us(t0),
        findings, profile_comparison, bench_telemetry: Vec::new(),
    }
}

#[must_use]
pub fn analyze_rust_source(file: &str, src: &str, profile: &CpuProfile, all_profiles: &[CpuProfile], opts: PerfOptions) -> PerfReport {
    analyze_sources(&[(file.to_string(), src.to_string())], profile, all_profiles, opts)
}

pub fn analyze_crate_perf(
    dir: &Path, skip: &[String], profile: &CpuProfile, all_profiles: &[CpuProfile], opts: PerfOptions,
) -> Result<PerfReport, VerifyError> {
    let mut paths = Vec::new();
    collect_rs_files_opts(dir, skip, opts.exclude_cfg_test, &mut paths)?;
    paths.sort();
    let mut files = Vec::with_capacity(paths.len());
    for p in paths {
        files.push((p.display().to_string(), fs::read_to_string(&p).map_err(|e| VerifyError::Io(format!("{}: {e}", p.display())))?));
    }
    Ok(analyze_sources(&files, profile, all_profiles, opts))
}

#[must_use]
pub fn run_zero_cc_bench(target: &Path, profile: &CpuProfile, spec_path: Option<&Path>) -> Vec<String> {
    let cand = env::var_os("ZERO_CC_BIN").map(PathBuf::from).filter(|p| p.is_file())
        .or_else(|| {
            env::var_os("HOME")
                .map(|h| PathBuf::from(h).join("zero-cc/target/release/zero-cc"))
                .filter(|p| p.is_file())
        })
        .unwrap_or_else(|| PathBuf::from("zero-cc"));
    let mut cmd = Command::new(&cand);
    cmd.arg(target).arg("--cpu").arg(&profile.name).arg("--bench");
    if let Some(sp) = spec_path { cmd.arg("--cpu-spec").arg(sp); }
    match cmd.output() {
        Ok(out) => {
            let txt = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
            let lines: Vec<String> = txt.lines()
                .filter(|l| l.contains("ns/blk") || l.contains("GB/s") || l.contains("[BENCH") || l.contains("bench"))
                .map(|l| l.trim().to_string()).collect();
            if !lines.is_empty() { lines }
            else if out.status.success() { vec![format!("zero-cc {} --cpu {} --bench ok (no bench rows)", target.display(), profile.name)] }
            else { vec![format!("zero-cc bench skipped for {}: exit {}", target.display(), out.status)] }
        }
        Err(_) => vec!["zero-cc binary not found (skipped live --perf-bench)".to_string()],
    }
}
