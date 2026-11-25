use std::{collections::BTreeSet, fs, path::Path};
use crate::abstract_eval::{ArchProfile, Domain, Op, Program, ProofStatus, VerifyError};
use crate::lint_rs::LintKind;
use crate::ntf1::{verify_ntf1_source, Ntf1Error};
use crate::rust_fe::verify_rust_functions;
use crate::simd_fuzz::{eval_lanes_x8, fault_name, prove_exhaustive, ProofVerdict, RefineConfig, FAULT_DOUBLE_FREE, FAULT_OOB, FAULT_UAF, FAULT_UNINIT, LANES};
use crate::{verify_kernel_rust_source, verify_program};
macro_rules! prog {
    ($name:expr; $($body:tt)*) => {{ let mut p = Program::new($name); prog!(@s p; $($body)*); p }}; (@s $p:ident;) => {};
    (@s $p:ident; buf $v:ident = ($n:expr, $l:expr, $m:expr, $r:expr, $o:expr, $d:expr); $($t:tt)*) => { let $v = $p.add_buf($n, $l, $m, $r, $o, $d); prog!(@s $p; $($t)*); };
    (@s $p:ident; uninit $v:ident = ($n:expr, $l:expr, $m:expr, $r:expr, $o:expr, $d:expr); $($t:tt)*) => { let $v = $p.add_uninit_buf($n, $l, $m, $r, $o, $d); prog!(@s $p; $($t)*); };
    (@s $p:ident; param $v:ident = $d:expr; $($t:tt)*) => { let $v = $p.add_param($d); prog!(@s $p; $($t)*); };
    (@s $p:ident; let $v:ident = $op:expr; $($t:tt)*) => { let $v = $p.push($op); prog!(@s $p; $($t)*); }; (@s $p:ident; do $op:expr; $($t:tt)*) => { $p.push($op); prog!(@s $p; $($t)*); };
    (@s $p:ident; out $v:expr; $($t:tt)*) => { $p.add_output($v); prog!(@s $p; $($t)*); }; }
#[derive(Clone, Debug)]
pub struct GauntletSummary { pub checks_passed: usize, pub checks_total: usize, pub proven_invariants: Vec<String>, pub learned_guards: Vec<String>, pub failures: Vec<String> }
impl GauntletSummary { #[must_use] pub fn is_clean(&self) -> bool { self.failures.is_empty() && self.checks_passed == self.checks_total } }
/// Build the non-linear `(x * x) % 16` kernel on `x in [0, 1000]` with optional 1-point fault at `x == 777`.
#[must_use] pub fn build_quad_mod16_kernel(with_777_fault: bool) -> Program {
    let mut p = prog!(if with_777_fault { "quad_mod16_fault777" } else { "quad_mod16_clean" };
        buf lut = ("qr16_lut", 10, false, 1, 0, Domain::range(0, 255)); param x = Domain::range(0, 1000);
        let sq = Op::Mul(x, x); let c16 = Op::Const(16); let idx = Op::Rem(sq, c16); do Op::Load { buf: lut, idx };
    ); if with_777_fault { let c777 = p.push(Op::Const(777)); let denom = p.push(Op::Sub(0, c777)); let q = p.push(Op::Div(4, denom)); p.add_output(q); } else { p.add_output(4); }
    p }
fn check_miri_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    let cfg = RefineConfig::default();
    let alias = prog!("miri_noalias"; buf a = ("a", 16, true, 1, 0, Domain::range(0, 100)); buf b = ("b", 16, false, 1, 8, Domain::range(0, 100)); param i = Domain::range(0, 15); let v = Op::Load { buf: b, idx: i }; let s = Op::Store { buf: a, idx: i, val: v }; out s;);
    if matches!(verify_program(&alias, ArchProfile::Aarch64Neon, cfg), Err(VerifyError::NoAliasViolation { .. })) { *passed += 1; guards.push("miri:noalias rejected overlapping &mut/& in region 1".into()); } else { fails.push("miri:noalias failed to catch overlap".into()); }
    let sh = prog!("miri_shl64"; param x = Domain::range(0, 100); let o = Op::Shl(x, 64); out o;);
    if matches!(verify_program(&sh, ArchProfile::X86_64Avx2, cfg), Err(VerifyError::ShiftOverflow { lo: 64, hi: 64, .. })) { *passed += 1; guards.push("miri:shift_ub rejected << 64 statically".into()); } else { fails.push("miri:shift_ub failed to catch << 64".into()); }
    let dv = prog!("miri_div0_42"; param xd = Domain::range(0, 100_000); let c100 = Op::Const(100); let c42 = Op::Const(42); let sub = Op::Sub(xd, c42); let q = Op::Div(c100, sub); out q;);
    if matches!(verify_program(&dv, ArchProfile::Aarch64Neon, cfg), Err(VerifyError::CounterexampleFound { inputs, .. }) if inputs == vec![42]) { *passed += 1; guards.push("miri:div0 ce=[42] isolated in [0..=100000]".into()); } else { fails.push("miri:div0 failed to catch x == 42".into()); }
    let eg = prog!("miri_egraph"; buf tb = ("tbl", 16, false, 1, 0, Domain::range(0, 255)); param xe = Domain::range(0, 1000); let c12 = Op::Const(12); let sm = Op::Add(xe, c12); let df = Op::Sub(sm, xe); let ld = Op::Load { buf: tb, idx: df }; out ld;);
    if matches!(verify_program(&eg, ArchProfile::Aarch64Neon, cfg), Ok(r) if r.abstract_report.status == ProofStatus::ProvenSafe) { inv.push("miri:egraph (x + 12) - x == 12 statically proven on x in 0..=1000".into()); } }
fn check_asan_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    let cfg = RefineConfig::default();
    let oob = prog!("asan_oob16"; buf b = ("arr", 16, false, 1, 0, Domain::range(0, 255)); param x = Domain::range(0, 16); let v = Op::Load { buf: b, idx: x }; out v;);
    match prove_exhaustive(&oob, cfg) {
        ProofVerdict::Counterexample { input, fault, synthesized_guard, .. } if input == vec![16] && (fault & FAULT_OOB) != 0 && synthesized_guard == "p0 in 0..=15" => { *passed += 1; guards.push(format!("asan:oob16 fault={} ce={input:?} guard=({synthesized_guard})", fault_name(fault))); }
        other => fails.push(format!("asan:oob16 unexpected verdict: {other:?}")), }
    let uaf = prog!("asan_uaf"; buf bu = ("heap", 16, true, 1, 0, Domain::range(0, 255)); param iu = Domain::range(0, 15); do Op::Free(bu); let lu = Op::Load { buf: bu, idx: iu }; out lu;);
    if let Err(VerifyError::UseAfterFree { buf, generation, .. }) = verify_program(&uaf, ArchProfile::Aarch64Neon, cfg) {
        if eval_lanes_x8(&uaf, &[[0; LANES]]).faults.iter().all(|&f| (f & FAULT_UAF) != 0) { *passed += 1; guards.push(format!("asan:uaf fault=UseAfterFree buf={buf} gen={generation} simd_lanes=8/8")); } else { fails.push("asan:uaf SIMD replay missed FAULT_UAF".into()); }
    } else { fails.push("asan:uaf static missed UAF".into()); }
    let df = prog!("asan_double_free"; buf bd = ("heap", 16, true, 1, 0, Domain::range(0, 255)); do Op::Free(bd); let f2 = Op::Free(bd); out f2;);
    if let Err(VerifyError::DoubleFree { buf, generation, .. }) = verify_program(&df, ArchProfile::Aarch64Neon, cfg) {
        if eval_lanes_x8(&df, &[]).faults.iter().all(|&f| (f & FAULT_DOUBLE_FREE) != 0) { *passed += 1; guards.push(format!("asan:double_free fault=DoubleFree buf={buf} gen={generation} simd_lanes=8/8")); } else { fails.push("asan:double_free SIMD replay missed FAULT_DOUBLE_FREE".into()); }
    } else { fails.push("asan:double_free static missed DoubleFree".into()); }
    let uninit = prog!("asan_uninit"; uninit bn = ("scratch", 16, true, 1, 0, Domain::range(0, 255)); param ix = Domain::range(0, 15); let ln = Op::Load { buf: bn, idx: ix }; out ln;);
    let init_ok = prog!("asan_init_ok"; uninit bi = ("scratch", 16, true, 1, 0, Domain::range(0, 255)); param ii = Domain::range(0, 15); let cv = Op::Const(7); do Op::Store { buf: bi, idx: ii, val: cv }; let li = Op::Load { buf: bi, idx: ii }; out li;);
    if matches!(verify_program(&uninit, ArchProfile::Aarch64Neon, cfg), Err(VerifyError::UninitializedRead { .. })) && verify_program(&init_ok, ArchProfile::Aarch64Neon, cfg).is_ok() && eval_lanes_x8(&uninit, &[[0, 1, 2, 3, 4, 5, 6, 7]]).faults.iter().all(|&f| (f & FAULT_UNINIT) != 0) {
        *passed += 1; inv.push("asan:init_mask store(buf[x]) -> load(buf[x]) proven initialized".into()); guards.push("asan:uninit fault=UninitializedRead buf=0 idx=[0..=15] simd_lanes=8/8".into());
    } else { fails.push("asan:uninit knockout failed".into()); } }
fn check_kani_and_arch_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    let cfg = RefineConfig::default();
    match (prove_exhaustive(&build_quad_mod16_kernel(false), cfg), prove_exhaustive(&build_quad_mod16_kernel(true), cfg)) {
        (ProofVerdict::ProvenTotal { boxes_discharged, learned_invariants }, ProofVerdict::Counterexample { input, fault, synthesized_guard, .. }) if boxes_discharged > 0 && input == vec![777] && synthesized_guard == "p0 in 0..=776 || p0 in 778..=1000" => {
            *passed += 1; inv.push(format!("kani:quad_mod16 ProvenTotal boxes={boxes_discharged} domain=[0..=1000]")); for li in learned_invariants { inv.push(format!("kani:quad_mod16 {li}")); }
            guards.push(format!("kani:quad_mod16_777 fault={} ce={input:?} guard=({synthesized_guard})", fault_name(fault))); }
        (vc, vb) => fails.push(format!("kani:quad_mod16 unexpected: clean={vc:?}, buggy={vb:?}")), }
    let mut k20 = Program::new("arch_20reg"); k20.simd_lanes = 2; for _ in 0..20 { let p = k20.add_param(Domain::range(0, 1000)); k20.add_output(p); }
    if matches!(verify_program(&k20, ArchProfile::X86_64Avx2, cfg), Err(VerifyError::RegisterSpill { peak_gprs: 20, max_gprs: 14, .. })) && verify_program(&k20, ArchProfile::Aarch64Neon, cfg).is_ok() {
        *passed += 1; inv.push("arch:20reg avx2=spill(20/14) neon=pass(20/28,20/32)".into());
    } else { fails.push("arch:20reg dual-arch spill knockout failed".into()); }
    let ok = verify_ntf1_source("inline.ntf1", "NTF1 airlock\n+t zero_cc -> zero_check\n+t zero_check -> Fault.Spill\n-t Fault.Spill <- Guard.Avx2\n0t zero_cc >< zero_check\n");
    let bad_svo = verify_ntf1_source("svo.ntf1", "NTF1 airlock\n# this is prose\n+t a -> b\n"); let bad_cov = verify_ntf1_source("uncov.ntf1", "NTF1 airlock\n+t a -> Fault.Leak\n");
    if matches!(ok, Ok(ref r) if r.canonical_idempotent && r.faults_covered == 1) && matches!(bad_svo, Err(Ntf1Error::SvoTax { .. })) && matches!(bad_cov, Err(Ntf1Error::UncoveredFault { .. })) {
        *passed += 1; inv.push("ntf1:airlock canonical_idempotent=true faults_covered=1".into()); guards.push("ntf1:svo_and_retro rejected SVO prose and uncovered Fault.Leak".into());
    } else { fails.push("ntf1:airlock knockout failed".into()); }
    let rs_ok = "/// @domain x: 0..=1000\npub fn lut_ok(x: i64, tbl: &[i64; 10]) -> i64 { tbl[((x * x) % 16) as usize] }\n";
    let rs_bad = "/// @domain x: 0..=1000\npub fn lut_bad(x: i64, tbl: &[i64; 10]) -> i64 { tbl[((x * x) % 16) as usize] / (x - 777) }\n";
    let rs_panic = "pub fn bad_k(x: Option<i64>) -> i64 { x.unwrap() }\n";
    let caught_777 = matches!(verify_rust_functions("bad.rs", rs_bad, ArchProfile::X86_64Avx2, cfg).failed.first().map(|f| &f.error), Some(VerifyError::CounterexampleFound { inputs, .. }) if inputs == &vec![777]);
    let caught_panic = matches!(verify_kernel_rust_source("panic.rs", rs_panic, ArchProfile::X86_64Avx2, cfg), Err(VerifyError::LintViolations { count: 1 })) && crate::scan_rust_source("panic.rs", rs_panic).findings.iter().any(|f| f.kind == LintKind::PanicCall);
    if verify_kernel_rust_source("ok.rs", rs_ok, ArchProfile::X86_64Avx2, cfg).is_ok() && caught_777 && caught_panic {
        *passed += 1; inv.push("rust_fe:lut_ok ProvenTotal directly from .rs source".into()); guards.push("rust_fe:div0_777_and_kernel_panic rejected x==777 and .unwrap()".into());
    } else { fails.push("rust_fe:raw .rs semantic knockout failed".into()); } }
/// Run the full Miri-class + ASan-class + Kani-class + AVX2/NEON + NTF1 + Rust-FE self-verification gauntlet.
#[must_use] pub fn run_gauntlet() -> GauntletSummary {
    let (mut inv, mut guards, mut fails, mut passed) = (Vec::new(), Vec::new(), Vec::new(), 0usize); check_miri_suite(&mut inv, &mut guards, &mut fails, &mut passed);
    check_asan_suite(&mut inv, &mut guards, &mut fails, &mut passed); check_kani_and_arch_suite(&mut inv, &mut guards, &mut fails, &mut passed);
    GauntletSummary { checks_passed: passed, checks_total: 11, proven_invariants: inv, learned_guards: guards, failures: fails } }
/// Zero-dependency autopoietic JSON ledger persisting proven invariants and learned guards across runs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AutopoieticLedger {
    pub epochs: u64, pub crates_verified: usize, pub files_scanned: usize, pub lines_scanned: usize,
    pub lint_errors: usize, pub lint_warnings: usize, pub gauntlet_passed: usize, pub gauntlet_total: usize,
    pub elapsed_us: u64, pub proven_invariants: BTreeSet<String>, pub learned_guards: BTreeSet<String>, }
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2); out.push('"');
    for b in s.bytes() { match b { b'"' => out.push_str("\\\""), b'\\' => out.push_str("\\\\"), b'\n' => out.push_str("\\n"), b'\r' => out.push_str("\\r"), b'\t' => out.push_str("\\t"), 0x20..=0x7E => out.push(b as char), o => out.push_str(&format!("\\u00{o:02x}")) } }
    out.push('"'); out
}
fn json_unescape(raw: &str) -> String {
    let (bytes, mut out, mut i) = (raw.as_bytes(), String::with_capacity(raw.len()), 0usize);
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 1 < bytes.len() { out.push(match bytes[i + 1] { b'"' => '"', b'\\' => '\\', b'n' => '\n', b'r' => '\r', b't' => '\t', o => o as char }); i += 2; }
        else { out.push(bytes[i] as char); i += 1; } }
    out }
fn parse_u64_field(src: &str, key: &str) -> Option<u64> {
    let needle = format!("\"{key}\""); let rest = src[src.find(&needle)? + needle.len()..].trim_start().strip_prefix(':')?.trim_start();
    rest[..rest.bytes().take_while(u8::is_ascii_digit).count()].parse().ok() }
fn parse_string_array(src: &str, key: &str) -> Vec<String> {
    let needle = format!("\"{key}\""); let Some(pos) = src.find(&needle) else { return Vec::new(); };
    let rest = &src[pos + needle.len()..]; let Some(lb) = rest.find('[') else { return Vec::new(); }; let (bytes, mut out, mut i) = (&rest.as_bytes()[lb + 1..], Vec::new(), 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b']' => break,
            b'"' => {
                i += 1; let start = i;
                while i < bytes.len() { if bytes[i] == b'\\' && i + 1 < bytes.len() { i += 2; } else if bytes[i] == b'"' { break; } else { i += 1; } }
                if i < bytes.len() { out.push(json_unescape(&rest[lb + 1 + start..lb + 1 + i])); i += 1; } }
            _ => i += 1, } }
    out }
impl AutopoieticLedger {
    #[must_use] pub fn from_json(src: &str) -> Self { Self { epochs: parse_u64_field(src, "epochs").unwrap_or(0), proven_invariants: parse_string_array(src, "proven_invariants").into_iter().collect(), learned_guards: parse_string_array(src, "learned_guards").into_iter().collect(), ..Self::default() } }
    #[must_use] pub fn load_or_new(path: &Path) -> Self { fs::read_to_string(path).map(|s| Self::from_json(&s)).unwrap_or_default() }
    pub fn absorb_invariants(&mut self, invariants: impl IntoIterator<Item = String>, guards: impl IntoIterator<Item = String>) { self.epochs = self.epochs.saturating_add(1); self.proven_invariants.extend(invariants); self.learned_guards.extend(guards); }
    #[must_use] pub fn to_json(&self) -> String {
        let fmt_arr = |set: &BTreeSet<String>| if set.is_empty() { "[]".to_string() } else { format!("[\n{}\n  ]", set.iter().map(|s| format!("    {}", json_escape(s))).collect::<Vec<_>>().join(",\n")) };
        format!("{{\n  \"schema\": \"zero-check.autopoietic/v2\",\n  \"epochs\": {},\n  \"crates_verified\": {},\n  \"files_scanned\": {},\n  \"lines_scanned\": {},\n  \"lint_errors\": {},\n  \"lint_warnings\": {},\n  \"gauntlet_passed\": {},\n  \"gauntlet_total\": {},\n  \"elapsed_us\": {},\n  \"proven_invariants\": {},\n  \"learned_guards\": {}\n}}\n", self.epochs, self.crates_verified, self.files_scanned, self.lines_scanned, self.lint_errors, self.lint_warnings, self.gauntlet_passed, self.gauntlet_total, self.elapsed_us, fmt_arr(&self.proven_invariants), fmt_arr(&self.learned_guards))
    }
    pub fn save(&self, path: &Path) -> Result<(), VerifyError> { fs::write(path, self.to_json()).map_err(|e| VerifyError::Io(format!("{}: {e}", path.display()))) } }
