use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use crate::abstract_eval::{ArchProfile, Domain, Op, Program, ProofStatus, VerifyError};
use crate::ntf1::{verify_ntf1_source, Ntf1Error};
use crate::simd_fuzz::{
    eval_lanes_x8, fault_name, prove_exhaustive, ProofVerdict, RefineConfig, FAULT_DOUBLE_FREE,
    FAULT_OOB, FAULT_UAF, FAULT_UNINIT, LANES,
};
use crate::verify_program;

#[derive(Clone, Debug)]
pub struct GauntletSummary {
    pub checks_passed: usize,
    pub checks_total: usize,
    pub proven_invariants: Vec<String>,
    pub learned_guards: Vec<String>,
    pub failures: Vec<String>,
}

impl GauntletSummary {
    #[must_use] pub fn is_clean(&self) -> bool {
        self.failures.is_empty() && self.checks_passed == self.checks_total
    }
}

/// Build the non-linear `(x * x) % 16` kernel on `x in [0, 1000]` with optional 1-point fault at `x == 777`.
#[must_use]
pub fn build_quad_mod16_kernel(with_777_fault: bool) -> Program {
    let mut p = Program::new(if with_777_fault { "quad_mod16_fault777" } else { "quad_mod16_clean" });
    let lut = p.add_buf("qr16_lut", 10, false, 1, 0, Domain::range(0, 255));
    let x = p.add_param(Domain::range(0, 1000));
    let sq = p.push(Op::Mul(x, x));
    let c16 = p.push(Op::Const(16));
    let idx = p.push(Op::Rem(sq, c16));
    let val = p.push(Op::Load { buf: lut, idx });
    if with_777_fault {
        let c777 = p.push(Op::Const(777));
        let denom = p.push(Op::Sub(x, c777));
        let q = p.push(Op::Div(val, denom));
        p.add_output(q);
    } else {
        p.add_output(idx);
    }
    p
}

fn check_miri_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    // 1. Miri-class noalias overlap knockout.
    let mut alias = Program::new("miri_noalias");
    let a = alias.add_buf("a", 16, true, 1, 0, Domain::range(0, 100));
    let b = alias.add_buf("b", 16, false, 1, 8, Domain::range(0, 100));
    let i = alias.add_param(Domain::range(0, 15));
    let v = alias.push(Op::Load { buf: b, idx: i });
    let s = alias.push(Op::Store { buf: a, idx: i, val: v });
    alias.add_output(s);
    if matches!(verify_program(&alias, ArchProfile::Aarch64Neon, RefineConfig::default()), Err(VerifyError::NoAliasViolation { .. })) {
        *passed += 1;
        guards.push("miri:noalias rejected overlapping &mut/& in region 1".to_string());
    } else { fails.push("miri:noalias failed to catch overlap".to_string()); }

    // 2. Miri-class shift UB knockout (`<< 64`).
    let mut sh = Program::new("miri_shl64");
    let x = sh.add_param(Domain::range(0, 100));
    let o = sh.push(Op::Shl(x, 64));
    sh.add_output(o);
    if matches!(verify_program(&sh, ArchProfile::X86_64Avx2, RefineConfig::default()), Err(VerifyError::ShiftOverflow { lo: 64, hi: 64, .. })) {
        *passed += 1;
        guards.push("miri:shift_ub rejected << 64 statically".to_string());
    } else { fails.push("miri:shift_ub failed to catch << 64".to_string()); }

    // 3. Miri-class interior div-by-zero CEGAR (`x == 42` in `[0, 100_000]`).
    let mut dv = Program::new("miri_div0_42");
    let xd = dv.add_param(Domain::range(0, 100_000));
    let c100 = dv.push(Op::Const(100));
    let c42 = dv.push(Op::Const(42));
    let sub = dv.push(Op::Sub(xd, c42));
    let q = dv.push(Op::Div(c100, sub));
    dv.add_output(q);
    if matches!(verify_program(&dv, ArchProfile::Aarch64Neon, RefineConfig::default()), Err(VerifyError::CounterexampleFound { inputs, .. }) if inputs == vec![42]) {
        *passed += 1;
        guards.push("miri:div0 ce=[42] isolated in [0..=100000]".to_string());
    } else { fails.push("miri:div0 failed to catch x == 42".to_string()); }

    // E-Graph static cancellation invariant.
    let mut eg = Program::new("miri_egraph");
    let tb = eg.add_buf("tbl", 16, false, 1, 0, Domain::range(0, 255));
    let xe = eg.add_param(Domain::range(0, 1000));
    let c12 = eg.push(Op::Const(12));
    let sm = eg.push(Op::Add(xe, c12));
    let df = eg.push(Op::Sub(sm, xe));
    let ld = eg.push(Op::Load { buf: tb, idx: df });
    eg.add_output(ld);
    if matches!(verify_program(&eg, ArchProfile::Aarch64Neon, RefineConfig::default()), Ok(r) if r.abstract_report.status == ProofStatus::ProvenSafe) {
        inv.push("miri:egraph (x + 12) - x == 12 statically proven on x in 0..=1000".to_string());
    }
}

fn check_asan_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    // 4. ASan-class 1-byte OOB + guard synthesis.
    let mut oob = Program::new("asan_oob16");
    let b = oob.add_buf("arr", 16, false, 1, 0, Domain::range(0, 255));
    let x = oob.add_param(Domain::range(0, 16));
    let v = oob.push(Op::Load { buf: b, idx: x });
    oob.add_output(v);
    match prove_exhaustive(&oob, RefineConfig::default()) {
        ProofVerdict::Counterexample { input, fault, synthesized_guard, .. }
            if input == vec![16] && (fault & FAULT_OOB) != 0 && synthesized_guard == "p0 in 0..=15" =>
        {
            *passed += 1;
            guards.push(format!("asan:oob16 fault={} ce={input:?} guard=({synthesized_guard})", fault_name(fault)));
        }
        other => fails.push(format!("asan:oob16 unexpected verdict: {other:?}")),
    }

    // 5. ASan-class Use-After-Free (static + 8-lane SIMD replay).
    let mut uaf = Program::new("asan_uaf");
    let bu = uaf.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    let iu = uaf.add_param(Domain::range(0, 15));
    uaf.push(Op::Free(bu));
    let lu = uaf.push(Op::Load { buf: bu, idx: iu });
    uaf.add_output(lu);
    let uaf_static = verify_program(&uaf, ArchProfile::Aarch64Neon, RefineConfig::default());
    let uaf_simd = eval_lanes_x8(&uaf, &[[0; LANES]]);
    if let Err(VerifyError::UseAfterFree { buf, generation, .. }) = uaf_static {
        if uaf_simd.faults.iter().all(|&f| (f & FAULT_UAF) != 0) {
            *passed += 1;
            guards.push(format!("asan:uaf fault=UseAfterFree buf={buf} gen={generation} simd_lanes=8/8"));
        } else { fails.push("asan:uaf SIMD replay missed FAULT_UAF".to_string()); }
    } else { fails.push(format!("asan:uaf static missed UAF: {uaf_static:?}")); }

    // 6. ASan-class Double-Free (static + 8-lane SIMD replay).
    let mut df = Program::new("asan_double_free");
    let bd = df.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    df.push(Op::Free(bd));
    let f2 = df.push(Op::Free(bd));
    df.add_output(f2);
    let df_static = verify_program(&df, ArchProfile::Aarch64Neon, RefineConfig::default());
    let df_simd = eval_lanes_x8(&df, &[]);
    if let Err(VerifyError::DoubleFree { buf, generation, .. }) = df_static {
        if df_simd.faults.iter().all(|&f| (f & FAULT_DOUBLE_FREE) != 0) {
            *passed += 1;
            guards.push(format!("asan:double_free fault=DoubleFree buf={buf} gen={generation} simd_lanes=8/8"));
        } else { fails.push("asan:double_free SIMD replay missed FAULT_DOUBLE_FREE".to_string()); }
    } else { fails.push(format!("asan:double_free static missed DoubleFree: {df_static:?}")); }

    // 7. ASan-class Uninitialized-Read vs Store-before-Load (static + 8-lane SIMD replay).
    let mut uninit = Program::new("asan_uninit");
    let bn = uninit.add_uninit_buf("scratch", 16, true, 1, 0, Domain::range(0, 255));
    let ix = uninit.add_param(Domain::range(0, 15));
    let ln = uninit.push(Op::Load { buf: bn, idx: ix });
    uninit.add_output(ln);
    let mut init_ok = Program::new("asan_init_ok");
    let bi = init_ok.add_uninit_buf("scratch", 16, true, 1, 0, Domain::range(0, 255));
    let ii = init_ok.add_param(Domain::range(0, 15));
    let cv = init_ok.push(Op::Const(7));
    init_ok.push(Op::Store { buf: bi, idx: ii, val: cv });
    let li = init_ok.push(Op::Load { buf: bi, idx: ii });
    init_ok.add_output(li);
    let u_bad = verify_program(&uninit, ArchProfile::Aarch64Neon, RefineConfig::default());
    let u_ok = verify_program(&init_ok, ArchProfile::Aarch64Neon, RefineConfig::default());
    let u_simd = eval_lanes_x8(&uninit, &[[0, 1, 2, 3, 4, 5, 6, 7]]);
    if matches!(u_bad, Err(VerifyError::UninitializedRead { .. })) && u_ok.is_ok() && u_simd.faults.iter().all(|&f| (f & FAULT_UNINIT) != 0) {
        *passed += 1;
        inv.push("asan:init_mask store(buf[x]) -> load(buf[x]) proven initialized".to_string());
        guards.push("asan:uninit fault=UninitializedRead buf=0 idx=[0..=15] simd_lanes=8/8".to_string());
    } else { fails.push("asan:uninit knockout failed".to_string()); }
}

fn check_kani_and_arch_suite(inv: &mut Vec<String>, guards: &mut Vec<String>, fails: &mut Vec<String>, passed: &mut usize) {
    // 8. Kani-class exhaustive ProvenTotal on `(x * x) % 16` across `x in [0, 1000]` vs 1-point failure at `x == 777`.
    let clean = build_quad_mod16_kernel(false);
    let buggy = build_quad_mod16_kernel(true);
    let v_clean = prove_exhaustive(&clean, RefineConfig::default());
    let v_buggy = prove_exhaustive(&buggy, RefineConfig::default());
    match (v_clean, v_buggy) {
        (
            ProofVerdict::ProvenTotal { boxes_discharged, learned_invariants },
            ProofVerdict::Counterexample { input, fault, synthesized_guard, .. },
        ) if boxes_discharged > 0 && input == vec![777] && synthesized_guard == "p0 in 0..=776 || p0 in 778..=1000" => {
            *passed += 1;
            inv.push(format!("kani:quad_mod16 ProvenTotal boxes={boxes_discharged} domain=[0..=1000]"));
            for li in learned_invariants { inv.push(format!("kani:quad_mod16 {li}")); }
            guards.push(format!("kani:quad_mod16_777 fault={} ce={input:?} guard=({synthesized_guard})", fault_name(fault)));
        }
        (vc, vb) => fails.push(format!("kani:quad_mod16 unexpected: clean={vc:?}, buggy={vb:?}")),
    }

    // 9. Dual-architecture 20-live-reg AVX2 spill vs NEON pass guard.
    let mut k20 = Program::new("arch_20reg");
    k20.simd_lanes = 2;
    for _ in 0..20 {
        let p = k20.add_param(Domain::range(0, 1000));
        k20.add_output(p);
    }
    let avx = verify_program(&k20, ArchProfile::X86_64Avx2, RefineConfig::default());
    let neon = verify_program(&k20, ArchProfile::Aarch64Neon, RefineConfig::default());
    if matches!(avx, Err(VerifyError::RegisterSpill { peak_gprs: 20, max_gprs: 14, .. })) && neon.is_ok() {
        *passed += 1;
        inv.push("arch:20reg avx2=spill(20/14) neon=pass(20/28,20/32)".to_string());
    } else { fails.push("arch:20reg dual-arch spill knockout failed".to_string()); }

    // 10. NTF1 causal airlock + zero-SVO + retro-causal completeness knockout.
    let valid_ntf1 = "NTF1 airlock\n+t zero_cc -> zero_check\n+t zero_check -> Fault.Spill\n-t Fault.Spill <- Guard.Avx2\n0t zero_cc >< zero_check\n";
    let svo_ntf1 = "NTF1 airlock\n# this is prose\n+t a -> b\n";
    let uncov_ntf1 = "NTF1 airlock\n+t a -> Fault.Leak\n";
    let ok = verify_ntf1_source("inline.ntf1", valid_ntf1);
    let bad_svo = verify_ntf1_source("svo.ntf1", svo_ntf1);
    let bad_cov = verify_ntf1_source("uncov.ntf1", uncov_ntf1);
    if matches!(ok, Ok(ref r) if r.canonical_idempotent && r.faults_covered == 1)
        && matches!(bad_svo, Err(Ntf1Error::SvoTax { .. }))
        && matches!(bad_cov, Err(Ntf1Error::UncoveredFault { .. }))
    {
        *passed += 1;
        inv.push("ntf1:airlock canonical_idempotent=true faults_covered=1".to_string());
        guards.push("ntf1:svo_and_retro rejected SVO prose and uncovered Fault.Leak".to_string());
    } else { fails.push("ntf1:airlock knockout failed".to_string()); }
}

/// Run the full Miri-class + ASan-class + Kani-class + AVX2/NEON + NTF1 self-verification gauntlet.
#[must_use]
pub fn run_gauntlet() -> GauntletSummary {
    let (mut inv, mut guards, mut fails, mut passed) = (Vec::new(), Vec::new(), Vec::new(), 0usize);
    check_miri_suite(&mut inv, &mut guards, &mut fails, &mut passed);
    check_asan_suite(&mut inv, &mut guards, &mut fails, &mut passed);
    check_kani_and_arch_suite(&mut inv, &mut guards, &mut fails, &mut passed);
    GauntletSummary {
        checks_passed: passed, checks_total: 10,
        proven_invariants: inv, learned_guards: guards, failures: fails,
    }
}

/// Zero-dependency autopoietic JSON ledger persisting proven invariants and learned guards across runs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AutopoieticLedger {
    pub epochs: u64,
    pub crates_verified: usize,
    pub files_scanned: usize,
    pub lines_scanned: usize,
    pub lint_errors: usize,
    pub lint_warnings: usize,
    pub gauntlet_passed: usize,
    pub gauntlet_total: usize,
    pub elapsed_us: u64,
    pub proven_invariants: BTreeSet<String>,
    pub learned_guards: BTreeSet<String>,
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for b in s.bytes() {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7E => out.push(b as char),
            other => out.push_str(&format!("\\u00{other:02x}")),
        }
    }
    out.push('"');
    out
}

fn json_unescape(raw: &str) -> String {
    let bytes = raw.as_bytes();
    let (mut out, mut i) = (String::with_capacity(bytes.len()), 0usize);
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 1 < bytes.len() {
            match bytes[i + 1] {
                b'"' => out.push('"'),
                b'\\' => out.push('\\'),
                b'n' => out.push('\n'),
                b'r' => out.push('\r'),
                b't' => out.push('\t'),
                other => out.push(other as char),
            }
            i += 2;
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

fn parse_u64_field(src: &str, key: &str) -> Option<u64> {
    let needle = format!("\"{key}\"");
    let pos = src.find(&needle)? + needle.len();
    let rest = src[pos..].trim_start().strip_prefix(':')?.trim_start();
    let end = rest.bytes().take_while(u8::is_ascii_digit).count();
    rest[..end].parse::<u64>().ok()
}

fn parse_string_array(src: &str, key: &str) -> Vec<String> {
    let needle = format!("\"{key}\"");
    let Some(pos) = src.find(&needle) else { return Vec::new(); };
    let rest = &src[pos + needle.len()..];
    let Some(lb) = rest.find('[') else { return Vec::new(); };
    let bytes = &rest.as_bytes()[lb + 1..];
    let (mut out, mut i) = (Vec::new(), 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b']' => break,
            b'"' => {
                i += 1;
                let start = i;
                while i < bytes.len() {
                    if bytes[i] == b'\\' && i + 1 < bytes.len() { i += 2; }
                    else if bytes[i] == b'"' { break; }
                    else { i += 1; }
                }
                if i < bytes.len() { out.push(json_unescape(&rest[lb + 1 + start..lb + 1 + i])); i += 1; }
            }
            _ => i += 1,
        }
    }
    out
}

impl AutopoieticLedger {
    #[must_use]
    pub fn from_json(src: &str) -> Self {
        Self {
            epochs: parse_u64_field(src, "epochs").unwrap_or(0),
            proven_invariants: parse_string_array(src, "proven_invariants").into_iter().collect(),
            learned_guards: parse_string_array(src, "learned_guards").into_iter().collect(),
            ..Self::default()
        }
    }

    #[must_use]
    pub fn load_or_new(path: &Path) -> Self {
        fs::read_to_string(path).map(|s| Self::from_json(&s)).unwrap_or_default()
    }

    pub fn absorb_invariants(&mut self, invariants: impl IntoIterator<Item = String>, guards: impl IntoIterator<Item = String>) {
        self.epochs = self.epochs.saturating_add(1);
        self.proven_invariants.extend(invariants);
        self.learned_guards.extend(guards);
    }

    #[must_use]
    pub fn to_json(&self) -> String {
        let fmt_arr = |set: &BTreeSet<String>| -> String {
            if set.is_empty() { return "[]".to_string(); }
            let items: Vec<String> = set.iter().map(|s| format!("    {}", json_escape(s))).collect();
            format!("[\n{}\n  ]", items.join(",\n"))
        };
        format!(
            concat!(
                "{{\n",
                "  \"schema\": \"zero-check.autopoietic/v2\",\n",
                "  \"epochs\": {},\n",
                "  \"crates_verified\": {},\n",
                "  \"files_scanned\": {},\n",
                "  \"lines_scanned\": {},\n",
                "  \"lint_errors\": {},\n",
                "  \"lint_warnings\": {},\n",
                "  \"gauntlet_passed\": {},\n",
                "  \"gauntlet_total\": {},\n",
                "  \"elapsed_us\": {},\n",
                "  \"proven_invariants\": {},\n",
                "  \"learned_guards\": {}\n",
                "}}\n"
            ),
            self.epochs, self.crates_verified, self.files_scanned, self.lines_scanned,
            self.lint_errors, self.lint_warnings, self.gauntlet_passed, self.gauntlet_total,
            self.elapsed_us, fmt_arr(&self.proven_invariants), fmt_arr(&self.learned_guards),
        )
    }

    pub fn save(&self, path: &Path) -> Result<(), VerifyError> {
        fs::write(path, self.to_json()).map_err(|e| VerifyError::Io(format!("{}: {e}", path.display())))
    }
}
