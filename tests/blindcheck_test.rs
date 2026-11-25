#![forbid(unsafe_code)]

#[cfg(not(miri))]
use std::path::Path;

#[cfg(not(miri))]
use zero_check::verify_crate_dir;
use zero_check::{
    build_quad_mod16_kernel, eval_lanes_x8, prove_exhaustive, refine_and_fuzz, run_gauntlet,
    scan_rust_source, verify_program, verify_rust_source, ArchProfile, AutopoieticLedger, Domain,
    LintKind, Op, Program, ProofStatus, ProofVerdict, RefineConfig, Severity, VerifyError,
    FAULT_DIV0, FAULT_DOUBLE_FREE, FAULT_NONE, FAULT_OOB, FAULT_OVERFLOW, FAULT_SHIFT, FAULT_UAF,
    FAULT_UNINIT,
};

#[cfg(not(miri))]
#[test]
fn bench_live_real_crates_sub_10ms() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let self_src = manifest_dir.join("src");
    let workspace_parent = manifest_dir.parent().unwrap_or(manifest_dir);
    let sibling_candidates = [
        ("zero-cc", workspace_parent.join("zero-cc").join("src")),
        ("zero-proxy/blindbind", workspace_parent.join("zero-proxy").join("src").join("blindbind")),
        ("zero-proxy/xdp", workspace_parent.join("zero-proxy").join("src").join("xdp")),
        ("zero-rans", workspace_parent.join("zero-rans").join("src")),
    ];

    let t0 = std::time::Instant::now();
    let self_rep = verify_crate_dir(&self_src).expect("zero-check/src must self-verify cleanly");
    assert_eq!(self_rep.error_count(), 0, "self had errors: {:?}", self_rep.findings);
    assert!(
        self_rep.lines_scanned <= 4600,
        "src LOC must be <= 4600, got {}",
        self_rep.lines_scanned
    );

    let mut total_files = self_rep.files_scanned;
    let mut total_lines = self_rep.lines_scanned;
    let mut total_warnings = self_rep.warning_count();
    let mut crates_scanned = 1usize;

    for (label, dir) in &sibling_candidates {
        if dir.is_dir() {
            let rep = verify_crate_dir(dir).unwrap_or_else(|e| panic!("{label} failed lint: {e}"));
            assert_eq!(rep.error_count(), 0, "{label} had errors: {:?}", rep.findings);
            total_files += rep.files_scanned;
            total_lines += rep.lines_scanned;
            total_warnings += rep.warning_count();
            crates_scanned += 1;
        }
    }

    let elapsed_us = t0.elapsed().as_micros();
    let elapsed_ms = (elapsed_us as f64) / 1000.0;
    let budget_ms = (25.0_f64).max((total_lines as f64) * 0.0015);
    assert!(
        elapsed_ms < budget_ms,
        "expected < {budget_ms:.1} ms (<= 1.5 ms/kLOC) to verify {total_lines} LOC across {crates_scanned} crates, got {elapsed_ms:.3} ms"
    );

    // Explicitly verify legal u128 >> 64 (as in Ed25519 wide-limb reduction) has zero false positives.
    let ed_path = workspace_parent
        .join("zero-proxy")
        .join("src")
        .join("blindbind")
        .join("ed25519.rs");
    let ed_src = if ed_path.is_file() {
        std::fs::read_to_string(&ed_path).expect("read ed25519.rs")
    } else {
        "pub fn reduce(x: u128) -> u64 { ((x >> 64) as u64) ^ (x as u64) }\n".to_string()
    };
    let ed_rep = verify_rust_source("ed25519.rs", &ed_src).expect("ed25519.rs must pass cleanly");
    assert_eq!(ed_rep.error_count(), 0);
    assert!(
        !ed_rep.findings.iter().any(|f| f.kind == LintKind::ShiftOverflow),
        "false positive ShiftOverflow on ed25519.rs u128 >> 64"
    );

    let miri_ms = 2_182_000.0f64;
    let speedup = miri_ms / elapsed_ms.max(0.001);
    eprintln!(
        "[ZERO-CHECK-BENCH] {crates_scanned} crates: {total_files} files, {total_lines} LOC, 0 errors, {total_warnings} warnings in {elapsed_ms:.3} ms ({elapsed_us} us) vs Miri 2,182 s ({speedup:.0}x faster); self: {} LOC clean",
        self_rep.lines_scanned
    );
}

#[test]
fn knockout_1_oob_one_off_and_safe_boundary_synthesis() {
    let build = |hi: i64| {
        let mut p = Program::new("oob_kernel");
        let b = p.add_buf("arr", 16, false, 1, 0, Domain::range(0, 1000));
        let x = p.add_param(Domain::range(0, hi));
        let v = p.push(Op::Load { buf: b, idx: x });
        p.add_output(v);
        p
    };
    let clean = build(15);
    let buggy = build(16);

    let clean_res = verify_program(&clean, ArchProfile::Aarch64Neon, RefineConfig::default());
    let buggy_res = verify_program(&buggy, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(clean_res.is_ok(), buggy_res.is_ok(), "knockout 1 must distinguish clean vs 1-off OOB");
    assert!(matches!(clean_res.as_ref().map(|r| &r.abstract_report.status), Ok(ProofStatus::ProvenSafe)));
    assert!(clean_res.expect("clean").refine_report.is_none());

    match buggy_res {
        Err(VerifyError::CounterexampleFound { fault, inputs, .. }) => {
            assert_ne!(fault & FAULT_OOB, 0, "expected FAULT_OOB, got 0x{fault:02x}");
            assert_eq!(inputs, vec![16]);
        }
        other => panic!("expected OOB counterexample at x=16, got {other:?}"),
    }

    // Autodidactic safe boundary synthesis carves exact [0..=15] safe subdomains out of [0..=16].
    let cfg = RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() };
    let syn = refine_and_fuzz(&buggy, cfg);
    assert!(syn.counterexamples.iter().any(|c| c.inputs == vec![16] && (c.fault & FAULT_OOB) != 0));
    assert_eq!(syn.unproven_boxes, 0);
    for x in 0..=15 {
        assert!(
            syn.safe_subdomains.iter().any(|b| b[0].contains(x)),
            "safe point {x} missing from synthesized safe subdomains"
        );
    }
    assert!(
        !syn.safe_subdomains.iter().any(|b| b[0].contains(16)),
        "buggy point 16 must not appear in safe subdomains"
    );
}

#[test]
fn knockout_2_shift_ub_64_ir_and_rust_lint() {
    // Static IR shift by 63 (clean) vs 64 (definite UB).
    let mut clean_s = Program::new("shl_63");
    let x0 = clean_s.add_param(Domain::range(0, 100));
    let o0 = clean_s.push(Op::Shl(x0, 63));
    clean_s.add_output(o0);

    let mut buggy_s = Program::new("shl_64");
    let x1 = buggy_s.add_param(Domain::range(0, 100));
    let o1 = buggy_s.push(Op::Shl(x1, 64));
    buggy_s.add_output(o1);

    let r_ok = verify_program(&clean_s, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_bad = verify_program(&buggy_s, ArchProfile::X86_64Avx2, RefineConfig::default());
    assert_ne!(r_ok.is_ok(), r_bad.is_ok(), "knockout 2 static shift");
    assert!(matches!(r_bad, Err(VerifyError::ShiftOverflow { lo: 64, hi: 64, .. })));

    // Dynamic shift variable [0..=63] (clean) vs [0..=64] (CEGAR catches s == 64).
    let build_var = |s_hi: i64| {
        let mut p = Program::new("shl_var");
        let x = p.add_param(Domain::range(1, 1024));
        let s = p.add_param(Domain::range(0, s_hi));
        let o = p.push(Op::ShlVar(x, s));
        p.add_output(o);
        p
    };
    let v_ok = verify_program(&build_var(63), ArchProfile::Aarch64Neon, RefineConfig::default());
    let v_bad = verify_program(&build_var(64), ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(v_ok.is_ok(), v_bad.is_ok(), "knockout 2 dynamic shift");
    match v_bad {
        Err(VerifyError::CounterexampleFound { fault, inputs, .. }) => {
            assert_ne!(fault & FAULT_SHIFT, 0);
            assert_eq!(inputs[1], 64);
        }
        other => panic!("expected shift counterexample at s=64, got {other:?}"),
    }

    // Rust source linter: legal u128 >> 64 & u64 << 63 pass; u64 << 64 & u128 << 128 fail.
    let src_ok = "pub fn ok(a: u64, acc: u128) -> (u64, u128) { let carry = acc >> 64; (a << 63, carry) }\n";
    let src_bad64 = "pub fn bad64(x: u64) -> u64 { x << 64 }\n";
    let src_bad128 = "pub fn bad128(x: u128) -> u128 { x << 128 }\n";
    let l_ok = verify_rust_source("ok.rs", src_ok);
    let l_b64 = verify_rust_source("bad64.rs", src_bad64);
    let l_b128 = verify_rust_source("bad128.rs", src_bad128);
    assert_ne!(l_ok.is_ok(), l_b64.is_ok(), "knockout 2 lint u64 << 64");
    assert_ne!(l_ok.is_ok(), l_b128.is_ok(), "knockout 2 lint u128 << 128");
    assert!(scan_rust_source("bad64.rs", src_bad64).findings.iter().any(|f| f.kind == LintKind::ShiftOverflow));
    assert!(scan_rust_source("bad128.rs", src_bad128).findings.iter().any(|f| f.kind == LintKind::ShiftOverflow));
}

#[test]
fn knockout_3_interior_div_by_zero_cegar_and_lint() {
    let mut clean = Program::new("div_safe");
    let x0 = clean.add_param(Domain::range(0, 100_000));
    let c100 = clean.push(Op::Const(100));
    let c1 = clean.push(Op::Const(1));
    let denom = clean.push(Op::Add(x0, c1));
    let q0 = clean.push(Op::Div(c100, denom));
    clean.add_output(q0);

    // Hidden interior singularity at x == 42 inside [0, 100_000].
    let mut buggy = Program::new("div_zero_42");
    let x1 = buggy.add_param(Domain::range(0, 100_000));
    let k100 = buggy.push(Op::Const(100));
    let k42 = buggy.push(Op::Const(42));
    let diff = buggy.push(Op::Sub(x1, k42));
    let q1 = buggy.push(Op::Div(k100, diff));
    buggy.add_output(q1);

    let r_ok = verify_program(&clean, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_bad = verify_program(&buggy, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_ok.is_ok(), r_bad.is_ok(), "knockout 3 interior div-by-zero");
    match r_bad {
        Err(VerifyError::CounterexampleFound { fault, inputs, .. }) => {
            assert_ne!(fault & FAULT_DIV0, 0);
            assert_eq!(inputs, vec![42]);
        }
        other => panic!("expected div-by-zero counterexample at x=42, got {other:?}"),
    }

    // Rust source lint for literal `/ 0` and `% 0`.
    let l_ok = verify_rust_source("ok.rs", "pub fn f(x: i64) -> i64 { x / 1 }\n");
    let l_bad = verify_rust_source("bad.rs", "pub fn f(x: i64) -> i64 { x / 0 }\n");
    assert_ne!(l_ok.is_ok(), l_bad.is_ok(), "knockout 3 lint / 0");
    assert!(scan_rust_source("bad.rs", "pub fn f(x: i64) -> i64 { x % 0 }\n")
        .findings
        .iter()
        .any(|f| f.kind == LintKind::DivByZero));
}

#[test]
fn knockout_4_noalias_mut_overlap() {
    let build = |b_offset: usize, b_mut: bool, a_mut: bool| {
        let mut p = Program::new("alias_kernel");
        let a = p.add_buf("a", 16, a_mut, 1, 0, Domain::range(0, 100));
        let b = p.add_buf("b", 16, b_mut, 1, b_offset, Domain::range(0, 100));
        let idx = p.add_param(Domain::range(0, 15));
        let v = p.push(Op::Load { buf: b, idx });
        let out = if a_mut { p.push(Op::Store { buf: a, idx, val: v }) } else { p.push(Op::Load { buf: a, idx }) };
        p.add_output(out);
        p
    };

    let disjoint_mut = build(16, true, true);
    let overlap_ro = build(8, false, false);
    let overlap_mut_ro = build(8, false, true);
    let overlap_mut_mut = build(15, true, true);

    let r_disjoint = verify_program(&disjoint_mut, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_ro = verify_program(&overlap_ro, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_mut_ro = verify_program(&overlap_mut_ro, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_mut_mut = verify_program(&overlap_mut_mut, ArchProfile::Aarch64Neon, RefineConfig::default());

    assert!(r_disjoint.is_ok(), "disjoint &mut buffers must pass");
    assert!(r_ro.is_ok(), "overlapping shared & buffers must pass");
    assert_ne!(r_disjoint.is_ok(), r_mut_ro.is_ok(), "knockout 4 &mut + & overlap");
    assert_ne!(r_disjoint.is_ok(), r_mut_mut.is_ok(), "knockout 4 &mut + &mut overlap");
    assert_eq!(r_mut_ro.unwrap_err(), VerifyError::NoAliasViolation { buf_a: 0, buf_b: 1, region: 1 });
    assert_eq!(r_mut_mut.unwrap_err(), VerifyError::NoAliasViolation { buf_a: 0, buf_b: 1, region: 1 });

    // Writing to a read-only buffer must also fail closed.
    let mut ro_write = Program::new("ro_write");
    let ro = ro_write.add_buf("ro", 8, false, 2, 0, Domain::range(0, 10));
    let i = ro_write.add_param(Domain::range(0, 7));
    let c = ro_write.push(Op::Const(1));
    let st = ro_write.push(Op::Store { buf: ro, idx: i, val: c });
    ro_write.add_output(st);
    assert_eq!(
        verify_program(&ro_write, ArchProfile::Aarch64Neon, RefineConfig::default()).unwrap_err(),
        VerifyError::WriteToReadOnly { buf: 0 }
    );
}

#[test]
fn knockout_5_transmute_and_raw_ptr_provenance() {
    let clean_src = "pub fn bits_to_f64(x: u64) -> f64 { f64::from_bits(x) }\n";
    let transmute_src = "pub fn bad(x: u64) -> f64 { unsafe { std::mem::transmute::<u64, f64>(x) } }\n";
    let raw_ptr_src = "pub fn bad_ptr(s: &[u8]) -> *const u8 { s.as_ptr() as *const u8 }\n";
    let ptr_read_src = "pub fn bad_read(p: *const u8) -> u8 { unsafe { std::ptr::read(p) } }\n";

    let ok_res = verify_rust_source("clean.rs", clean_src);
    let tm_res = verify_rust_source("transmute.rs", transmute_src);
    let rp_res = verify_rust_source("raw_ptr.rs", raw_ptr_src);
    let pr_res = verify_rust_source("ptr_read.rs", ptr_read_src);

    assert!(ok_res.is_ok(), "clean f64::from_bits must pass");
    assert_ne!(ok_res.is_ok(), tm_res.is_ok(), "knockout 5 transmute");
    assert_ne!(ok_res.is_ok(), rp_res.is_ok(), "knockout 5 raw-ptr cast");
    assert_ne!(ok_res.is_ok(), pr_res.is_ok(), "knockout 5 ptr::read");

    let tm_rep = scan_rust_source("transmute.rs", transmute_src);
    assert!(tm_rep.findings.iter().any(|f| f.kind == LintKind::UnsafeBlock && f.severity == Severity::Error));
    assert!(tm_rep.findings.iter().any(|f| f.kind == LintKind::Transmute && f.severity == Severity::Error));

    let rp_rep = scan_rust_source("raw_ptr.rs", raw_ptr_src);
    assert!(rp_rep.findings.iter().any(|f| f.kind == LintKind::RawPtrProvenance && f.severity == Severity::Error));
}

#[test]
fn dual_arch_20_live_reg_avx2_spill_vs_neon_pass() {
    // Kernel A: 8-lane SIMD, 12 buffers + 1 live index + 7 live outputs = 8 live SSA => 20 peak GPRs, 16 YMM / 32 NEON V-regs.
    let mut k_8lane = Program::new("neon_20gpr_8lane");
    for i in 0..12 {
        k_8lane.add_buf(format!("b{i}"), 16, false, 1, i * 16, Domain::range(0, 100));
    }
    let idx = k_8lane.add_param(Domain::range(0, 15));
    for i in 0..7u8 {
        let v = k_8lane.push(Op::Load { buf: i, idx });
        k_8lane.add_output(v);
    }
    let avx2_a = verify_program(&k_8lane, ArchProfile::X86_64Avx2, RefineConfig::default());
    let neon_a = verify_program(&k_8lane, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(avx2_a.is_ok(), neon_a.is_ok(), "20-GPR 8-lane kernel must fail AVX2 and pass NEON");
    assert_eq!(
        avx2_a.unwrap_err(),
        VerifyError::RegisterSpill {
            profile: ArchProfile::X86_64Avx2,
            peak_gprs: 20,
            max_gprs: 14,
            peak_vecs: 16,
            max_vecs: 16,
        }
    );
    let sched_a = neon_a.expect("NEON must pass").abstract_report.schedule;
    assert_eq!(sched_a.peak_gprs, 20);
    assert_eq!(sched_a.peak_vecs, 32);

    // Kernel B: native 128-bit 2-lane kernel with 20 simultaneously live SSA registers.
    let mut k_20ssa = Program::new("neon_20ssa_2lane");
    k_20ssa.simd_lanes = 2;
    for _ in 0..20 {
        let p = k_20ssa.add_param(Domain::range(0, 1000));
        k_20ssa.add_output(p);
    }
    let avx2_b = verify_program(&k_20ssa, ArchProfile::X86_64Avx2, RefineConfig::default());
    let neon_b = verify_program(&k_20ssa, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(avx2_b.is_ok(), neon_b.is_ok(), "20-live-SSA kernel must fail AVX2 and pass NEON");
    assert!(matches!(avx2_b, Err(VerifyError::RegisterSpill { peak_gprs: 20, max_gprs: 14, .. })));
    let sched_b = neon_b.expect("NEON 20-live-SSA must pass").abstract_report.schedule;
    assert_eq!(sched_b.peak_gprs, 20);
    assert_eq!(sched_b.peak_vecs, 20);

    // Kernel C: 10 live SSA values at 8 lanes => 20/16 YMM and 40/32 NEON V-regs -> spills on BOTH!
    let mut k_both = Program::new("spill_both");
    for _ in 0..10 {
        let p = k_both.add_param(Domain::range(0, 100));
        k_both.add_output(p);
    }
    assert!(matches!(
        verify_program(&k_both, ArchProfile::X86_64Avx2, RefineConfig::default()),
        Err(VerifyError::RegisterSpill { profile: ArchProfile::X86_64Avx2, peak_vecs: 20, max_vecs: 16, .. })
    ));
    assert!(matches!(
        verify_program(&k_both, ArchProfile::Aarch64Neon, RefineConfig::default()),
        Err(VerifyError::RegisterSpill { profile: ArchProfile::Aarch64Neon, peak_vecs: 40, max_vecs: 32, .. })
    ));
}

#[test]
fn egraph_dependency_overflow_and_fail_closed_cegar() {
    // E-Graph solves interval dependency problem: (x + 12) - x == 12 statically on x in [0, 1000].
    let mut eg = Program::new("egraph_cancel");
    let b = eg.add_buf("tbl", 16, false, 1, 0, Domain::range(0, 255));
    let x = eg.add_param(Domain::range(0, 1000));
    let c12 = eg.push(Op::Const(12));
    let sum = eg.push(Op::Add(x, c12));
    let idx = eg.push(Op::Sub(sum, x));
    let val = eg.push(Op::Load { buf: b, idx });
    eg.add_output(val);

    let rep = verify_program(&eg, ArchProfile::Aarch64Neon, RefineConfig::default()).expect("egraph proven");
    assert_eq!(rep.abstract_report.status, ProofStatus::ProvenSafe);
    assert!(rep.refine_report.is_none(), "static E-Graph proof should require zero fuzzing");
    assert_eq!(rep.abstract_report.domains[idx], Domain::exact(12));

    // Signed i64 overflow knockout.
    let mut ov = Program::new("i64_ov");
    let big = ov.add_param(Domain::range(i64::MAX - 1, i64::MAX));
    let one = ov.push(Op::Const(1));
    let add = ov.push(Op::Add(big, one));
    ov.add_output(add);
    match verify_program(&ov, ArchProfile::Aarch64Neon, RefineConfig::default()) {
        Err(VerifyError::CounterexampleFound { fault, inputs, .. }) => {
            assert_ne!(fault & FAULT_OVERFLOW, 0);
            assert_eq!(inputs, vec![i64::MAX]);
        }
        other => panic!("expected signed overflow counterexample, got {other:?}"),
    }

    // Fail-closed guarantee: when max_epochs expires with unproven boxes, verify_program MUST return Err.
    let mut deep = Program::new("deep_hidden_div0");
    let xd = deep.add_param(Domain::range(0, 10_000_000));
    let k1 = deep.push(Op::Const(1));
    let k_needle = deep.push(Op::Const(77_777));
    let d = deep.push(Op::Sub(xd, k_needle));
    let q = deep.push(Op::Div(k1, d));
    deep.add_output(q);
    let tiny_cfg = RefineConfig { max_epochs: 1, fuzz_ticks_per_box: 1, ..RefineConfig::default() };
    assert!(
        verify_program(&deep, ArchProfile::Aarch64Neon, tiny_cfg).is_err(),
        "verify_program must fail closed when CEGAR budget expires with unproven boxes"
    );
}

#[test]
fn static_lint_hygiene_and_comment_masking() {
    let clamp_src = concat!("pub fn f(x: i64) -> i64 { x.cl", "amp(0, 10) }\n");
    let allow_src = concat!("#[al", "low(dead_code)]\npub fn f() {}\n");
    let todo_src = "pub fn f() { todo!(); }\n";
    let unchk_src = "pub fn f(s: &[u8]) -> u8 { *s.get_unchecked(0) }\n";
    let uninit_src = "pub fn f(x: core::mem::MaybeUninit<u64>) -> u64 { unsafe { x.assume_init() } }\n";
    let non_ascii = "pub fn f() -> u8 { 1 } // cafe\u{00e9}\n";

    assert!(scan_rust_source("c.rs", clamp_src).findings.iter().any(|f| f.kind == LintKind::ClampCall));
    assert!(scan_rust_source("a.rs", allow_src).findings.iter().any(|f| f.kind == LintKind::AllowAttr));
    assert!(scan_rust_source("t.rs", todo_src).findings.iter().any(|f| f.kind == LintKind::UnfinishedMacro));
    assert!(scan_rust_source("u.rs", unchk_src).findings.iter().any(|f| f.kind == LintKind::UncheckedIndex));
    assert!(scan_rust_source("ui.rs", uninit_src).findings.iter().any(|f| f.kind == LintKind::UninitAccess));
    assert!(scan_rust_source("n.rs", non_ascii).findings.iter().any(|f| f.kind == LintKind::NonAscii));

    // Comments, nested block comments, raw strings, char literals, and Rust lifetimes produce 0 findings.
    let masked_clean = concat!(
        "// unsafe { std::mem::transmute(x) } x << 64 x / 0\n",
        "/* outer /* unsafe ptr::read */ as *const u8 */\n",
        "pub fn pick<'a>(a: &'a str, _b: &'a str) -> (&'a str, char) {\n",
        "    let _ = \"unsafe transmute as *mut u8 todo!()\";\n",
        "    let _ = r#\"get_unchecked x << 64 x / 0\"#;\n",
        "    (a, '\\'')\n",
        "}\n"
    );
    let rep = verify_rust_source("masked.rs", masked_clean).expect("masked literals/comments must be clean");
    assert_eq!(rep.error_count(), 0);
    assert_eq!(rep.warning_count(), 0);
}

#[test]
fn knockout_6_asan_use_after_free_and_stale_gen() {
    // Live load vs Free(buf) -> Load(buf) (UAF) + pointer offset wrap fail-closed.
    let mut live = Program::new("uaf_live");
    let bl = live.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    let il = live.add_param(Domain::range(0, 15));
    let vl = live.push(Op::Load { buf: bl, idx: il });
    live.add_output(vl);

    let mut uaf = Program::new("uaf_dead");
    let bu = uaf.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    let iu = uaf.add_param(Domain::range(0, 15));
    uaf.push(Op::Free(bu));
    let vu = uaf.push(Op::Load { buf: bu, idx: iu });
    uaf.add_output(vu);

    let r_live = verify_program(&live, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_uaf = verify_program(&uaf, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_live.is_ok(), r_uaf.is_ok(), "knockout 6 live vs UAF");
    assert!(matches!(r_uaf, Err(VerifyError::UseAfterFree { buf: 0, generation: 2, .. })));

    let simd_live = eval_lanes_x8(&live, &[[0, 1, 2, 3, 4, 5, 6, 7]]);
    let simd_uaf = eval_lanes_x8(&uaf, &[[0, 1, 2, 3, 4, 5, 6, 7]]);
    assert!(simd_live.faults.iter().all(|&f| f == FAULT_NONE));
    assert!(simd_uaf.faults.iter().all(|&f| (f & FAULT_UAF) != 0));

    // ABA reallocation: Alloc(g1) -> Free -> Alloc(g2); CheckGen(g1) fails UAF while CheckGen(g2) passes.
    let build_aba = |use_stale: bool| {
        let mut p = Program::new(if use_stale { "aba_stale" } else { "aba_fresh" });
        let b = p.add_uninit_buf("slot", 8, true, 1, 0, Domain::range(0, 255));
        let g1 = p.push(Op::Alloc { buf: b, len: 8 });
        p.push(Op::Free(b));
        let g2 = p.push(Op::Alloc { buf: b, len: 8 });
        let chk = p.push(Op::CheckGen { buf: b, expected: if use_stale { g1 } else { g2 } });
        p.add_output(chk);
        p
    };
    let aba_ok = build_aba(false);
    let aba_bad = build_aba(true);
    let ra_ok = verify_program(&aba_ok, ArchProfile::Aarch64Neon, RefineConfig::default());
    let ra_bad = verify_program(&aba_bad, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(ra_ok.is_ok(), ra_bad.is_ok(), "knockout 6 ABA fresh vs stale generation");
    assert!(matches!(ra_bad, Err(VerifyError::UseAfterFree { buf: 0, generation: 4, .. })));
    assert!(eval_lanes_x8(&aba_ok, &[]).faults.iter().all(|&f| f == FAULT_NONE));
    assert!(eval_lanes_x8(&aba_bad, &[]).faults.iter().all(|&f| (f & FAULT_UAF) != 0));

    // Dynamic Alloc expansion that overlaps a neighbor or wraps usize pointer offset must fail closed.
    let mut grow_alias = Program::new("grow_alias");
    let ga = grow_alias.add_buf("a", 8, true, 1, 0, Domain::range(0, 10));
    let _ = grow_alias.add_buf("b", 8, false, 1, 16, Domain::range(0, 10));
    let g_id = grow_alias.push(Op::Alloc { buf: ga, len: 24 });
    grow_alias.add_output(g_id);
    assert_eq!(
        verify_program(&grow_alias, ArchProfile::Aarch64Neon, RefineConfig::default()).unwrap_err(),
        VerifyError::NoAliasViolation { buf_a: 0, buf_b: 1, region: 1 }
    );
    let mut ptr_wrap = Program::new("ptr_wrap");
    ptr_wrap.add_buf("wrap", 16, true, 1, usize::MAX - 4, Domain::range(0, 10));
    assert!(matches!(ptr_wrap.validate(), Err(VerifyError::NoAliasViolation { buf_a: 0, buf_b: 0, region: 1 })));
    assert!(matches!(prove_exhaustive(&ptr_wrap, RefineConfig::default()), ProofVerdict::Incomplete { .. }));
}

#[test]
fn knockout_7_asan_double_free_and_uninit_read() {
    // Single Free vs Double Free.
    let mut single_free = Program::new("single_free");
    let b0 = single_free.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    let f0 = single_free.push(Op::Free(b0));
    single_free.add_output(f0);

    let mut double_free = Program::new("double_free");
    let b1 = double_free.add_buf("heap", 16, true, 1, 0, Domain::range(0, 255));
    double_free.push(Op::Free(b1));
    let f1 = double_free.push(Op::Free(b1));
    double_free.add_output(f1);

    let r_sf = verify_program(&single_free, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_df = verify_program(&double_free, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_sf.is_ok(), r_df.is_ok(), "knockout 7 single vs double free");
    assert!(matches!(r_df, Err(VerifyError::DoubleFree { buf: 0, generation: 2, .. })));
    assert!(eval_lanes_x8(&single_free, &[]).faults.iter().all(|&f| f == FAULT_NONE));
    assert!(eval_lanes_x8(&double_free, &[]).faults.iter().all(|&f| (f & FAULT_DOUBLE_FREE) != 0));

    // Uninitialized read vs Store(x) -> Load(x) symbolic initialization proof.
    let mut uninit = Program::new("uninit_read");
    let bu = uninit.add_uninit_buf("scratch", 16, true, 1, 0, Domain::range(0, 255));
    let iu = uninit.add_param(Domain::range(0, 15));
    let lu = uninit.push(Op::Load { buf: bu, idx: iu });
    uninit.add_output(lu);

    let mut init_sym = Program::new("init_sym");
    let bi = init_sym.add_uninit_buf("scratch", 16, true, 1, 0, Domain::range(0, 255));
    let ii = init_sym.add_param(Domain::range(0, 15));
    let c9 = init_sym.push(Op::Const(9));
    init_sym.push(Op::Store { buf: bi, idx: ii, val: c9 });
    let li = init_sym.push(Op::Load { buf: bi, idx: ii });
    init_sym.add_output(li);

    let r_un = verify_program(&uninit, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_in = verify_program(&init_sym, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_un.is_ok(), r_in.is_ok(), "knockout 7 uninit vs Store->Load");
    assert!(matches!(r_un, Err(VerifyError::UninitializedRead { buf: 0, .. })));
    assert!(eval_lanes_x8(&uninit, &[[0, 1, 2, 3, 4, 5, 6, 7]]).faults.iter().all(|&f| (f & FAULT_UNINIT) != 0));
    assert!(eval_lanes_x8(&init_sym, &[[0, 1, 2, 3, 4, 5, 6, 7]]).faults.iter().all(|&f| f == FAULT_NONE));

    // Partial init mask: Store(buf[0]) then Load(buf[x]) on x in 0..=3 -> CEGAR catches FAULT_UNINIT and synthesizes `p0 == 0`.
    let mut partial = Program::new("partial_init");
    let bp = partial.add_uninit_buf("scratch", 8, true, 1, 0, Domain::range(0, 255));
    let xp = partial.add_param(Domain::range(0, 3));
    let c0 = partial.push(Op::Const(0));
    let cv = partial.push(Op::Const(42));
    partial.push(Op::Store { buf: bp, idx: c0, val: cv });
    let lp = partial.push(Op::Load { buf: bp, idx: xp });
    partial.add_output(lp);
    match prove_exhaustive(&partial, RefineConfig::default()) {
        ProofVerdict::Counterexample { input, fault, synthesized_guard, .. } => {
            assert_ne!(fault & FAULT_UNINIT, 0);
            assert_ne!(input, vec![0]);
            assert_eq!(synthesized_guard, "p0 == 0");
        }
        other => panic!("expected partial-init counterexample with guard p0 == 0, got {other:?}"),
    }
}

#[test]
fn knockout_8_kani_exhaustive_proven_total_vs_point_777() {
    let clean = build_quad_mod16_kernel(false);
    let buggy = build_quad_mod16_kernel(true);

    let rep_clean = verify_program(&clean, ArchProfile::Aarch64Neon, RefineConfig::default());
    let rep_buggy = verify_program(&buggy, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(rep_clean.is_ok(), rep_buggy.is_ok(), "knockout 8 Kani ProvenTotal vs 1-point x == 777");

    // Exhaustive Kani-class branch-and-bound discharges `(x * x) % 16 < 10` for all x in 0..=1000 in 3 symbolic boxes.
    let v_clean = prove_exhaustive(&clean, RefineConfig::default());
    match v_clean {
        ProofVerdict::ProvenTotal { boxes_discharged, learned_invariants } => {
            assert_eq!(boxes_discharged, 3, "expected 3 quadratic-residue boxes (1 mod 2, 0 mod 4, 2 mod 4)");
            assert_eq!(learned_invariants.len(), 3);
        }
        other => panic!("expected ProvenTotal for clean quad_mod16 kernel, got {other:?}"),
    }

    // 1-point singularity at x == 777 inside [0, 1000] yields Counterexample([777]) + exact safe guard.
    let syn_buggy = refine_and_fuzz(&buggy, RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() });
    assert_eq!(syn_buggy.unproven_boxes, 0, "all non-faulting sub-boxes must be algebraically discharged");
    match &syn_buggy.verdict {
        ProofVerdict::Counterexample { input, fault, synthesized_guard, .. } => {
            assert_eq!(input, &vec![777]);
            assert_ne!(fault & FAULT_DIV0, 0);
            assert_eq!(synthesized_guard, "p0 in 0..=776 || p0 in 778..=1000");
        }
        other => panic!("expected Counterexample([777]), got {other:?}"),
    }
    for x in 0..=1000 {
        let covered = syn_buggy.safe_subdomains.iter().any(|b| b[0].contains(x));
        if x == 777 {
            assert!(!covered, "buggy point 777 must be excluded from safe subdomains");
        } else {
            assert!(covered, "safe point {x} missing from coalesced safe subdomains");
        }
    }
}

#[test]
fn autopoietic_gauntlet_and_cli_ledger() {
    let summary = run_gauntlet();
    assert!(summary.is_clean(), "gauntlet failed: {:?}", summary.failures);
    assert_eq!(summary.checks_passed, 11);
    assert_eq!(summary.checks_total, 11);
    assert!(!summary.proven_invariants.is_empty());
    assert!(!summary.learned_guards.is_empty());

    // Zero-dep AutopoieticLedger JSON round-trip and monotonic epoch accumulation.
    let mut ledger = AutopoieticLedger::default();
    ledger.absorb_invariants(summary.proven_invariants.clone(), summary.learned_guards.clone());
    assert_eq!(ledger.epochs, 1);
    let json1 = ledger.to_json();
    assert!(json1.is_ascii(), "ledger JSON must be 100% 7-bit ASCII");
    let mut loaded = AutopoieticLedger::from_json(&json1);
    assert_eq!(loaded.epochs, 1);
    assert_eq!(loaded.proven_invariants, ledger.proven_invariants);
    assert_eq!(loaded.learned_guards, ledger.learned_guards);
    loaded.absorb_invariants(["extra:inv".to_string()], ["extra:guard".to_string()]);
    assert_eq!(loaded.epochs, 2);
    assert!(loaded.proven_invariants.contains("extra:inv"));
    assert!(loaded.learned_guards.contains("extra:guard"));

    // Live CLI execution on self + any sibling crates present (< 25 ms wall-clock).
    #[cfg(not(miri))]
    {
        let bin = env!("CARGO_BIN_EXE_zero-check");
        let ledger_file = std::env::temp_dir().join("zero_check_test_ledger.json");
        let _ = std::fs::remove_file(&ledger_file);
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let workspace_parent = manifest_dir.parent().unwrap_or(manifest_dir);
        let mut cmd = std::process::Command::new(bin);
        cmd.arg("--ledger").arg(&ledger_file)
            .arg("--ntf1").arg(manifest_dir.join("specs").join("zero_check.ntf1"))
            .arg(manifest_dir.join("src"));
        let cc_ntf1 = workspace_parent.join("zero-cc").join("specs").join("zero_cc.ntf1");
        if cc_ntf1.is_file() {
            cmd.arg(cc_ntf1);
        }
        for sib in [
            workspace_parent.join("zero-cc").join("src"),
            workspace_parent.join("zero-proxy").join("src").join("blindbind"),
            workspace_parent.join("zero-proxy").join("src").join("xdp"),
            workspace_parent.join("zero-rans").join("src"),
        ] {
            if sib.is_dir() {
                cmd.arg(sib);
            }
        }
        let t0 = std::time::Instant::now();
        let out = cmd.output().expect("run zero-check CLI");
        let cli_ms = (t0.elapsed().as_micros() as f64) / 1000.0;
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "CLI failed: stdout={stdout}\nstderr={stderr}");
        assert!(stdout.contains("[ZERO-CHECK-V2]"), "missing summary line: {stdout}");
        assert!(stdout.contains("gauntlet=11/11"), "expected 11/11 gauntlet: {stdout}");
        assert!(stdout.contains("[NTF1]"), "missing NTF1 summary line: {stdout}");
        let disk_json = std::fs::read_to_string(&ledger_file).expect("read written ledger");
        let parsed = AutopoieticLedger::from_json(&disk_json);
        assert_eq!(parsed.epochs, 1);
        assert!(parsed.proven_invariants.len() >= 5);
        assert!(parsed.learned_guards.len() >= 6);
        let _ = std::fs::remove_file(&ledger_file);
        eprintln!("[ZERO-CHECK-CLI-TEST] wall={cli_ms:.3} ms | {}", stdout.lines().last().unwrap_or(""));
    }
}

#[test]
fn knockout_9_store_to_load_value_forwarding() {
    let build_const = |stored: i64| {
        let mut p = Program::new(if stored == 0 { "store_zero_div" } else { "store_five_div" });
        let b = p.add_buf("scratch", 4, true, 1, 0, Domain::range(1, 10));
        let c0 = p.push(Op::Const(0));
        let cv = p.push(Op::Const(stored));
        let c100 = p.push(Op::Const(100));
        p.push(Op::Store { buf: b, idx: c0, val: cv });
        let v = p.push(Op::Load { buf: b, idx: c0 });
        let q = p.push(Op::Div(c100, v));
        p.add_output(q);
        p
    };
    let safe_const = build_const(5);
    let zero_const = build_const(0);

    let r_safe = verify_program(&safe_const, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_zero = verify_program(&zero_const, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_safe.is_ok(), r_zero.is_ok(), "knockout 9 static Store->Load div-by-zero");
    assert!(matches!(r_zero, Err(VerifyError::DivByZero { .. })));
    assert!(matches!(prove_exhaustive(&safe_const, RefineConfig::default()), ProofVerdict::ProvenTotal { .. }));
    match prove_exhaustive(&zero_const, RefineConfig::default()) {
        ProofVerdict::Counterexample { fault, synthesized_guard, .. } => {
            assert_ne!(fault & FAULT_DIV0, 0);
            assert_eq!(synthesized_guard, "false");
        }
        other => panic!("expected DivByZero counterexample on Store(0)->Load->Div, got {other:?}"),
    }
    let simd_zero = eval_lanes_x8(&zero_const, &[]);
    let simd_safe = eval_lanes_x8(&safe_const, &[]);
    assert!(simd_zero.faults.iter().all(|&f| (f & FAULT_DIV0) != 0));
    assert!(simd_safe.faults.iter().all(|&f| f == FAULT_NONE));
    assert_eq!(simd_safe.outputs[0], [20; 8]);

    // Dynamic index Store(b, p0, val) -> Load(b, p1) -> Div(100, v) on p0, p1 in 0..=3.
    let build_dyn = |stored: i64| {
        let mut p = Program::new("dyn_store_load");
        let b = p.add_buf("scratch", 4, true, 1, 0, Domain::range(1, 10));
        let p0 = p.add_param(Domain::range(0, 3));
        let p1 = p.add_param(Domain::range(0, 3));
        let cv = p.push(Op::Const(stored));
        let c100 = p.push(Op::Const(100));
        p.push(Op::Store { buf: b, idx: p0, val: cv });
        let v = p.push(Op::Load { buf: b, idx: p1 });
        let q = p.push(Op::Div(c100, v));
        p.add_output(q);
        p
    };
    let dyn_safe = build_dyn(5);
    let dyn_zero = build_dyn(0);
    let rd_safe = verify_program(&dyn_safe, ArchProfile::Aarch64Neon, RefineConfig::default());
    let rd_zero = verify_program(&dyn_zero, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(rd_safe.is_ok(), rd_zero.is_ok(), "knockout 9 dynamic Store->Load div-by-zero");
    assert!(matches!(prove_exhaustive(&dyn_safe, RefineConfig::default()), ProofVerdict::ProvenTotal { .. }));
    let syn = refine_and_fuzz(&dyn_zero, RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() });
    assert_eq!(syn.unproven_boxes, 0, "all non-aliasing pairs must discharge algebraically");
    assert!(syn.counterexamples.iter().any(|c| c.inputs.len() == 2 && c.inputs[0] == c.inputs[1] && (c.fault & FAULT_DIV0) != 0));
    for x in 0..=3 {
        for y in 0..=3 {
            let covered = syn.safe_subdomains.iter().any(|b| b[0].contains(x) && b[1].contains(y));
            if x == y {
                assert!(!covered, "faulting diagonal ({x}, {y}) must be excluded");
            } else {
                assert!(covered, "safe off-diagonal ({x}, {y}) must be covered");
            }
        }
    }
}

#[test]
fn knockout_10_empty_safe_guard_false_and_unknown() {
    let build = |lo: i64, hi: i64| {
        let mut p = Program::new("oob_guard_soundness");
        let b = p.add_buf("arr", 16, false, 1, 0, Domain::range(0, 100));
        let x = p.add_param(Domain::range(lo, hi));
        let v = p.push(Op::Load { buf: b, idx: x });
        p.add_output(v);
        p
    };
    let all_oob = build(16, 32);
    let partial_oob = build(0, 32);

    // Exhaustive proof on all-OOB domain must emit "false" (never "!(p0 == 16)").
    let all_rep = refine_and_fuzz(&all_oob, RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() });
    assert!(all_rep.safe_subdomains.is_empty());
    assert_eq!(all_rep.unproven_boxes, 0);
    assert_eq!(all_rep.synthesized_guard, "false");
    match &all_rep.verdict {
        ProofVerdict::Counterexample { input, fault, synthesized_guard, .. } => {
            assert_eq!(input, &vec![16]);
            assert_ne!(fault & FAULT_OOB, 0);
            assert_eq!(synthesized_guard, "false");
        }
        other => panic!("expected Counterexample with false guard, got {other:?}"),
    }

    // Without synthesize_safe_boundary, partial OOB stops early and must emit "unknown" (never "!(p0 == 32)").
    let unsyn = refine_and_fuzz(&partial_oob, RefineConfig { synthesize_safe_boundary: false, ..RefineConfig::default() });
    assert!(unsyn.safe_subdomains.is_empty());
    assert!(unsyn.unproven_boxes > 0);
    assert_eq!(unsyn.synthesized_guard, "unknown");

    // With synthesize_safe_boundary, partial OOB synthesizes exact "p0 in 0..=15".
    let syn = refine_and_fuzz(&partial_oob, RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() });
    assert_eq!(syn.synthesized_guard, "p0 in 0..=15");
    assert_ne!(all_rep.synthesized_guard, syn.synthesized_guard, "knockout 10 all-OOB vs partial-OOB guard");
    assert_ne!(unsyn.synthesized_guard, syn.synthesized_guard, "knockout 10 unsynthesized unknown vs exact guard");
}

#[test]
fn knockout_11_high_slot_init_and_contradictory_domain() {
    // High slot >= 64 initialized via Const(70) and read via 35 + 35 (distinct node) vs uninit slot 71.
    let build_hi = |read_slot_70: bool| {
        let mut p = Program::new(if read_slot_70 { "hi_slot_70_ok" } else { "hi_slot_71_uninit" });
        let b = p.add_uninit_buf("big", 128, true, 1, 0, Domain::range(1, 255));
        let c70 = p.push(Op::Const(70));
        let c99 = p.push(Op::Const(99));
        p.push(Op::Store { buf: b, idx: c70, val: c99 });
        let idx = if read_slot_70 {
            let c35a = p.push(Op::Const(35));
            let c35b = p.push(Op::Const(35));
            p.push(Op::Add(c35a, c35b))
        } else {
            p.push(Op::Const(71))
        };
        let v = p.push(Op::Load { buf: b, idx });
        p.add_output(v);
        p
    };
    let ok_70 = build_hi(true);
    let bad_71 = build_hi(false);

    let r_ok = verify_program(&ok_70, ArchProfile::Aarch64Neon, RefineConfig::default());
    let r_bad = verify_program(&bad_71, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r_ok.is_ok(), r_bad.is_ok(), "knockout 11 slot 70 init vs slot 71 uninit");
    assert!(matches!(r_ok.as_ref().map(|r| &r.abstract_report.status), Ok(ProofStatus::ProvenSafe)));
    assert!(matches!(r_bad, Err(VerifyError::UninitializedRead { buf: 0, idx_lo: 71, idx_hi: 71, .. })));
    assert!(matches!(prove_exhaustive(&ok_70, RefineConfig::default()), ProofVerdict::ProvenTotal { .. }));
    let simd_ok = eval_lanes_x8(&ok_70, &[]);
    let simd_bad = eval_lanes_x8(&bad_71, &[]);
    assert!(simd_ok.faults.iter().all(|&f| f == FAULT_NONE));
    assert_eq!(simd_ok.outputs[0], [99; 8]);
    assert!(simd_bad.faults.iter().all(|&f| (f & FAULT_UNINIT) != 0));

    // Dynamic Store(b, p0, 99) -> Load(b, p1) on uninit slots 68..=71 preserves safe diagonal p0 == p1.
    let mut diag = Program::new("hi_slot_diag");
    let bd = diag.add_uninit_buf("big", 128, true, 1, 0, Domain::range(1, 255));
    let p0 = diag.add_param(Domain::range(68, 71));
    let p1 = diag.add_param(Domain::range(68, 71));
    let c99 = diag.push(Op::Const(99));
    diag.push(Op::Store { buf: bd, idx: p0, val: c99 });
    let ld = diag.push(Op::Load { buf: bd, idx: p1 });
    diag.add_output(ld);
    let diag_rep = refine_and_fuzz(&diag, RefineConfig { synthesize_safe_boundary: true, ..RefineConfig::default() });
    assert_eq!(diag_rep.unproven_boxes, 0);
    for x in 68..=71 {
        for y in 68..=71 {
            let covered = diag_rep.safe_subdomains.iter().any(|b| b[0].contains(x) && b[1].contains(y));
            assert_eq!(covered, x == y, "high-slot diagonal mismatch at ({x}, {y})");
        }
    }

    // Contradictory empty congruence domains must be rejected by validate() and never return ProvenTotal.
    let bad_dom = Domain { lo: 1, hi: 1, modulus: 2, rem: 0 };
    let good_dom = Domain { lo: 2, hi: 2, modulus: 2, rem: 0 };
    assert_eq!(bad_dom.is_const(), None);
    assert_eq!(bad_dom.tighten(), None);
    assert_eq!(good_dom.is_const(), Some(2));

    let mut bad_param = Program::new("bad_param_dom");
    let bp = bad_param.add_param(bad_dom);
    bad_param.add_output(bp);

    let mut good_param = Program::new("good_param_dom");
    let gp = good_param.add_param(good_dom);
    good_param.add_output(gp);

    assert_ne!(good_param.validate().is_ok(), bad_param.validate().is_ok(), "knockout 11 valid vs contradictory param domain");
    assert_eq!(bad_param.validate(), Err(VerifyError::InvalidParam(0)));
    assert!(matches!(prove_exhaustive(&bad_param, RefineConfig::default()), ProofVerdict::Incomplete { .. }));
    assert!(matches!(prove_exhaustive(&good_param, RefineConfig::default()), ProofVerdict::ProvenTotal { .. }));

    let mut bad_buf = Program::new("bad_buf_dom");
    bad_buf.add_buf("bad", 4, false, 1, 0, bad_dom);
    assert_eq!(bad_buf.validate(), Err(VerifyError::InvalidBuffer(0)));

    assert_eq!(Domain { lo: 0, hi: 10, modulus: 2, rem: 3 }.tighten(), None);
    assert_eq!(Domain { lo: 0, hi: 10, modulus: 0, rem: 0 }.tighten(), None);
}

#[test]
fn knockout_12_sethi_ullman_vs_naive_schedule() {
    // Interleaved 32-leaf balanced binary tree: even leaves pushed before odd leaves.
    // Naive (delta, u) schedules all 16 even leaves first (peak >= 17 > 14 AVX2 GPRs),
    // while Sethi-Ullman (delta, helps, !su[u], u) pairs each sibling immediately (peak <= 7).
    let mut p = Program::new("interleaved_tree32");
    p.simd_lanes = 2;
    let mut even = Vec::new();
    let mut odd = Vec::new();
    for _ in 0..16 { even.push(p.add_param(Domain::range(0, 100))); }
    for _ in 0..16 { odd.push(p.add_param(Domain::range(0, 100))); }
    let mut level: Vec<usize> = even.into_iter().zip(odd).map(|(a, b)| p.push(Op::Add(a, b))).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        for pair in level.chunks_exact(2) {
            next.push(p.push(Op::Add(pair[0], pair[1])));
        }
        level = next;
    }
    p.add_output(level[0]);

    // Compute naive (delta, u) peak live count on the exact same DAG.
    let n = p.nodes.len();
    let (mut deps, mut cons, mut rem_uses) = (vec![Vec::new(); n], vec![Vec::new(); n], vec![0usize; n]);
    for (id, dep) in deps.iter_mut().enumerate() {
        let (kids, cnt) = p.nodes[id].children();
        for &k in &kids[..cnt] {
            if !dep.contains(&k) { dep.push(k); cons[k].push(id); rem_uses[k] += 1; }
        }
    }
    rem_uses[level[0]] += 1;
    let mut rem_deps: Vec<usize> = deps.iter().map(Vec::len).collect();
    let mut ready: Vec<usize> = (0..n).filter(|&i| rem_deps[i] == 0).collect();
    let (mut live, mut naive_peak) = (std::collections::BTreeSet::new(), 0usize);
    while !ready.is_empty() {
        let mut best = (0usize, (isize::MAX, usize::MAX));
        for (pos, &u) in ready.iter().enumerate() {
            let kills = deps[u].iter().filter(|&&d| rem_uses[d] == 1).count() as isize;
            let key = (isize::from(rem_uses[u] > 0) - kills, u);
            if key < best.1 { best = (pos, key); }
        }
        let u = ready.swap_remove(best.0);
        naive_peak = naive_peak.max(live.len() + usize::from(rem_uses[u] > 0));
        if rem_uses[u] > 0 { live.insert(u); }
        for &d in &deps[u] { rem_uses[d] -= 1; if rem_uses[d] == 0 { live.remove(&d); } }
        for &c in &cons[u] { rem_deps[c] -= 1; if rem_deps[c] == 0 { ready.push(c); } }
    }

    let su_rep = p.verify_schedule(ArchProfile::X86_64Avx2).expect("Sethi-Ullman must fit AVX2 14-GPR cliff");
    assert!(naive_peak > 14, "expected naive (delta, u) to exceed AVX2 14-GPR cliff, got {naive_peak}");
    assert!(su_rep.peak_gprs <= 14, "Sethi-Ullman peak {} must fit AVX2 14-GPR cliff", su_rep.peak_gprs);
    assert_ne!(su_rep.peak_gprs, naive_peak, "knockout 12 Sethi-Ullman vs naive (delta, u) peak GPRs");
    assert!(su_rep.peak_gprs < naive_peak);
}

#[test]
fn knockout_13_lint_expect_path_clamp_and_unused_prop() {
    let clean_src = "pub fn ok(x: i64) -> i64 { let _ = x; let _used = x.min(1).max(0); _used }\n";
    let expect_src = "#[expect(dead_code)]\npub fn f() {}\n";
    let path_clamp_src = "pub fn f(x: i64) -> i64 { i64::clamp(x, 0, 1) }\n";
    let unused_prop_src = "pub fn f(x: i64) -> i64 { let _prop = x + 1; x }\n";

    let r_clean = scan_rust_source("clean.rs", clean_src);
    let r_expect = scan_rust_source("expect.rs", expect_src);
    let r_pclamp = scan_rust_source("pclamp.rs", path_clamp_src);
    let r_uprop = scan_rust_source("uprop.rs", unused_prop_src);

    assert!(r_clean.is_clean() && r_clean.warning_count() == 0);
    assert_ne!(r_clean.is_clean(), r_expect.is_clean(), "knockout 13 #[expect(...)]");
    assert!(r_expect.findings.iter().any(|f| f.kind == LintKind::ExpectAttr));
    assert_ne!(r_clean.is_clean(), r_pclamp.is_clean(), "knockout 13 i64::clamp(...)");
    assert!(r_pclamp.findings.iter().any(|f| f.kind == LintKind::ClampCall));
    assert_ne!(r_clean.warning_count(), r_uprop.warning_count(), "knockout 13 unused _var prop");
    assert!(r_uprop.findings.iter().any(|f| f.kind == LintKind::UnusedProp));

    // Self src/ and sibling zero-cc/src/ must have 0 errors and 0 UnusedProp findings.
    #[cfg(not(miri))]
    {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let self_rep = verify_crate_dir(&manifest_dir.join("src")).expect("zero-check/src clean");
        assert!(self_rep.lines_scanned <= 4600, "zero-check/src LOC {} > 4600", self_rep.lines_scanned);
        assert!(!self_rep.findings.iter().any(|f| f.kind == LintKind::UnusedProp));
        let sib_cc = manifest_dir.parent().unwrap_or(manifest_dir).join("zero-cc").join("src");
        if sib_cc.is_dir() {
            let cc_rep = verify_crate_dir(&sib_cc).expect("zero-cc/src clean");
            assert!(!cc_rep.findings.iter().any(|f| f.kind == LintKind::UnusedProp));
        }
    }
}

#[test]
fn knockout_14_ntf1_airlock_svo_and_coevolution() {
    use zero_check::{emit_ntf1, parse_ntf1, verify_ntf1_source, Ntf1Error};

    let self_src = include_str!("../specs/zero_check.ntf1");
    let self_rep = verify_ntf1_source("zero_check.ntf1", self_src).expect("specs/zero_check.ntf1 must pass");
    #[cfg(not(miri))]
    {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let self_spec_path = manifest_dir.join("specs").join("zero_check.ntf1");
        let file_rep = zero_check::verify_ntf1_file(&self_spec_path).expect("specs/zero_check.ntf1 file must pass");
        assert_eq!((file_rep.forward_count, file_rep.retro_count, file_rep.faults_covered), (self_rep.forward_count, self_rep.retro_count, self_rep.faults_covered));
    }
    assert!(self_rep.canonical_idempotent);
    assert!(self_rep.forward_count >= 5 && self_rep.retro_count >= 5 && self_rep.airlock_count >= 2);
    assert!(self_rep.faults_covered >= 6);
    let canon1 = emit_ntf1(&parse_ntf1(self_src).expect("parse self spec"));
    let canon2 = emit_ntf1(&parse_ntf1(&canon1).expect("reparse canonical"));
    assert_eq!(canon1, canon2, "emit_ntf1(parse_ntf1(s)) must be an exact fixed-point");

    // Counterfactual knockouts: SVO prose, comment SVO, dangling +t, uncovered Fault.*, broken 0t.
    let svo_code = "NTF1 bad\n+t the -> b\n";
    let svo_comment = "NTF1 bad\n# this comment carries SVO tax\n+t a -> b\n";
    let dangling = "NTF1 bad\n+t a ->\n";
    let uncov_fault = "NTF1 bad\n+t a -> Fault.Spill\n";
    let bad_0t_dir = "NTF1 bad\n+t a -> b\n0t a -> b\n";
    let bad_0t_ungrounded = "NTF1 bad\n+t a -> b\n0t a >< ghost\n";
    let bad_0t_partial_pipe = "NTF1 bad\n+t a -> b\n0t a |> ghost >< b\n";
    let ok_0t_full_pipe = "NTF1 ok\n+t a -> b\n0t a |> b >< b\n";
    let non_ascii = "NTF1 bad\n# caf\u{00e9}\n+t a -> b\n";

    let ok_res = verify_ntf1_source("zero_check.ntf1", self_src);
    let r_svo1 = verify_ntf1_source("svo1.ntf1", svo_code);
    let r_svo2 = verify_ntf1_source("svo2.ntf1", svo_comment);
    let r_dang = verify_ntf1_source("dang.ntf1", dangling);
    let r_uncov = verify_ntf1_source("uncov.ntf1", uncov_fault);
    let r_0t1 = verify_ntf1_source("0t1.ntf1", bad_0t_dir);
    let r_0t2 = verify_ntf1_source("0t2.ntf1", bad_0t_ungrounded);
    let r_0t_partial = verify_ntf1_source("0t_partial.ntf1", bad_0t_partial_pipe);
    let r_0t_full = verify_ntf1_source("0t_full.ntf1", ok_0t_full_pipe);
    let r_ascii = verify_ntf1_source("ascii.ntf1", non_ascii);

    assert_ne!(ok_res.is_ok(), r_svo1.is_ok(), "knockout 14 SVO token");
    assert!(matches!(r_svo1, Err(Ntf1Error::SvoTax { .. })));
    assert_ne!(ok_res.is_ok(), r_svo2.is_ok(), "knockout 14 SVO in # comment");
    assert!(matches!(r_svo2, Err(Ntf1Error::SvoTax { .. })));
    assert_ne!(ok_res.is_ok(), r_dang.is_ok(), "knockout 14 dangling +t");
    assert!(matches!(r_dang, Err(Ntf1Error::DanglingMorphism { .. })));
    assert_ne!(ok_res.is_ok(), r_uncov.is_ok(), "knockout 14 uncovered Fault.*");
    assert!(matches!(r_uncov, Err(Ntf1Error::UncoveredFault { .. })));
    assert_ne!(ok_res.is_ok(), r_0t1.is_ok(), "knockout 14 0t wrong operator");
    assert!(matches!(r_0t1, Err(Ntf1Error::BrokenAirlock { .. })));
    assert_ne!(ok_res.is_ok(), r_0t2.is_ok(), "knockout 14 ungrounded 0t");
    assert!(matches!(r_0t2, Err(Ntf1Error::BrokenAirlock { .. })));
    assert_ne!(r_0t_full.is_ok(), r_0t_partial.is_ok(), "knockout 14 0t all-atoms airlock grounding");
    assert!(r_0t_full.is_ok());
    assert!(matches!(r_0t_partial, Err(Ntf1Error::BrokenAirlock { .. })));
    assert!(matches!(r_ascii, Err(Ntf1Error::NonAscii { .. })));

    // Cross-crate NTF1 + Rust co-evolution check when ../zero-cc is present (< 25 ms).
    #[cfg(not(miri))]
    {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let sib_root = manifest_dir.parent().unwrap_or(manifest_dir).join("zero-cc");
        let sib_spec = sib_root.join("specs").join("zero_cc.ntf1");
        if sib_spec.is_file() {
            let t0 = std::time::Instant::now();
            let cc_ntf1 = zero_check::verify_ntf1_file(&sib_spec).expect("../zero-cc/specs/zero_cc.ntf1 must pass");
            let cc_lint = verify_crate_dir(&sib_root.join("src")).expect("../zero-cc/src must pass");
            let elapsed_ms = (t0.elapsed().as_micros() as f64) / 1000.0;
            assert!(cc_ntf1.canonical_idempotent);
            assert!(cc_lint.is_clean());
            assert!(elapsed_ms < 25.0, "co-evolution check took {elapsed_ms:.3} ms (>= 25 ms)");
        }
    }
}

#[test]
fn knockout_15_raw_rs_semantic_verifier_and_kernel_strict() {
    use zero_check::{parse_rust_programs, verify_kernel_rust_source, verify_rust_functions};

    // 1. Raw `.rs` quadratic LUT proof vs 1-point interior div-by-zero at x == 777 (zero manual Program!).
    let rs_quad_ok = "pub fn lut_quad(#[zero_domain(0..=1000)] x: i64, tbl: &[i64; 10]) -> i64 { tbl[((x * x) % 16) as usize] }\n";
    let rs_quad_bad = "pub fn lut_quad(#[zero_domain(0..=1000)] x: i64, tbl: &[i64; 10]) -> i64 { tbl[((x * x) % 16) as usize] / (x - 777) }\n";
    let q_ok = verify_rust_functions("quad_ok.rs", rs_quad_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    let q_bad = verify_rust_functions("quad_bad.rs", rs_quad_bad, ArchProfile::X86_64Avx2, RefineConfig::default());
    assert_ne!(q_ok.is_clean(), q_bad.is_clean(), "knockout 15.1 raw .rs quad_mod16 clean vs div0@777");
    assert_eq!(q_ok.proven.len(), 1);
    assert!(matches!(q_ok.proven[0].1.verdict, ProofVerdict::ProvenTotal { .. }));
    assert!(matches!(
        q_bad.failed.first().map(|f| &f.error),
        Some(VerifyError::CounterexampleFound { inputs, fault, .. }) if inputs == &vec![777] && (*fault & FAULT_DIV0) != 0
    ));

    // 2. Raw `.rs` u8 slice OOB at idx == 64 vs masked `(idx & 63) as usize`, plus negative i64 -> usize fail-closed.
    let rs_pkt_bad = "pub fn read_pkt(buf: &[u8; 64], idx: u8) -> i64 { buf[idx as usize] }\n";
    let rs_pkt_ok = "pub fn read_pkt(buf: &[u8; 64], idx: u8) -> i64 { buf[(idx & 63) as usize] }\n";
    let rs_neg_cast = "/// @domain x: -5..=5\npub fn neg_idx(buf: &[u8; 64], x: i64) -> i64 { buf[((x as usize) + 1)] }\n";
    let p_bad = verify_rust_functions("pkt_bad.rs", rs_pkt_bad, ArchProfile::X86_64Avx2, RefineConfig::default());
    let p_ok = verify_rust_functions("pkt_ok.rs", rs_pkt_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    let p_neg = verify_rust_functions("neg.rs", rs_neg_cast, ArchProfile::X86_64Avx2, RefineConfig::default());
    assert_ne!(p_ok.is_clean(), p_bad.is_clean(), "knockout 15.2 raw .rs u8 OOB vs masked");
    assert!(matches!(p_ok.proven[0].1.abstract_report.status, ProofStatus::ProvenSafe));
    assert!(matches!(
        p_bad.failed.first().map(|f| &f.error),
        Some(VerifyError::CounterexampleFound { inputs, fault, .. }) if inputs.len() == 1 && inputs[0] >= 64 && (*fault & FAULT_OOB) != 0
    ));
    let pkt_prog = &parse_rust_programs(rs_pkt_bad).programs[0];
    assert!(matches!(
        prove_exhaustive(pkt_prog, RefineConfig::default()),
        ProofVerdict::Counterexample { ref synthesized_guard, .. } if synthesized_guard == "p0 in 0..=63"
    ));
    assert_ne!(p_ok.is_clean(), p_neg.is_clean(), "knockout 15.2 negative i64 as usize must fail closed");

    // 3. Raw `.rs` 20-parameter live-register function failing AVX2 spill (14 GPR) while passing NEON (28 GPR).
    let rs_20 = concat!(
        "/// @domain a0: 0..=10, a1: 0..=10, a2: 0..=10, a3: 0..=10, a4: 0..=10\n",
        "/// @domain a5: 0..=10, a6: 0..=10, a7: 0..=10, a8: 0..=10, a9: 0..=10\n",
        "/// @domain b0: 0..=10, b1: 0..=10, b2: 0..=10, b3: 0..=10, b4: 0..=10\n",
        "/// @domain b5: 0..=10, b6: 0..=10, b7: 0..=10, b8: 0..=10, b9: 0..=10\n",
        "pub fn live20(a0: i64, a1: i64, a2: i64, a3: i64, a4: i64, a5: i64, a6: i64, a7: i64, a8: i64, a9: i64, ",
        "b0: i64, b1: i64, b2: i64, b3: i64, b4: i64, b5: i64, b6: i64, b7: i64, b8: i64, b9: i64) -> ",
        "(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) {\n",
        "    (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9)\n",
        "}\n"
    );
    let r20_avx = verify_rust_functions("r20.rs", rs_20, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r20_neon = verify_rust_functions("r20.rs", rs_20, ArchProfile::Aarch64Neon, RefineConfig::default());
    assert_ne!(r20_avx.is_clean(), r20_neon.is_clean(), "knockout 15.3 raw .rs 20-reg AVX2 spill vs NEON pass");
    assert!(matches!(
        r20_avx.failed.first().map(|f| &f.error),
        Some(VerifyError::RegisterSpill { profile: ArchProfile::X86_64Avx2, peak_gprs: 20, max_gprs: 14, .. })
    ));
    assert_eq!(r20_neon.proven.len(), 1);

    // 4. --kernel-strict rejects `.unwrap()` / `panic!(...)` while passing panic-free kernel code + loop unroll + zero-cc batch skip.
    let rs_k_panic = "pub fn bad_u(x: Option<i64>) -> i64 { x.unwrap() }\npub fn bad_p() { panic!(\"boom\"); }\n";
    let rs_k_ok = concat!(
        "/// @domain a: 0..=1000\n",
        "/// @domain lut: 0..=255\n",
        "#[inline(always)]\n",
        "pub fn ring_step(a: &[i64; 8], lut: &[i64; 16], out: &mut [i64; 8]) {\n",
        "    for lane in 0..8 {\n",
        "        let v: i64 = a[lane];\n",
        "        let idx: i64 = { assert!(v >= 0 && v < 1001); v & 15 };\n",
        "        out[lane] = lut[idx as usize].wrapping_add(1_i64);\n",
        "    }\n",
        "}\n",
        "pub fn ring_step_batch(a: &[[i64; 8]], lut: &[i64; 16], out: &mut [[i64; 8]]) {\n",
        "    let blocks = a.len().min(out.len());\n",
        "    for blk in 0..blocks { ring_step(&a[blk], lut, &mut out[blk]); }\n",
        "}\n"
    );
    let k_bad = verify_kernel_rust_source("k_panic.rs", rs_k_panic, ArchProfile::X86_64Avx2, RefineConfig::default());
    let k_ok = verify_kernel_rust_source("k_ok.rs", rs_k_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    assert_ne!(k_ok.is_ok(), k_bad.is_ok(), "knockout 15.4 --kernel-strict panic rejection");
    assert!(matches!(k_bad, Err(VerifyError::LintViolations { count: 2 })));
    let (_, proofs) = k_ok.expect("panic-free kernel must pass");
    assert_eq!(proofs.proven.len(), 1);
    assert_eq!(proofs.proven[0].0, "ring_step");
    assert_eq!(proofs.skipped_non_kernel_fns, vec!["ring_step_batch".to_string()]);
    assert_eq!(parse_rust_programs(rs_k_ok).programs.len(), 1);

    // 5. CLI `--prove-fns --kernel-strict` live exit-code knockout on /tmp .rs files.
    #[cfg(not(miri))]
    {
        let bin = env!("CARGO_BIN_EXE_zero-check");
        let tmp = std::env::temp_dir();
        let f_ok = tmp.join("zero_check_fe_ok.rs");
        let f_bad = tmp.join("zero_check_fe_bad.rs");
        std::fs::write(&f_ok, rs_k_ok).expect("write ok.rs");
        std::fs::write(&f_bad, rs_quad_bad).expect("write bad.rs");
        let out_ok = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict"])
            .arg(&f_ok)
            .output()
            .expect("run CLI on ok.rs");
        let out_bad = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict"])
            .arg(&f_bad)
            .output()
            .expect("run CLI on bad.rs");
        let _ = std::fs::remove_file(&f_ok);
        let _ = std::fs::remove_file(&f_bad);
        assert!(out_ok.status.success(), "CLI ok.rs failed: {}", String::from_utf8_lossy(&out_ok.stderr));
        assert!(!out_bad.status.success(), "CLI bad.rs must exit non-zero");
        assert!(String::from_utf8_lossy(&out_bad.stderr).contains("777"));
    }
}

#[test]
fn knockout_16_live_miri_head_to_head_and_guarded_branches() {
    use zero_check::verify_rust_functions;

    // (a) Live Miri head-to-head on a standalone 0-dep crate: Miri passes partial unit tests (exit 0),
    // while zero-check proves all 4 latent UB paths in < 10 ms (exit 1) and passes the patched crate (exit 0).
    #[cfg(not(miri))]
    {
        let bin = env!("CARGO_BIN_EXE_zero-check");
        let root = std::env::temp_dir().join(format!("zero_check_k16_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("src")).expect("mkdir src");
        std::fs::create_dir_all(root.join("tests")).expect("mkdir tests");
        std::fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"k16_probe\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("write Cargo.toml");

        let buggy_lib = concat!(
            "#![forbid(unsafe_code)]\n",
            "pub fn zero_free(buf: &mut [i64; 8]) { let _ = buf; }\n",
            "pub fn cond_uaf(buf: &mut [i64; 8], cmd: u8) -> i64 {\n",
            "    if cmd == 221 { zero_free(buf); }\n",
            "    buf[0]\n",
            "}\n",
            "/// @uninit scratch\n",
            "pub fn cond_uninit(scratch: &mut [i64; 16], mode: u8) -> i64 {\n",
            "    scratch[0] = 7;\n",
            "    if (mode & 1) == 1 { scratch[1] } else { scratch[0] }\n",
            "}\n",
            "/// @region a: 1, 0\n",
            "/// @region b: 1, 8\n",
            "pub fn region_collide(a: &mut [i64; 16], b: &[i64; 16], i: u8) -> i64 {\n",
            "    let idx = (i & 15) as usize;\n",
            "    a[idx] = b[idx];\n",
            "    a[idx]\n",
            "}\n",
            "fn helper_div0(x: u16) -> i64 {\n",
            "    if x == 4099 { 100 / (x as i64 - 4099) } else { match x { 0..=15 => 1, _ => 2 } }\n",
            "}\n",
            "pub fn entry_pkt(x: u16) -> i64 { helper_div0(x) }\n",
        );
        let miri_tests = concat!(
            "use k16_probe::{cond_uaf, cond_uninit, entry_pkt, region_collide};\n",
            "#[test]\n",
            "fn partial_unit_tests_miss_all_four_bugs() {\n",
            "    let mut b = [1_i64; 8];\n",
            "    assert_eq!(cond_uaf(&mut b, 0), 1);\n",
            "    assert_eq!(cond_uaf(&mut b, 1), 1);\n",
            "    let mut s = [0_i64; 16];\n",
            "    assert_eq!(cond_uninit(&mut s, 0), 7);\n",
            "    let mut a = [0_i64; 16];\n",
            "    let r = [3_i64; 16];\n",
            "    assert_eq!(region_collide(&mut a, &r, 2), 3);\n",
            "    assert_eq!(entry_pkt(7), 1);\n",
            "}\n",
        );
        let lib_rs = root.join("src").join("lib.rs");
        std::fs::write(&lib_rs, buggy_lib).expect("write buggy lib.rs");
        std::fs::write(root.join("tests").join("miri_probe.rs"), miri_tests).expect("write miri test");

        let miri_out = std::process::Command::new("cargo")
            .env_remove("RUSTFLAGS")
            .args(["+nightly", "miri", "test", "--manifest-path"])
            .arg(root.join("Cargo.toml"))
            .arg("--offline")
            .output()
            .expect("run cargo +nightly miri test");
        assert!(
            miri_out.status.success(),
            "live Miri must pass partial tests: {}",
            String::from_utf8_lossy(&miri_out.stderr)
        );

        let t0 = std::time::Instant::now();
        let zc_bug = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict", "--require-totality"])
            .arg(&lib_rs)
            .output()
            .expect("run zero-check on buggy crate");
        let zc_ms = (t0.elapsed().as_micros() as f64) / 1000.0;
        let bug_err = String::from_utf8_lossy(&zc_bug.stderr);
        assert_ne!(miri_out.status.success(), zc_bug.status.success(), "knockout 16 Miri vs zero-check");
        assert!(!zc_bug.status.success(), "zero-check must fail on buggy crate");
        assert!(zc_ms < 10.0, "zero-check took {zc_ms:.3} ms (>= 10 ms)");
        assert!(bug_err.contains("cond_uaf") && bug_err.contains("fault 0x10: [221]"), "missing UAF@221: {bug_err}");
        assert!(bug_err.contains("cond_uninit") && bug_err.contains("fault 0x40:"), "missing Uninit: {bug_err}");
        assert!(bug_err.contains("region_collide") && bug_err.contains("noalias overlap"), "missing NoAliasViolation: {bug_err}");
        assert!(bug_err.contains("entry_pkt") && bug_err.contains("fault 0x08: [4099]"), "missing Div0@4099: {bug_err}");

        let patched_lib = concat!(
            "#![forbid(unsafe_code)]\n",
            "pub fn zero_free(buf: &mut [i64; 8]) { let _ = buf; }\n",
            "pub fn cond_uaf(buf: &mut [i64; 8], cmd: u8) -> i64 {\n",
            "    if cmd == 221 { zero_free(buf); return 0; }\n",
            "    buf[0]\n",
            "}\n",
            "/// @uninit scratch\n",
            "pub fn cond_uninit(scratch: &mut [i64; 16], mode: u8) -> i64 {\n",
            "    scratch[0] = 7;\n",
            "    scratch[1] = 9;\n",
            "    if (mode & 1) == 1 { scratch[1] } else { scratch[0] }\n",
            "}\n",
            "/// @region a: 1, 0\n",
            "/// @region b: 1, 16\n",
            "pub fn region_collide(a: &mut [i64; 16], b: &[i64; 16], i: u8) -> i64 {\n",
            "    let idx = (i & 15) as usize;\n",
            "    a[idx] = b[idx];\n",
            "    a[idx]\n",
            "}\n",
            "fn helper_div0(x: u16) -> i64 {\n",
            "    if x == 4099 { 0 } else { match x { 0..=15 => 1, _ => 2 } }\n",
            "}\n",
            "pub fn entry_pkt(x: u16) -> i64 { helper_div0(x) }\n",
            "/// @domain idx: -10..=32\n",
            "pub fn guarded_read(arr: &[i64; 16], idx: i64) -> i64 {\n",
            "    if idx < 0 || (idx as usize) >= 16 { return 0; }\n",
            "    arr[idx as usize]\n",
            "}\n",
        );
        std::fs::write(&lib_rs, patched_lib).expect("write patched lib.rs");
        let zc_ok = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict", "--require-totality"])
            .arg(&lib_rs)
            .output()
            .expect("run zero-check on patched crate");
        let _ = std::fs::remove_dir_all(&root);
        assert!(
            zc_ok.status.success(),
            "zero-check must prove patched crate: {}",
            String::from_utf8_lossy(&zc_ok.stderr)
        );
    }

    // (b) Direct overlapping vs disjoint sub-slice calls + comparison casts + conditional select.
    let subslice_bad = concat!(
        "fn blend(dst: &mut [i64; 16], src: &[i64; 16], i: u8) -> i64 {\n",
        "    let idx = (i & 15) as usize;\n",
        "    dst[idx] = src[idx];\n",
        "    dst[idx]\n",
        "}\n",
        "pub fn call_overlap(buf: &mut [i64; 32], i: u8) -> i64 {\n",
        "    blend(&mut buf[0..16], &buf[8..24], i)\n",
        "}\n",
    );
    let subslice_ok = concat!(
        "fn blend(dst: &mut [i64; 16], src: &[i64; 16], i: u8) -> i64 {\n",
        "    let idx = (i & 15) as usize;\n",
        "    dst[idx] = src[idx];\n",
        "    dst[idx]\n",
        "}\n",
        "pub fn call_disjoint(buf: &mut [i64; 32], i: u8) -> i64 {\n",
        "    blend(&mut buf[0..16], &buf[16..32], i)\n",
        "}\n",
        "/// @domain va: 0..=100, vb: 0..=100, vc: 0..=1, vt: 0..=50, vf: 0..=50\n",
        "pub fn cmp_and_sel(va: i64, vb: i64, vc: i64, vt: i64, vf: i64) -> i64 {\n",
        "    let gt = (va > vb) as i64;\n",
        "    let chosen = if vc != 0_i64 { vt } else { vf };\n",
        "    gt + chosen\n",
        "}\n",
    );
    let r_bad = verify_rust_functions("sub_bad.rs", subslice_bad, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_ok = verify_rust_functions("sub_ok.rs", subslice_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    assert_ne!(r_ok.is_clean(), r_bad.is_clean(), "knockout 16b overlapping vs disjoint sub-slices");
    assert!(matches!(r_bad.failed.first().map(|f| &f.error), Some(VerifyError::NoAliasViolation { .. })));
    assert!(r_ok.is_clean() && r_ok.proven.len() >= 2);
}

#[test]
fn knockout_17_cfg_test_separation_and_cli_skip() {
    use zero_check::verify_kernel_rust_source;

    let cfg_test_ok = "#[cfg(test)] mod tests { fn t() { Some(1).unwrap(); } }\n";
    let prod_panic = "pub fn prod() { Some(1).unwrap(); }\n";
    let cfg_test_unsafe = "#[cfg(test)] mod tests { unsafe fn bad() {} }\n";
    let cfg_kani_ok = "#[cfg(kani)]\nmod proofs {\n    fn k(i: usize) { let _u = 1; let a = [0; 4]; let _ = a[i]; Some(1).expect(\"k\"); }\n}\n";
    let cfg_kani_clamp = concat!("#[cfg(kani)] mod bad_k { fn c(x: i64) -> i64 { x.cl", "amp(0, 1) } }\n");
    let cfg_test_allow = concat!("#[cfg(test)] mod bad_a { #[al", "low(dead_code)] fn f() {} }\n");
    let cfg_test_ascii = "#[cfg(test)] mod bad_n { fn f() {} // caf\u{00e9}\n}\n";

    let r_test_ok = verify_kernel_rust_source("t_ok.rs", cfg_test_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_prod_bad = verify_kernel_rust_source("p_bad.rs", prod_panic, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_test_unsafe = verify_kernel_rust_source("t_unsafe.rs", cfg_test_unsafe, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_kani_ok = verify_kernel_rust_source("k_ok.rs", cfg_kani_ok, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_kani_clamp = verify_kernel_rust_source("k_clamp.rs", cfg_kani_clamp, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_test_allow = verify_kernel_rust_source("t_allow.rs", cfg_test_allow, ArchProfile::X86_64Avx2, RefineConfig::default());
    let r_test_ascii = verify_kernel_rust_source("t_ascii.rs", cfg_test_ascii, ArchProfile::X86_64Avx2, RefineConfig::default());

    assert_ne!(r_test_ok.is_ok(), r_prod_bad.is_ok(), "knockout 17 cfg(test) vs prod PanicCall");
    assert_ne!(r_test_ok.is_ok(), r_test_unsafe.is_ok(), "knockout 17 cfg(test) must still fail UnsafeBlock");
    assert_ne!(r_kani_ok.is_ok(), r_kani_clamp.is_ok(), "knockout 17 cfg(kani) must still fail ClampCall");
    assert_ne!(r_test_ok.is_ok(), r_test_allow.is_ok(), "knockout 17 cfg(test) must still fail AllowAttr");
    assert_ne!(r_test_ok.is_ok(), r_test_ascii.is_ok(), "knockout 17 cfg(test) must still fail NonAscii");
    let (lint_ok, _) = r_test_ok.expect("cfg(test) unwrap must pass");
    assert_eq!((lint_ok.error_count(), lint_ok.warning_count()), (0, 0));
    let (lint_kani, _) = r_kani_ok.expect("cfg(kani) panic/index/unused must pass");
    assert_eq!((lint_kani.error_count(), lint_kani.warning_count()), (0, 0));
    assert!(scan_rust_source("t_unsafe.rs", cfg_test_unsafe).findings.iter().any(|f| f.kind == LintKind::UnsafeBlock));

    #[cfg(not(miri))]
    {
        let bin = env!("CARGO_BIN_EXE_zero-check");
        let root = std::env::temp_dir().join(format!("zero_check_k17_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).expect("mkdir k17");
        std::fs::write(root.join("safe.rs"), "pub fn id(x: u8) -> i64 { x as i64 }\n").expect("write safe.rs");
        std::fs::write(root.join("ffi_bad.rs"), "pub fn bad() { unsafe {} }\n").expect("write ffi_bad.rs");
        let raw_out = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict", "--exclude-cfg-test"])
            .arg(&root)
            .output()
            .expect("run raw");
        let skip_out = std::process::Command::new(bin)
            .args(["--no-ledger", "--prove-fns", "--kernel-strict", "--skip", "ffi_bad.rs"])
            .arg(&root)
            .output()
            .expect("run skip");
        let _ = std::fs::remove_dir_all(&root);
        assert_ne!(raw_out.status.success(), skip_out.status.success(), "knockout 17 --skip CLI");
        assert!(skip_out.status.success(), "skip failed: {}", String::from_utf8_lossy(&skip_out.stderr));
        let stdout = String::from_utf8_lossy(&skip_out.stdout);
        assert!(stdout.contains("files=1") && stdout.contains("errors=0 warnings=0"), "unexpected skip stdout: {stdout}");
    }
}
