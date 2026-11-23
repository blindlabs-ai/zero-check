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
        self_rep.lines_scanned <= 2500,
        "src LOC must be <= 2500, got {}",
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
    assert!(
        elapsed_ms < 25.0,
        "expected < 25 ms to verify {total_lines} LOC across {crates_scanned} crates, got {elapsed_ms:.3} ms"
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
        "    let _s = \"unsafe transmute as *mut u8 todo!()\";\n",
        "    let _r = r#\"get_unchecked x << 64 x / 0\"#;\n",
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
    let _gb = grow_alias.add_buf("b", 8, false, 1, 16, Domain::range(0, 10));
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
    assert_eq!(summary.checks_passed, 9);
    assert_eq!(summary.checks_total, 9);
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
        cmd.arg("--ledger").arg(&ledger_file).arg(manifest_dir.join("src"));
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
        assert!(stdout.contains("gauntlet=9/9"), "expected 9/9 gauntlet: {stdout}");
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
