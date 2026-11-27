use zero_check::{
    eval_lanes_x8, parse_rust_programs, refine_and_fuzz, sample_batch_x8, sample_counterexample,
    scan_rust_source, synthesize_rust_poc_test_for_prog, verify_rust_functions_with_opts,
    ArchProfile, CmpKind, Domain, LintKind, Op, Program, ProofStatus, ProofVerdict, RefineConfig,
    RustFeOptions, VerifyError, FAULT_NONE, FAULT_OOB, FAULT_PANIC, FAULT_UAF, FAULT_UNINIT,
    LANES,
};

#[test]
fn seam1_deep_ast_recursion_and_utf8_fail_closed() {
    let deep_expr = format!(
        "pub fn deep_expr(x: i64) -> i64 {{ {}x{} }}",
        "(".repeat(2_000),
        ")".repeat(2_000)
    );
    let shallow_expr = "pub fn shallow_expr(x: i64) -> i64 { ((x)) }";
    let deep_expr_unit = parse_rust_programs(&deep_expr);
    let shallow_expr_unit = parse_rust_programs(shallow_expr);
    assert!(deep_expr_unit.programs.is_empty());
    assert_ne!(deep_expr_unit.programs.len(), shallow_expr_unit.programs.len());
    assert_eq!(shallow_expr_unit.programs.len(), 1);

    let deep_block = format!(
        "pub fn deep_blk(x: i64) -> i64 {{ {}x{} }}",
        "{".repeat(2_000),
        "}".repeat(2_000)
    );
    let shallow_block = "pub fn shallow_blk(x: i64) -> i64 { { { x } } }";
    let deep_blk_unit = parse_rust_programs(&deep_block);
    let shallow_blk_unit = parse_rust_programs(shallow_block);
    assert!(deep_blk_unit.programs.is_empty());
    assert_ne!(deep_blk_unit.programs.len(), shallow_blk_unit.programs.len());

    let deep_const = format!(
        "const K: i64 = {}1{};\npub fn use_k(x: i64) -> i64 {{ x + K }}",
        "(".repeat(2_000),
        ")".repeat(2_000)
    );
    let shallow_const = "const K: i64 = ((1));\npub fn use_k(x: i64) -> i64 { x + K }";
    let deep_const_unit = parse_rust_programs(&deep_const);
    let shallow_const_unit = parse_rust_programs(shallow_const);
    assert!(deep_const_unit.programs.is_empty());
    assert_ne!(deep_const_unit.programs.len(), shallow_const_unit.programs.len());

    let deep_mod = format!(
        "{}pub fn inner(x: i64) -> i64 {{ x }}{}",
        "mod m { ".repeat(2_000),
        " }".repeat(2_000)
    );
    let deep_mod_unit = parse_rust_programs(&deep_mod);
    assert!(deep_mod_unit.programs.is_empty());

    let opts = RustFeOptions::external_audit();
    let deep_bm = format!(
        "pub fn deep_bm(b: &[u8], i: usize) -> usize {{ {}i{} }}",
        "if b[i] < 128 { ".repeat(2_000),
        " } else { 0 }".repeat(2_000)
    );
    let bm_rep = verify_rust_functions_with_opts(
        "deep_bm.rs",
        &deep_bm,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    assert!(bm_rep.failed.is_empty());

    let deep_if_str = format!(
        "pub fn deep_if_str(s: &str, i: usize, c: bool) -> &str {{ {}&s[i..]{} }}",
        "if c { ".repeat(65),
        " } else { s }".repeat(65)
    );
    let deep_blk_str = format!(
        "pub fn deep_blk_str(s: &str, i: usize) -> &str {{ {}&s[i..]{} }}",
        "{ ".repeat(2_000),
        " }".repeat(2_000)
    );
    let shallow_safe_str =
        "pub fn shallow_safe_str(s: &str, i: usize) -> &str { if s.is_char_boundary(i) { &s[i..] } else { s } }";
    let rep_if = verify_rust_functions_with_opts(
        "deep_if_str.rs",
        &deep_if_str,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    let rep_blk = verify_rust_functions_with_opts(
        "deep_blk_str.rs",
        &deep_blk_str,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    let rep_ok = verify_rust_functions_with_opts(
        "shallow_ok.rs",
        shallow_safe_str,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    assert!(rep_ok.is_clean());
    assert_ne!(rep_if.failed.len(), rep_ok.failed.len());
    assert_ne!(rep_blk.failed.len(), rep_ok.failed.len());
    assert!(matches!(
        &rep_if.failed[0].error,
        VerifyError::Utf8CharBoundary { detail } if detail.contains("maximum AST nesting depth")
    ));
    assert!(matches!(
        &rep_blk.failed[0].error,
        VerifyError::Utf8CharBoundary { detail } if detail.contains("maximum AST nesting depth")
    ));

    let shallow_sup = "fn private_div(d: i64) -> i64 { 100 / d }\npub fn caller() -> i64 { private_div(2) }";
    let deep_trunc_sup = format!(
        "fn private_div(d: i64) -> i64 {{ 100 / d }}\npub fn caller(x: i64) -> i64 {{ let a = private_div(2); let b = {}private_div(x){}; a + b }}",
        "{ ".repeat(70),
        " }".repeat(70)
    );
    let rep_shallow_sup = verify_rust_functions_with_opts(
        "shallow_sup.rs",
        shallow_sup,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    let rep_deep_trunc = verify_rust_functions_with_opts(
        "deep_trunc_sup.rs",
        &deep_trunc_sup,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    assert!(rep_shallow_sup.failed.is_empty());
    assert!(!rep_shallow_sup.suppressed_guarded.is_empty());
    assert_eq!(rep_deep_trunc.failed.len(), 1);
    assert_eq!(rep_deep_trunc.failed[0].fn_name, "private_div");
    assert!(rep_deep_trunc.suppressed_guarded.is_empty());
    assert_ne!(rep_deep_trunc.failed.len(), rep_shallow_sup.failed.len());

    let shallow_utf8_sup =
        "fn bad_slice(s: &str, i: usize) -> &str { let _ = format!(\"{s}\"); &s[i..] }\npub fn entry(s: &str) -> &str { bad_slice(s, 0) }";
    let deep_utf8_trunc = format!(
        "fn bad_slice(s: &str, i: usize) -> &str {{ let _ = format!(\"{{s}}\"); &s[i..] }}\npub fn entry(s: &str, raw_i: usize) -> &str {{ let _a = bad_slice(s, 0); {}bad_slice(s, raw_i){} }}",
        "{ ".repeat(70),
        " }".repeat(70)
    );
    let rep_u8_shallow = verify_rust_functions_with_opts(
        "shallow_u8_sup.rs",
        shallow_utf8_sup,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    let rep_u8_deep = verify_rust_functions_with_opts(
        "deep_u8_trunc.rs",
        &deep_utf8_trunc,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        opts,
    );
    assert!(rep_u8_shallow.failed.is_empty());
    assert!(!rep_u8_shallow.suppressed_guarded.is_empty());
    assert!(rep_u8_deep.failed.iter().any(|f| f.fn_name == "bad_slice"));
    assert!(rep_u8_deep.suppressed_guarded.is_empty());
    assert_ne!(rep_u8_deep.failed.len(), rep_u8_shallow.failed.len());
}

#[test]
fn seam2_bijective_slot_tables_and_wide_node_ids() {
    let mut pb = Program::new("buf_overflow");
    for i in 0..256u16 {
        let id = pb.add_buf(format!("b{i}"), 4, true, i + 1, 0, Domain::range(0, 10));
        assert_eq!(id, i as u8);
    }
    assert!(pb.validate().is_ok());
    let extra_id = pb.add_uninit_buf("b256", 4, true, 300, 0, Domain::range(0, 10));
    assert_eq!(extra_id, u8::MAX);
    assert!(pb.bufs[0].pre_init);
    assert_ne!(pb.bufs[0].pre_init, pb.bufs[256].pre_init);
    assert_eq!(pb.validate(), Err(VerifyError::InvalidBuffer(u8::MAX)));

    let mut pp = Program::new("param_overflow");
    for i in 0..256usize {
        pp.add_named_param(format!("p{i}"), Domain::range(0, 10));
    }
    assert!(pp.validate().is_ok());
    let n256 = pp.add_named_param("p256", Domain::range(0, 10));
    assert_eq!(pp.nodes[n256], Op::Param(u8::MAX));
    assert_ne!(pp.nodes[n256], Op::Param(0));
    assert_eq!(pp.validate(), Err(VerifyError::InvalidParam(u8::MAX)));

    let mut pg = Program::new("guard_len_mismatch");
    let x = pg.add_param(Domain::range(0, 10));
    pg.add_output(x);
    assert!(pg.validate().is_ok());
    pg.node_guards.pop();
    assert_ne!(pg.validate(), Ok(()));

    let mut big = Program::new("wide_nodes");
    big.check_reg_budget = false;
    let x = big.add_param(Domain::range(0, 10));
    for _ in 0..65_540 {
        big.push(Op::Const(1));
    }
    let fault_id = big.push(Op::BoundsCheck { idx: x, limit: 5 });
    big.add_output(fault_id);
    assert!(fault_id > usize::from(u16::MAX));
    let batch_res = eval_lanes_x8(&big, &[[0, 1, 2, 3, 4, 5, 6, 7]]);
    assert_eq!(batch_res.fault_nodes[5], u16::MAX);
    assert_ne!(batch_res.fault_nodes[5], fault_id as u16);

    let rep = refine_and_fuzz(&big, RefineConfig::default());
    match rep.verdict {
        ProofVerdict::Counterexample { input, node, fault, .. } => {
            assert_eq!(node, fault_id);
            assert_ne!(node, fault_id & 0xFFFF);
            assert_eq!(input, vec![5]);
            assert_ne!(fault & FAULT_OOB, 0);
        }
        other => panic!("expected Counterexample for >65536 node, got {other:?}"),
    }
    let ce = sample_counterexample(&big, 1).expect("sample counterexample");
    assert_eq!(ce.node, fault_id);
}

#[test]
fn seam3_malformed_domain_and_unvalidated_program_totality() {
    let bad1 = Domain { lo: 10, hi: 5, modulus: 0, rem: -1 };
    let bad2 = Domain { lo: 0, hi: 10, modulus: -5, rem: 0 };
    let bad3 = Domain { lo: 0, hi: 10, modulus: 1, rem: -1 };
    let good = Domain::range(0, 20);

    for bad in [bad1, bad2, bad3] {
        assert_eq!(bad.canonicalize(), Domain::top());
        assert_ne!(bad.canonicalize(), bad);
        assert!(!bad.contains(0));
        assert!(!bad.contains(7));
        assert_eq!(bad.rem_mod(2), None);
        assert_eq!(bad.try_meet(good), None);
        assert_eq!(good.try_meet(bad), None);
        let _ = bad.meet(good);
        let _ = bad.join(good);
        let _ = bad.eval_add_sub(good, false);
        let _ = bad.eval_add_sub(good, true);
        let _ = bad.eval_mul(good);
        assert_eq!(bad.eval_div_rem(good, false), (Domain::top(), true));
        assert_eq!(good.eval_div_rem(bad, true), (Domain::top(), true));
        let _ = bad.eval_square();
        let _ = bad.eval_shl(2);
        let _ = bad.eval_shr(2);
        let _ = bad.eval_bit(good, 0);
        let _ = bad.eval_bit(good, 1);
        let _ = bad.eval_bit(good, 2);
        let _ = bad.eval_cmp(CmpKind::Eq, good);
    }
    assert!(!bad1.is_nonneg());
    assert_eq!(bad1.width_u128(), 0);
    let mut seed = 42u64;
    let batch = sample_batch_x8(&[bad1, bad2, bad3], 0, &mut seed);
    assert_eq!(batch.len(), 3);

    let mut invalid = Program::new("unvalidated");
    invalid.nodes.push(Op::Add(5, 0));
    invalid.node_guards.push(None);
    invalid.outputs.push(0);
    assert!(invalid.infer_domains(&[]).is_empty());
    let (_, status, proven) = invalid.check_obligations(&[]);
    assert_ne!(status, ProofStatus::ProvenSafe);
    assert_eq!(proven, 0);
    let ev = eval_lanes_x8(&invalid, &[]);
    assert_eq!(ev.faults, [FAULT_NONE; LANES]);
    assert!(ev.outputs.is_empty());

    let mut p = Program::new("bad_pdoms");
    let x = p.add_param(Domain::range(0, 10));
    p.add_output(x);
    assert!(p.infer_domains(&[]).is_empty());
    let (_, st_short, _) = p.check_obligations(&[]);
    assert_ne!(st_short, ProofStatus::ProvenSafe);
    let (_, st_bad, _) = p.check_obligations(&[bad1]);
    assert_ne!(st_bad, ProofStatus::ProvenSafe);
    let ev_short = eval_lanes_x8(&p, &[]);
    assert!(ev_short.outputs.is_empty());
}

#[test]
fn seam4_guarded_alloc_havoc_and_check_gen_soundness() {
    let build_store_load = |with_guarded_alloc: bool| {
        let mut p = Program::new("guarded_alloc_load");
        let b = p.add_uninit_buf("scratch", 8, true, 1, 0, Domain::range(0, 255));
        let cond = p.add_param(Domain::range(0, 1));
        let c0 = p.push(Op::Const(0));
        let c42 = p.push(Op::Const(42));
        p.push(Op::Store { buf: b, idx: c0, val: c42 });
        if with_guarded_alloc {
            p.push_guarded(Op::Alloc { buf: b, len: 4 }, Some((cond, true)));
        }
        let ld = p.push(Op::Load { buf: b, idx: c0 });
        p.add_output(ld);
        (p, ld)
    };

    let (clean, ld_clean) = build_store_load(false);
    let (doms_clean, st_clean, _) = clean.check_obligations(&clean.param_domains);
    assert_eq!(st_clean, ProofStatus::ProvenSafe);
    assert_eq!(doms_clean[ld_clean], Domain::exact(42));

    let (buggy, ld_buggy) = build_store_load(true);
    let (doms_buggy, st_buggy, _) = buggy.check_obligations(&buggy.param_domains);
    assert_ne!(doms_buggy[ld_buggy], Domain::exact(42));
    assert_ne!(st_buggy, ProofStatus::ProvenSafe);
    assert!(matches!(
        st_buggy,
        ProofStatus::Uncertain(VerifyError::UninitializedRead { .. })
    ));

    let ev = eval_lanes_x8(&buggy, &[[0, 1, 0, 1, 0, 1, 0, 1]]);
    assert_eq!(ev.faults[0], FAULT_NONE);
    assert_ne!(ev.faults[1] & FAULT_UNINIT, 0);

    let rep = refine_and_fuzz(&buggy, RefineConfig::default());
    assert!(matches!(
        rep.verdict,
        ProofVerdict::Counterexample { ref input, fault, .. }
            if input == &vec![1] && (fault & FAULT_UNINIT) != 0
    ));

    let mut cg = Program::new("guarded_alloc_checkgen");
    let b = cg.add_buf("heap", 8, true, 1, 0, Domain::range(0, 255));
    let cond = cg.add_param(Domain::range(0, 1));
    let gen1 = cg.push(Op::Const(1));
    cg.push_guarded(Op::Alloc { buf: b, len: 4 }, Some((cond, true)));
    let chk = cg.push(Op::CheckGen { buf: b, expected: gen1 });
    cg.add_output(chk);

    let (_, st_cg, _) = cg.check_obligations(&cg.param_domains);
    assert_ne!(st_cg, ProofStatus::ProvenSafe);
    assert!(matches!(
        st_cg,
        ProofStatus::Uncertain(VerifyError::UseAfterFree { .. })
    ));
    let rep_cg = refine_and_fuzz(&cg, RefineConfig::default());
    assert!(matches!(
        rep_cg.verdict,
        ProofVerdict::Counterexample { ref input, fault, .. }
            if input == &vec![1] && (fault & FAULT_UAF) != 0
    ));
}

#[test]
fn seam5_nonlinear_operand_feedback_and_poc_shrinking() {
    let mut quad = Program::new("quad_lock");
    let x = quad.add_param(Domain::range(0, 1_000_000));
    let sq = quad.push(Op::Mul(x, x));
    let k = quad.push(Op::Const(12_321));
    let eq = quad.push(Op::Cmp(CmpKind::Eq, sq, k));
    let z = quad.push(Op::Const(0));
    quad.push_guarded(Op::PanicIfZero(z, 0), Some((eq, true)));
    quad.add_output(sq);

    let qrep = refine_and_fuzz(&quad, RefineConfig::default());
    assert_ne!(
        qrep.verdict,
        ProofVerdict::Incomplete {
            boxes_discharged: qrep.proven_boxes,
            unproven_boxes: qrep.unproven_boxes,
        }
    );
    assert!(matches!(
        qrep.verdict,
        ProofVerdict::Counterexample { ref input, fault, .. }
            if input == &vec![111] && (fault & FAULT_PANIC) != 0
    ));

    let mut xor_lock = Program::new("xor_lock");
    let x = xor_lock.add_param(Domain::range(0, 1_000_000));
    let mask = xor_lock.push(Op::Const(0x5A5A));
    let xr = xor_lock.push(Op::BitXor(x, mask));
    let target = xor_lock.push(Op::Const(0x1234));
    let eq = xor_lock.push(Op::Cmp(CmpKind::Eq, xr, target));
    let z = xor_lock.push(Op::Const(0));
    xor_lock.push_guarded(Op::PanicIfZero(z, 0), Some((eq, true)));
    xor_lock.add_output(xr);

    let xrep = refine_and_fuzz(&xor_lock, RefineConfig::default());
    assert!(matches!(
        xrep.verdict,
        ProofVerdict::Counterexample { ref input, fault, .. }
            if input == &vec![0x486E] && (fault & FAULT_PANIC) != 0
    ));

    let mut wide = Program::new("wide_shrink");
    let x = wide.add_param(Domain::range(0, 1_000_000));
    let k = wide.push(Op::Const(100));
    let gt = wide.push(Op::Cmp(CmpKind::Gt, x, k));
    let z = wide.push(Op::Const(0));
    wide.push_guarded(Op::PanicIfZero(z, 0), Some((gt, true)));
    wide.add_output(x);

    let wrep = refine_and_fuzz(&wide, RefineConfig::default());
    let ce = wrep.counterexamples.first().expect("shrunk counterexample");
    assert_ne!(ce.inputs, vec![1_000_000]);
    assert_eq!(ce.inputs, vec![101]);
    let poc = synthesize_rust_poc_test_for_prog(&wide, ce);
    assert!(poc.contains("let p0 = 101;"), "unexpected PoC:\n{poc}");
}

#[test]
fn seam6_lint_utf8_char_literal_column_preservation() {
    let line1 = "pub fn f1(x: Option<i64>) -> (char, i64) { ('\u{00e9}', x.unwrap()) }";
    let line2 = "pub fn f2(x: Option<i64>) -> (char, i64) { ('\u{1F680}', x.unwrap()) }";
    let line3 = "pub fn f3<'a>(x: Option<&'a str>) -> &'a str { x.unwrap() }";
    let src = format!("{line1}\n{line2}\n{line3}\n");

    let exp1 = line1.find("unwrap").expect("unwrap in line1") + 1;
    let exp2 = line2.find("unwrap").expect("unwrap in line2") + 1;
    let exp3 = line3.find("unwrap").expect("unwrap in line3") + 1;

    let rep = scan_rust_source("utf8_col.rs", &src);
    let panics: Vec<_> = rep
        .findings
        .iter()
        .filter(|f| f.kind == LintKind::PanicCall)
        .collect();
    assert_eq!(panics.len(), 3, "findings: {:?}", rep.findings);
    assert_eq!((panics[0].line, panics[0].col), (1, exp1));
    assert_ne!(panics[0].col, exp1 - 1);
    assert_eq!((panics[1].line, panics[1].col), (2, exp2));
    assert_ne!(panics[1].col, exp2 - 3);
    assert_eq!((panics[2].line, panics[2].col), (3, exp3));
}
