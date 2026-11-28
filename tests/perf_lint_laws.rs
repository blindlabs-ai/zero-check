#![forbid(unsafe_code)]

use std::path::Path;
use std::process::Command;
use zero_check::{
    analyze_rust_source, detect_host_cpu_profile, parse_cpu_spec, resolve_cpu_profile,
    PerfOptions, PerfRule, PerfSeverity, DEFAULT_AMD_ZEN_EPYC_SPEC,
};

#[test]
fn law_parse_all_six_zen_epyc_profiles_and_host_autodetect() {
    let profiles = parse_cpu_spec(DEFAULT_AMD_ZEN_EPYC_SPEC).expect("spec must parse cleanly");
    assert_eq!(profiles.len(), 6, "must parse all 6 canonical AMD Zen/EPYC profiles");
    let expected = [
        ("zen1_naples", 23u32, 32usize, 8usize, 512usize, 8usize, 64usize, "avx2_128x2"),
        ("zen2_rome", 23, 32, 8, 512, 16, 64, "avx2"),
        ("zen3_milan", 25, 32, 8, 512, 32, 64, "avx2"),
        ("zen4_genoa", 25, 32, 8, 1024, 32, 64, "avx512_256x2"),
        ("zen4c_bergamo", 25, 32, 8, 1024, 16, 64, "avx512_256x2"),
        ("zen5_turin", 26, 48, 12, 1024, 32, 64, "avx512_512"),
    ];
    for (p, (name, fam, l1, ways, l2, l3, line, simd)) in profiles.iter().zip(expected) {
        assert_eq!(p.name, name);
        assert_eq!(p.family, fam);
        assert_eq!(p.l1d_kib, l1);
        assert_eq!(p.l1d_ways, ways);
        assert_eq!(p.l2_kib, l2);
        assert_eq!(p.l3_ccx_mib, l3);
        assert_eq!(p.line_bytes, line);
        assert_eq!(p.simd, simd);
    }
    let host = detect_host_cpu_profile(&profiles);
    assert!(host.l1d_kib >= 16 && host.l2_kib >= 128 && host.line_bytes == 64);
    if let Ok(cpuinfo) = std::fs::read_to_string("/proc/cpuinfo") {
        if cpuinfo.contains("Ryzen 9 3900X") {
            assert_eq!(host.name, "zen2_rome", "Ryzen 9 3900X must auto-detect as zen2_rome");
            assert_eq!(host.l1d_kib, 32);
            assert_eq!(host.l2_kib, 512);
        }
    }
    assert!(resolve_cpu_profile("nonexistent_cpu", None).is_err());
}

#[test]
fn knockout_perf01_l1d_l2_residency_and_zen2_vs_zen5_shift() {
    let (zen2, all) = resolve_cpu_profile("zen2_rome", None).expect("zen2_rome");
    let (zen5, _) = resolve_cpu_profile("zen5_turin", None).expect("zen5_turin");
    let opts = PerfOptions::default();

    let bad_u64 = r#"
        pub fn build_recip_bad() -> [u64; 4096] {
            let tbl: [u64; 4096] = [0u64; 4096];
            tbl
        }
    "#;
    let good_u32 = r#"
        pub fn build_recip_good() -> [u32; 4096] {
            let tbl: [u32; 4096] = [0u32; 4096];
            tbl
        }
    "#;
    let rep_bad_z2 = analyze_rust_source("recip.rs", bad_u64, &zen2, &all, opts);
    let rep_good_z2 = analyze_rust_source("recip.rs", good_u32, &zen2, &all, opts);
    let rep_bad_z5 = analyze_rust_source("recip.rs", bad_u64, &zen5, &all, opts);

    let bad_z2_p1: Vec<_> = rep_bad_z2.findings.iter().filter(|f| f.rule == PerfRule::Perf01).collect();
    let good_z2_p1: Vec<_> = rep_good_z2.findings.iter().filter(|f| f.rule == PerfRule::Perf01).collect();
    let bad_z5_p1: Vec<_> = rep_bad_z5.findings.iter().filter(|f| f.rule == PerfRule::Perf01).collect();

    assert_ne!(bad_z2_p1.len(), good_z2_p1.len(), "counterfactual knockout: [u64;4096] must trigger PERF-01 while [u32;4096] clears");
    assert_eq!(bad_z2_p1.len(), 1);
    assert_eq!(bad_z2_p1[0].severity, PerfSeverity::High);
    assert_eq!(bad_z2_p1[0].cache_bytes, 32_768);
    assert!(good_z2_p1.is_empty(), "[u32; 4096] = 16 KiB (50% L1D) must clear PERF-01");
    assert_ne!(bad_z2_p1.len(), bad_z5_p1.len(), "32 KiB is 100% Zen2 L1D cliff but 68% (<75%) on Zen5 48 KiB L1D");

    // Verify L2 overflow shift between Zen 2 (512 KiB L2) and Zen 5 (1024 KiB L2)
    let big_l2 = r#"
        const HASH_SIZE: usize = 1 << 17;
        pub fn alloc_hash() -> Vec<u64> {
            vec![0u64; HASH_SIZE]
        }
    "#;
    let rep_l2_z2 = analyze_rust_source("hash.rs", big_l2, &zen2, &all, opts);
    let rep_l2_z5 = analyze_rust_source("hash.rs", big_l2, &zen5, &all, opts);
    let z2_row = rep_l2_z2.profile_comparison.iter().find(|r| r.profile_name == "zen2_rome").expect("zen2 row");
    let z5_row = rep_l2_z5.profile_comparison.iter().find(|r| r.profile_name == "zen5_turin").expect("zen5 row");
    assert_eq!(z2_row.l2_overflows, 1, "1 MiB exceeds Zen2 512 KiB L2");
    assert_eq!(z5_row.l2_overflows, 0, "1 MiB fits within Zen5 1024 KiB L2");
    assert_ne!(z2_row.l2_overflows, z5_row.l2_overflows);

    // Verify tuple element table sizing: vec![(1u64, 0u8); 4096] = 64 KiB (200% Zen2 L1D)
    let tup_tbl = "pub fn recip_tuple() -> Vec<(u64, u8)> { vec![(1u64, 0u8); 4096] }\n";
    let rep_tup = analyze_rust_source("tup.rs", tup_tbl, &zen2, &all, opts);
    assert!(rep_tup.findings.iter().any(|f| f.rule == PerfRule::Perf01 && f.cache_bytes == 65_536));
}

#[test]
fn knockout_perf02_cache_line_straddle_struct() {
    let (zen2, all) = resolve_cpu_profile("zen2_rome", None).expect("zen2_rome");
    let opts = PerfOptions::default();

    let bad_structs = r#"
        pub struct BadSlot34 {
            pub tag: u32,
            pub cdf: [u16; 15],
        }
        pub struct BadSlot112 {
            pub tag: u32,
            pub hi: [u16; 15],
            pub lo0: [u16; 15],
            pub lo1: [u16; 15],
            pub meta: [u8; 18],
        }
    "#;
    let good_structs = r#"
        #[repr(C, align(32))]
        pub struct GoodSlot32 {
            pub tag: u16,
            pub cdf: [u16; 15],
        }
        #[repr(C, align(64))]
        pub struct GoodSlot128 {
            pub tag: u32,
            pub pad: [u8; 30],
            pub hi: [u16; 15],
            pub lo0: [u16; 15],
            pub lo1: [u16; 15],
            pub pad2: [u8; 4],
        }
    "#;
    let rep_bad = analyze_rust_source("slots.rs", bad_structs, &zen2, &all, opts);
    let rep_good = analyze_rust_source("slots.rs", good_structs, &zen2, &all, opts);
    let bad_p2: Vec<_> = rep_bad.findings.iter().filter(|f| f.rule == PerfRule::Perf02).collect();
    let good_p2: Vec<_> = rep_good.findings.iter().filter(|f| f.rule == PerfRule::Perf02).collect();

    assert_ne!(bad_p2.len(), good_p2.len(), "counterfactual knockout: unaligned 34B/112B structs fail, aligned 32B/128B clear");
    assert_eq!(bad_p2.len(), 2);
    assert!(bad_p2.iter().any(|f| f.cache_bytes >= 34 && f.cache_bytes <= 36));
    assert!(bad_p2.iter().any(|f| f.cache_bytes >= 112 && f.cache_bytes <= 116));
    assert!(good_p2.is_empty(), "aligned 32B / 128B structs must clear PERF-02");
}

#[test]
fn knockout_perf03_perf06_compounding_callgraph_alloc_chain() {
    let (zen2, all) = resolve_cpu_profile("zen2_rome", None).expect("zen2_rome");
    let opts = PerfOptions::default();

    let bad_chain = r#"
        fn inner_alloc_helper(n: usize) -> Vec<u8> {
            let mut tmp = Vec::with_capacity(n);
            tmp.push(1);
            tmp
        }
        pub fn outer_loop(blocks: &[usize]) -> usize {
            let mut acc = 0usize;
            for &n in blocks {
                let buf = inner_alloc_helper(n);
                acc += buf.len();
            }
            acc
        }
    "#;
    let clean_chain = r#"
        fn inner_reuse_helper(scratch: &mut Vec<u8>, n: usize) -> usize {
            scratch.clear();
            scratch.push(n as u8);
            scratch.len()
        }
        pub fn outer_loop(blocks: &[usize]) -> usize {
            let mut scratch = Vec::with_capacity(256);
            let mut acc = 0usize;
            for &n in blocks {
                acc += inner_reuse_helper(&mut scratch, n);
            }
            acc
        }
    "#;
    let rep_bad = analyze_rust_source("chain.rs", bad_chain, &zen2, &all, opts);
    let rep_clean = analyze_rust_source("chain.rs", clean_chain, &zen2, &all, opts);
    let bad_p3: Vec<_> = rep_bad.findings.iter().filter(|f| f.rule == PerfRule::Perf03).collect();
    let clean_p3: Vec<_> = rep_clean.findings.iter().filter(|f| f.rule == PerfRule::Perf03).collect();

    assert_ne!(bad_p3.len(), clean_p3.len(), "counterfactual knockout: caller-loop -> callee-alloc must trigger PERF-03");
    assert_eq!(bad_p3.len(), 1);
    assert!(
        bad_p3[0].compounding_path.contains("outer_loop -> inner_alloc_helper"),
        "expected exact compounding path 'outer_loop -> inner_alloc_helper', got: {}",
        bad_p3[0].compounding_path
    );
    assert!(clean_p3.is_empty(), "hoisted scratch arena reuse must clear PERF-03");
    let formatted = rep_bad.format_report(5);
    assert!(formatted.contains("[PERF-06] Top Compounding Hotspots"));
    assert!(formatted.contains("outer_loop -> inner_alloc_helper"));
}

#[test]
fn knockout_perf04_and_perf05_bitloop_div_and_chain_walk() {
    let (zen2, all) = resolve_cpu_profile("zen2_rome", None).expect("zen2_rome");
    let opts = PerfOptions::default();

    let bad_hot = r#"
        pub fn slow_kernel(src: &[u8], prev: &[usize], freq: u32) -> u32 {
            let mut acc = 0u32;
            for &byte in src {
                for bit in 0..8 {
                    acc ^= ((byte >> bit) as u32) % freq;
                }
                let mut cur = byte as usize;
                while cur != 0 {
                    cur = prev[cur & 1023];
                    acc = acc.wrapping_add(cur as u32);
                }
            }
            acc
        }
    "#;
    let fast_hot = r#"
        pub fn fast_kernel(src: &[u8], recip: u32) -> u32 {
            let mut acc = 0u32;
            for &byte in src {
                let hi = (byte >> 4) as u32;
                let lo = (byte & 15) as u32;
                acc = acc.wrapping_add((hi.wrapping_mul(recip)) >> 12);
                acc = acc.wrapping_add(lo / 16);
            }
            acc
        }
    "#;
    let rep_bad = analyze_rust_source("hot.rs", bad_hot, &zen2, &all, opts);
    let rep_fast = analyze_rust_source("hot.rs", fast_hot, &zen2, &all, opts);

    let bad_p4 = rep_bad.findings.iter().filter(|f| f.rule == PerfRule::Perf04).count();
    let bad_p5 = rep_bad.findings.iter().filter(|f| f.rule == PerfRule::Perf05).count();
    let fast_p4 = rep_fast.findings.iter().filter(|f| f.rule == PerfRule::Perf04).count();
    let fast_p5 = rep_fast.findings.iter().filter(|f| f.rule == PerfRule::Perf05).count();

    assert!(bad_p4 >= 2, "must catch both 0..8 serial bit-loop and runtime % freq, got {bad_p4}");
    assert!(bad_p5 >= 1, "must catch nested prev[...] chain walk at depth >= 2, got {bad_p5}");
    assert_ne!(bad_p4, fast_p4);
    assert_ne!(bad_p5, fast_p5);
    assert_eq!(fast_p4, 0);
    assert_eq!(fast_p5, 0);
}

#[test]
fn cli_perf_advisory_vs_strict_and_default_unchanged() {
    let bin = env!("CARGO_BIN_EXE_zero-check");
    let tmp = std::env::temp_dir().join("zero_check_perf_cli_test.rs");
    std::fs::write(
        &tmp,
        "pub fn hot(xs: &[u32], d: u32) -> u32 { let mut s = 0u32; for &x in xs { let v = Vec::<u8>::with_capacity(64); s = s.wrapping_add(x % d).wrapping_add(v.len() as u32); } s }\n",
    )
    .expect("write temp rs");

    // 1. Default mode (no --perf): must NOT emit PERF lines and exit 0.
    let def = Command::new(bin)
        .args(["--no-ledger", tmp.to_str().expect("utf8")])
        .output()
        .expect("run default zero-check");
    let def_out = String::from_utf8_lossy(&def.stdout);
    assert!(def.status.success(), "default mode must exit 0: {def_out}");
    assert!(!def_out.contains("[PERF-CPU]"), "default mode must not alter output");

    // 2. Advisory --perf mode: prints PERF report and exits 0.
    let adv = Command::new(bin)
        .args(["--no-ledger", "--perf", "--cpu", "zen5_turin", tmp.to_str().expect("utf8")])
        .output()
        .expect("run --perf zero-check");
    let adv_out = String::from_utf8_lossy(&adv.stdout);
    assert!(adv.status.success(), "--perf without --perf-strict must exit 0: {adv_out}");
    assert!(adv_out.contains("[PERF-CPU] profile=zen5_turin"));
    assert!(adv_out.contains("[PERF-06] Top Compounding Hotspots"));

    // 3. Strict --perf-strict mode: exits non-zero on HIGH findings.
    let strict = Command::new(bin)
        .args(["--no-ledger", "--perf", "--perf-strict", "--cpu", "zen2_rome", tmp.to_str().expect("utf8")])
        .output()
        .expect("run --perf-strict zero-check");
    assert!(!strict.status.success(), "--perf-strict must exit non-zero on HIGH perf findings");
    let _ = std::fs::remove_file(&tmp);
    assert!(Path::new(env!("CARGO_MANIFEST_DIR")).join("specs/amd_zen_epyc.spec").is_file());
}
