use std::path::PathBuf;
use std::process::Command;
use zero_check::{
    scan_crate_dir_with_opts, scan_rust_source, scan_rust_source_with_opts,
    verify_rust_functions_with_opts, ArchProfile, Domain, LintKind, LintOptions, RefineConfig,
    RustFeOptions,
};

fn tmp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("zero_check_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("create tmp src dir");
    std::fs::create_dir_all(dir.join("tests")).expect("create tmp tests dir");
    dir
}

#[test]
fn real_world_neg_lit_cast_wrapping_sub_and_test_array_sig_lints() {
    let src_bad = r#"
pub fn bad_casts() -> usize {
    let a = -1 as usize;
    let b = (-5_i64) as u64;
    if a == 0 { return -2 as usize; }
    a + (b as usize)
}
pub fn bad_wrap_idx(buf: &[u8], i: usize) -> u8 {
    if i < buf.len() { buf[i.wrapping_sub(1)] } else { 0 }
}
"#;
    let rep_default = scan_rust_source("bad.rs", src_bad);
    let neg_casts = rep_default.findings.iter().filter(|f| f.kind == LintKind::NegLitUsizeCast).count();
    let wrap_idx = rep_default.findings.iter().filter(|f| f.kind == LintKind::UnguardedIndex).count();
    assert_eq!(neg_casts, 3, "expected 3 unary negative-literal unsigned casts, got {:?}", rep_default.findings);
    assert_eq!(wrap_idx, 1, "expected 1 wrapping_sub index warning, got {:?}", rep_default.findings);

    let rep_ext = scan_rust_source_with_opts("bad.rs", src_bad, LintOptions::external_audit());
    assert_eq!(rep_ext.error_count(), 3, "audit_external must retain all 3 NegLitUsizeCast errors");
    assert_eq!(rep_ext.warning_count(), 0, "audit_external must suppress UnguardedIndex warnings");

    let src_clean = r#"
pub fn safe_sub_casts(x: usize, buf: &[u8], a: &[usize; 4]) -> usize {
    let d1 = x - 1 as usize;
    let d2 = buf.len() - 1 as usize;
    let d3 = a[0] - 1 as usize;
    let d4 = foo(-1) as usize;
    let mask = 0u64.wrapping_sub(1);
    let idx = buf[d1.wrapping_sub(1) & 3] as usize;
    d1 + d2 + d3 + d4 + (mask as usize) + idx
}
fn foo(v: i64) -> i64 { v }

#[test]
fn arr_sig() -> [u8; 4] {
    let x = 1u64 << 99;
    [x as u8; 4]
}

#[cfg(all(test, not(miri)))]
fn cfg_all_test_helper(buf: &[u8; 16]) -> [u8; 4] {
    let y = 1u64 / 0;
    [buf[0] ^ (y as u8); 4]
}
"#;
    let rep_clean_ext = scan_rust_source_with_opts("clean.rs", src_clean, LintOptions::external_audit());
    assert_eq!(
        rep_clean_ext.findings.len(),
        0,
        "guarded casts, array-sig #[test], and #[cfg(all(test))] must have 0 findings in external audit: {:?}",
        rep_clean_ext.findings
    );
    assert_ne!(rep_ext.is_clean(), rep_clean_ext.is_clean());
}

#[test]
fn real_world_cve_hunt_bugs_pocs_and_zero_false_positives() {
    let dir = tmp_dir("cve_hunt");
    let buggy_lib = r#"
#[allow(dead_code)]
pub fn png_chunk_end_u32(off: u32, len: u32) -> u32 {
    off + len
}

pub struct Chunk;
impl Chunk {
    pub fn bad_tail_read(buf: &[u8], off: usize) -> u8 {
        if off <= buf.len() - 4 { buf[off] } else { 0 }
    }
    pub fn safe_tail_read(buf: &[u8], off: usize) -> u8 {
        if buf.len() >= 4 && off <= buf.len() - 4 { buf[off + 3] } else { 0 }
    }
}

pub fn http_header_byte(buf: &[u8], idx: usize) -> u8 {
    buf[idx]
}

pub fn http_header_safe(buf: &[u8], idx: usize) -> u8 {
    if idx < buf.len() { buf[idx] } else { 0 }
}

pub fn varint_decode_shift(byte: u8, shift: u32) -> u64 {
    (byte as u64) << shift
}

pub fn varint_decode_safe(byte: u8, shift: u32) -> u64 {
    if shift < 64 { (byte as u64) << shift } else { 0 }
}

pub fn parse_tag_unwrap(tag: u8) -> u32 {
    let opt = if tag == 1 { Some(42u32) } else { None };
    opt.unwrap()
}

pub fn parse_tag_safe(tag: u8) -> u32 {
    let opt = if tag == 1 { Some(42u32) } else { None };
    opt.unwrap_or(0)
}

pub fn bad_signed_cast_lut(b: u8, lut: &[u8; 256]) -> u8 {
    lut[(b as i8) as usize]
}

pub fn bad_arr_val_oob(arr: [i32; 4], idx: usize) -> i32 {
    arr[idx]
}

pub fn bad_ref_div(x: &u32, y: &mut u32) -> u32 {
    *y = 1;
    *y / *x
}

pub fn bad_ref_write_only(x: &u32, y: &mut u32) -> u32 {
    *y = 100u32 / *x;
    1
}

pub fn bad_bool_div(flag: bool, denom: u32) -> u32 {
    if flag { 100u32 / denom } else { 0 }
}

pub fn bad_opt_bool_div(opt: Option<bool>, denom: u32) -> u32 {
    if let Some(flag) = opt {
        if flag { 100u32 / denom } else { 0 }
    } else {
        0
    }
}

pub fn bad_opt_bool_match(opt: Option<bool>, denom: u32) -> u32 {
    match opt {
        Some(true) => 100u32 / denom,
        _ => 0,
    }
}

pub fn bad_if_let_some_true(opt: Option<bool>, denom: u32) -> u32 {
    if let Some(true) = opt { 100u32 / denom } else { 0 }
}

pub fn ok_widening_u8(b: u8) -> i32 {
    (b as i32) + 1
}
"#;
    let test_noise = r#"
#[cfg(test)]
mod tests {
    #[test]
    fn noisy_test_harness() -> [u8; 4] {
        let _x = 1u64 << 99;
        [0u8; 4]
    }
}
"#;
    let noisy_int_test = r#"
#[test]
fn integration_noise() {
    let _bad = 1u64 / 0;
    unsafe {}
}
"#;
    std::fs::write(dir.join("src/lib.rs"), buggy_lib).expect("write buggy lib.rs");
    std::fs::write(dir.join("src/test_noise.rs"), test_noise).expect("write src/test_noise.rs");
    std::fs::write(dir.join("tests/noise.rs"), noisy_int_test).expect("write tests/noise.rs");

    // 1. Direct API check under external audit mode.
    let rep = verify_rust_functions_with_opts(
        "lib.rs",
        buggy_lib,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        RustFeOptions::external_audit(),
    );
    let failed_names: Vec<&str> = rep.failed.iter().map(|f| f.fn_name.as_str()).collect();
    let proven_names: Vec<&str> = rep.proven.iter().map(|(n, _)| n.as_str()).collect();

    let must_fail = [
        "png_chunk_end_u32",
        "Chunk::bad_tail_read",
        "http_header_byte",
        "varint_decode_shift",
        "parse_tag_unwrap",
        "bad_signed_cast_lut",
        "bad_arr_val_oob",
        "bad_ref_div",
        "bad_ref_write_only",
        "bad_bool_div",
        "bad_opt_bool_div",
        "bad_opt_bool_match",
        "bad_if_let_some_true",
    ];
    for name in must_fail {
        assert!(
            failed_names.contains(&name),
            "expected {name} to fail; failed={failed_names:?} proven={proven_names:?} skipped={:?}",
            rep.skipped_non_kernel_fns
        );
    }
    for must_pass in [
        "Chunk::safe_tail_read",
        "http_header_safe",
        "varint_decode_safe",
        "parse_tag_safe",
        "ok_widening_u8",
    ] {
        assert!(
            proven_names.contains(&must_pass),
            "expected guarded {must_pass} to prove with 0 FP; proven={proven_names:?} failed={:?} skipped={:?}",
            rep.failed,
            rep.skipped_non_kernel_fns
        );
    }

    // Every failure must have a concrete synthesized #[test] PoC.
    for f in &rep.failed {
        let poc = f.poc_test.as_deref().unwrap_or_else(|| panic!("missing poc_test for {}", f.fn_name));
        assert!(poc.contains("#[test]"), "PoC for {} missing #[test]: {poc}", f.fn_name);
        if f.fn_name == "Chunk::bad_tail_read" {
            assert!(poc.contains("fn poc_Chunk_bad_tail_read()"), "invalid method PoC header: {poc}");
            assert!(poc.contains("Chunk::bad_tail_read(&buf"), "missing slice arg in PoC: {poc}");
        }
    }

    // 2. CLI `--audit-external --emit-poc --quiet` on the temp crate (must ignore tests/noise.rs and src/test_noise.rs),
    //    then compile and execute EVERY emitted PoC live with `rustc --edition 2021 --test`!
    let bin = env!("CARGO_BIN_EXE_zero-check");
    let out = Command::new(bin)
        .args(["--no-ledger", "--audit-external", "--emit-poc", "--quiet"])
        .arg(&dir)
        .output()
        .expect("run zero-check --audit-external --emit-poc --quiet");
    assert_eq!(out.status.code(), Some(1), "buggy crate must exit 1");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!stderr.contains("noise.rs"), "tests/ dir must be excluded under --audit-external: {stderr}");
    assert!(!stderr.contains("test_noise.rs"), "cfg(test) file must be excluded under --audit-external: {stderr}");
    assert!(stdout.contains("fn poc_Chunk_bad_tail_read()"), "missing PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_png_chunk_end_u32()"), "missing u32 PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_parse_tag_unwrap()"), "missing unwrap PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_signed_cast_lut()"), "missing &[u8; 256] PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_arr_val_oob()"), "missing [i32; 4] PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_ref_div()"), "missing &u32/&mut u32 PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_ref_write_only()"), "missing write-only &mut u32 PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_bool_div()"), "missing bool PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_opt_bool_div()"), "missing Option<bool> PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_opt_bool_match()"), "missing match Some(true) PoC on stdout: {stdout}");
    assert!(stdout.contains("fn poc_bad_if_let_some_true()"), "missing if let Some(true) PoC on stdout: {stdout}");

    let poc_rs = dir.join("poc_harness.rs");
    let poc_bin = dir.join("poc_harness");
    std::fs::write(&poc_rs, format!("{buggy_lib}\n{stdout}\n")).expect("write poc_harness.rs");
    let rustc_out = Command::new("rustc")
        .args(["--edition", "2021", "--test", "-o"])
        .arg(&poc_bin)
        .arg(&poc_rs)
        .output()
        .expect("compile emitted PoCs with rustc --edition 2021 --test");
    assert!(
        rustc_out.status.success(),
        "emitted PoCs must compile cleanly with rustc --edition 2021 --test;\nstderr:\n{}\n--- emitted PoCs ---\n{stdout}",
        String::from_utf8_lossy(&rustc_out.stderr),
    );
    let run_out = Command::new(&poc_bin)
        .output()
        .expect("execute compiled PoC test binary");
    let run_stdout = String::from_utf8_lossy(&run_out.stdout);
    assert_ne!(
        run_out.status.code(),
        Some(0),
        "compiled PoC binary must panic on emitted counterexamples;\nstdout:\n{run_stdout}"
    );
    let expected_summary = format!("0 passed; {} failed", must_fail.len());
    assert!(
        run_stdout.contains(&expected_summary),
        "expected every emitted PoC to panic ({expected_summary});\nstdout:\n{run_stdout}\n--- emitted PoCs ---\n{stdout}"
    );
    assert_ne!(rustc_out.status.code(), run_out.status.code());

    // 3. Clean external crate with #[allow], .clamp(), >14 live vars, #[cfg(test)], and tests/ dir:
    //    Mode B (--audit-external) MUST exit 0 (0 FP), while Mode A (--kernel-strict) MUST exit 1!
    let clean_dir = tmp_dir("cve_clean");
    let clean_lib = r#"
#[allow(dead_code)]
pub fn guarded_wide_parser(buf: &[u8], off: usize, a: i64, b: i64) -> i64 {
    let v0 = a.wrapping_add(1);
    let v1 = b.wrapping_add(2);
    let v2 = v0.wrapping_add(v1);
    let v3 = v2.wrapping_add(3);
    let v4 = v3.wrapping_add(4);
    let v5 = v4.wrapping_add(5);
    let v6 = v5.wrapping_add(6);
    let v7 = v6.wrapping_add(7);
    let v8 = v7.wrapping_add(8);
    let v9 = v8.wrapping_add(9);
    let v10 = v9.wrapping_add(10);
    let v11 = v10.wrapping_add(11);
    let v12 = v11.wrapping_add(12);
    let v13 = v12.wrapping_add(13);
    let v14 = v13.wrapping_add(14);
    let v15 = v14.wrapping_add(15);
    let head = if buf.len() >= 4 && off <= buf.len() - 4 { buf[off + 3] as i64 } else { 0 };
    head.wrapping_add(v0).wrapping_add(v1).wrapping_add(v2).wrapping_add(v3)
        .wrapping_add(v4).wrapping_add(v5).wrapping_add(v6).wrapping_add(v7)
        .wrapping_add(v8).wrapping_add(v9).wrapping_add(v10).wrapping_add(v11)
        .wrapping_add(v12).wrapping_add(v13).wrapping_add(v14).wrapping_add(v15)
}

#[allow(dead_code)]
pub fn external_clamp_helper(x: i32) -> i32 {
    x.clamp(0, 100)
}

#[cfg(test)]
mod tests {
    #[test]
    fn arr_sig() -> [u8; 4] {
        let _x = 1u64 << 99;
        [0u8; 4]
    }
}
"#;
    std::fs::write(clean_dir.join("src/lib.rs"), clean_lib).expect("write clean lib.rs");
    std::fs::write(clean_dir.join("tests/noise.rs"), noisy_int_test).expect("write clean tests/noise.rs");

    let ext_lint = scan_crate_dir_with_opts(&clean_dir, &[], LintOptions::external_audit()).expect("ext lint");
    assert_eq!(ext_lint.files_scanned, 1, "tests/ must be excluded");
    assert_eq!(ext_lint.findings.len(), 0, "clean external crate must have 0 lint findings: {:?}", ext_lint.findings);

    let ext_out = Command::new(bin)
        .args(["--no-ledger", "--audit-external", "--emit-poc"])
        .arg(&clean_dir)
        .output()
        .expect("run zero-check --audit-external on clean crate");
    let strict_out = Command::new(bin)
        .args(["--no-ledger", "--kernel-strict"])
        .arg(&clean_dir)
        .output()
        .expect("run zero-check --kernel-strict on clean crate");

    assert_eq!(
        ext_out.status.code(),
        Some(0),
        "Mode B (--audit-external) must exit 0 with 0 FP on guarded external crate; stdout={} stderr={}",
        String::from_utf8_lossy(&ext_out.stdout),
        String::from_utf8_lossy(&ext_out.stderr),
    );
    assert_eq!(strict_out.status.code(), Some(1), "Mode A (--kernel-strict) must reject #[allow], .clamp(), and tests/");
    assert_ne!(ext_out.status.code(), strict_out.status.code());

    // 4. Direct Extended-GCD CRT meet verification.
    let m = Domain::congruent(0, 100, 4, 1).try_meet(Domain::congruent(0, 100, 3, 2)).expect("CRT meet");
    assert_eq!((m.lo, m.hi, m.modulus, m.rem), (5, 89, 12, 5));

    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&clean_dir);
}

#[test]
fn async_fn_await_havoc_and_live_future_poll_pocs() {
    let dir = tmp_dir("async_poc_hunt");
    let async_lib = r#"#![forbid(unsafe_code)]

mod ext {
    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    pub async fn reset_state(s: &mut u32) -> Result<usize, u8> {
        *s = 0;
        Ok(4)
    }

    pub async fn fill_zero(buf: &mut [u8]) -> Result<usize, u8> {
        for b in buf.iter_mut() {
            *b = 0;
        }
        Ok(buf.len())
    }

    pub async fn read_into(buf: &mut [u8]) -> Result<usize, u8> {
        if !buf.is_empty() {
            buf[0] = 0;
        }
        Ok(buf.len())
    }

    pub struct YieldOnce {
        pub yielded: bool,
    }

    impl Future for YieldOnce {
        type Output = ();
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
            if self.yielded {
                Poll::Ready(())
            } else {
                self.yielded = true;
                cx.waker().wake_by_ref();
                Poll::Pending
            }
        }
    }
}

use ext::YieldOnce;

async fn read_hdr_tag(b: &[u8]) -> Result<u8, u8> {
    if b.is_empty() { Err(1) } else { Ok(b[0]) }
}

pub async fn async_read_frame(buf: &[u8], off: u32, len: u32) -> Result<u32, u8> {
    let _tag = read_hdr_tag(buf).await?;
    Ok(off + len)
}

pub async fn async_read_frame_safe(buf: &[u8], off: u32, len: u32) -> Result<u32, u8> {
    let _tag = read_hdr_tag(buf).await?;
    Ok(off.wrapping_add(len))
}

pub struct AsyncFramer {
    pub denom: u32,
}

impl AsyncFramer {
    pub async fn bad_tail_await(buf: &[u8], off: usize) -> Result<u8, u8> {
        let _tag = read_hdr_tag(buf).await?;
        if off <= buf.len() - 4 { Ok(buf[off]) } else { Ok(0) }
    }

    pub async fn safe_tail_await(buf: &[u8], off: usize) -> Result<u8, u8> {
        let _tag = read_hdr_tag(buf).await?;
        if buf.len() >= 4 && off <= buf.len() - 4 { Ok(buf[off + 3]) } else { Ok(0) }
    }

    pub async fn bad_self_mut(&mut self) -> Result<u32, u8> {
        if self.denom == 0 {
            return Ok(0);
        }
        let _n = ext::reset_state(&mut self.denom).await?;
        Ok(100u32 / self.denom)
    }
}

pub struct AsyncReader {
    pub scale: u32,
}

impl AsyncReader {
    pub async fn bad_div_await(&self, buf: &[u8]) -> Result<u32, u8> {
        let _tag = read_hdr_tag(buf).await?;
        Ok(100u32 / self.scale)
    }
}

pub async fn bad_local_mut_await() -> Result<u32, u8> {
    let mut denom: u32 = 10;
    let _n = ext::reset_state(&mut denom).await?;
    Ok(100u32 / denom)
}

pub async fn bad_reborrow_mut_await(state: &mut u32) -> Result<u32, u8> {
    if *state == 0 {
        return Ok(0);
    }
    let _n = ext::reset_state(state).await?;
    Ok(100u32 / *state)
}

pub async fn bad_buf_mut_await() -> Result<u8, u8> {
    let mut buf = [1u8; 4];
    let pre = 100u8 / buf[0];
    let _n = ext::fill_zero(&mut buf).await?;
    Ok(pre / buf[0])
}

pub async fn bad_yield_once_await(x: u32) -> u32 {
    YieldOnce { yielded: false }.await;
    100u32 / x
}

pub async fn safe_slice_mut_len_invariant_await(buf: &mut [u8], off: usize) -> Result<u8, u8> {
    if buf.len() >= 4 && off <= buf.len() - 4 {
        let _n = ext::read_into(buf).await?;
        Ok(buf[off + 3])
    } else {
        Ok(0)
    }
}

pub async fn safe_pre_await_const_buf_await() -> Result<u8, u8> {
    let mut buf = [2u8; 4];
    let pre = 100u8 / buf[0];
    let _n = ext::fill_zero(&mut buf).await?;
    Ok(pre)
}
"#;
    std::fs::write(dir.join("src/lib.rs"), async_lib).expect("write async lib.rs");

    // 1. Direct API check under external audit mode.
    let rep = verify_rust_functions_with_opts(
        "lib.rs",
        async_lib,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        RustFeOptions::external_audit(),
    );
    let failed_names: Vec<&str> = rep.failed.iter().map(|f| f.fn_name.as_str()).collect();
    let proven_names: Vec<&str> = rep.proven.iter().map(|(n, _)| n.as_str()).collect();
    assert!(
        rep.skipped_non_kernel_fns.is_empty(),
        "expected 0 skipped async fns, got {:?}",
        rep.skipped_non_kernel_fns
    );

    let must_fail = [
        "async_read_frame",
        "AsyncFramer::bad_tail_await",
        "AsyncFramer::bad_self_mut",
        "AsyncReader::bad_div_await",
        "bad_local_mut_await",
        "bad_reborrow_mut_await",
        "bad_buf_mut_await",
        "bad_yield_once_await",
    ];
    for name in must_fail {
        assert!(
            failed_names.contains(&name),
            "expected async fn {name} to fail; failed={failed_names:?} proven={proven_names:?}"
        );
    }
    assert_eq!(failed_names.len(), must_fail.len(), "unexpected extra failures: {failed_names:?}");

    for must_pass in [
        "read_hdr_tag",
        "async_read_frame_safe",
        "AsyncFramer::safe_tail_await",
        "safe_slice_mut_len_invariant_await",
        "safe_pre_await_const_buf_await",
    ] {
        assert!(
            proven_names.contains(&must_pass),
            "expected guarded async fn {must_pass} to prove with 0 FP; proven={proven_names:?} failed={:?}",
            rep.failed
        );
    }

    // Every async failure must emit a 100% safe Waker::noop() + std::pin::pin! + Future::poll PoC.
    for f in &rep.failed {
        let poc = f.poc_test.as_deref().unwrap_or_else(|| panic!("missing async poc_test for {}", f.fn_name));
        assert!(poc.contains("std::task::Waker::noop()"), "missing Waker::noop() in PoC for {}: {poc}", f.fn_name);
        assert!(poc.contains("std::pin::pin!("), "missing std::pin::pin! in PoC for {}: {poc}", f.fn_name);
        assert!(poc.contains("std::future::Future::poll("), "missing Future::poll in PoC for {}: {poc}", f.fn_name);
        assert!(!poc.contains("unsafe"), "emitted async PoC must contain 0 unsafe tokens: {poc}");
    }

    // 2. CLI `--audit-external --emit-poc --quiet`, then compile & execute EVERY async PoC live
    //    under `#![forbid(unsafe_code)]` via `rustc --edition 2021 --test` and assert 0 passed; N failed!
    let bin = env!("CARGO_BIN_EXE_zero-check");
    let out = Command::new(bin)
        .args(["--no-ledger", "--audit-external", "--emit-poc", "--quiet"])
        .arg(&dir)
        .output()
        .expect("run zero-check --audit-external --emit-poc --quiet on async crate");
    assert_eq!(out.status.code(), Some(1), "buggy async crate must exit 1");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(!stdout.contains("unsafe"), "CLI emitted async PoCs must contain 0 unsafe tokens:\n{stdout}");
    for expected_fn in [
        "fn poc_async_read_frame()",
        "fn poc_AsyncFramer_bad_tail_await()",
        "fn poc_AsyncFramer_bad_self_mut()",
        "fn poc_AsyncReader_bad_div_await()",
        "fn poc_bad_local_mut_await()",
        "fn poc_bad_reborrow_mut_await()",
        "fn poc_bad_buf_mut_await()",
        "fn poc_bad_yield_once_await()",
    ] {
        assert!(stdout.contains(expected_fn), "missing {expected_fn} on stdout:\n{stdout}");
    }

    let poc_rs = dir.join("async_poc_harness.rs");
    let poc_bin = dir.join("async_poc_harness");
    std::fs::write(&poc_rs, format!("{async_lib}\n{stdout}\n")).expect("write async_poc_harness.rs");
    let rustc_out = Command::new("rustc")
        .args(["--edition", "2021", "--test", "-o"])
        .arg(&poc_bin)
        .arg(&poc_rs)
        .output()
        .expect("compile emitted async PoCs with rustc --edition 2021 --test");
    assert!(
        rustc_out.status.success(),
        "emitted async PoCs must compile cleanly under #![forbid(unsafe_code)];\nstderr:\n{}\n--- emitted PoCs ---\n{stdout}",
        String::from_utf8_lossy(&rustc_out.stderr),
    );
    let run_out = Command::new(&poc_bin)
        .output()
        .expect("execute compiled async PoC test binary");
    let run_stdout = String::from_utf8_lossy(&run_out.stdout);
    assert_ne!(
        run_out.status.code(),
        Some(0),
        "compiled async PoC binary must panic on every polled witness;\nstdout:\n{run_stdout}"
    );
    let expected_summary = format!("0 passed; {} failed", must_fail.len());
    assert!(
        run_stdout.contains(&expected_summary),
        "expected every emitted async PoC to panic via Future::poll ({expected_summary});\nstdout:\n{run_stdout}\n--- emitted PoCs ---\n{stdout}"
    );
    assert_ne!(rustc_out.status.code(), run_out.status.code());

    // 3. String-level unsafe-qualifier skip & zero-attribute-bleed regression (8 unsafe variants).
    let unsafe_src = r#"
/// @domain x: 1..=10
pub unsafe fn u_plain(x: u32) -> u32 { 100 / x }
pub fn safe_must_fail_no_leak(x: u32) -> u32 { 100 / x }
pub unsafe async fn u_unsafe_async(x: u32) -> u32 { 100 / x }
pub async unsafe fn u_async_unsafe(x: u32) -> u32 { 100 / x }
pub const unsafe fn u_const_unsafe(x: u32) -> u32 { 100 / x }
pub unsafe extern "C" fn u_extern_unsafe(x: u32) -> u32 { 100 / x }
pub struct S;
impl S {
    pub unsafe fn m_plain(x: u32) -> u32 { 100 / x }
    pub unsafe async fn m_unsafe_async(x: u32) -> u32 { 100 / x }
    pub async unsafe fn m_async_unsafe(x: u32) -> u32 { 100 / x }
}
pub fn safe_after_unsafe(x: u32) -> u32 { if x > 0 { 100 / x } else { 0 } }
"#;
    let urep = verify_rust_functions_with_opts(
        "unsafe_skip.rs",
        unsafe_src,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        RustFeOptions::external_audit(),
    );
    assert_eq!(urep.skipped_non_kernel_fns.len(), 8, "all 8 unsafe fn variants must be skipped: {:?}", urep.skipped_non_kernel_fns);
    assert_eq!(urep.failed.len(), 1, "safe_must_fail_no_leak must fail (no @domain leak from unsafe fn): {:?}", urep.failed);
    assert_eq!(urep.failed[0].fn_name, "safe_must_fail_no_leak");
    assert_eq!(urep.proven.len(), 1, "only safe_after_unsafe may prove: {:?}", urep.proven);
    assert_eq!(urep.proven[0].0, "safe_after_unsafe");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn external_21_fp_regression_and_counterfactual_knockouts() {
    // 1. Lexical ShiftOverflow (u128 fields/macros/arrays/parens) & modular u16/u32 casts must pass.
    let lex_ok = r#"
pub struct Rec { pub nan_mask: u128 }
pub fn field_shift(rec: &Rec) -> u64 { (rec.nan_mask >> 64) as u64 }
pub fn paren_shift(a: u128, b: u128) -> u128 { let mid = a + b; ((mid & 0x7FFF_FFFF_FFFF_FFFF) << 64) | (mid >> 63) }
pub fn array_and_macro(x: u128) -> u64 {
    macro_rules! hi { ($v:expr) => { ($v >> 64) as u64 }; }
    let hp = [x; 4];
    hi!(x) ^ ((hp[0] >> 64) as u64)
}
pub fn modular_bam() -> [u16; 2] { [-4096i16 as u16, -1i32 as u32 as u16] }
"#;
    let rep_lex_ok = scan_rust_source_with_opts("lex_ok.rs", lex_ok, LintOptions::external_audit());
    assert_eq!(rep_lex_ok.error_count(), 0, "valid u128 shifts and modular u16/u32 casts must have 0 errors: {:?}", rep_lex_ok.findings);

    // Counterfactual lexical knockouts: genuine u64 << 64, u128 << 128, u32 << 32, and -1 as usize must still fail.
    for (name, src, kind) in [
        ("bad_u64_var.rs", "pub fn f(x: u64) -> u64 { x << 64 }\n", LintKind::ShiftOverflow),
        ("bad_u64_lit.rs", "pub fn f() -> u64 { 1u64 << 64 }\n", LintKind::ShiftOverflow),
        ("bad_u128_128.rs", "pub fn f(x: u128) -> u128 { x << 128 }\n", LintKind::ShiftOverflow),
        ("bad_u32_32.rs", "pub fn f(x: u32) -> u32 { x << 32 }\n", LintKind::ShiftOverflow),
        ("bad_neg_usize.rs", "pub fn f() -> usize { -1 as usize }\n", LintKind::NegLitUsizeCast),
    ] {
        let rep = scan_rust_source_with_opts(name, src, LintOptions::external_audit());
        assert_ne!(rep.error_count(), 0, "counterfactual {name} must fail closed");
        assert!(rep.findings.iter().any(|f| f.kind == kind), "counterfactual {name} expected {kind:?}, got {:?}", rep.findings);
    }

    // 2. All 7 total Rust prover patterns must prove cleanly.
    let prover_ok = r#"
pub fn pack_decoded_lag10(d_exp: i32, sgn: usize) -> u32 {
    1u32 | (((d_exp.max(-16).min(16) + 16) as u32) << 1) | ((sgn as u32) << 7)
}
pub fn shr_rne_u64(val: u64, shift: u32) -> u64 {
    if shift == 0 { return val; }
    if shift >= 64 { return u64::from(shift == 64 && val > (1u64 << 63)); }
    let (rem, half, q) = (val & ((1u64 << shift) - 1), 1u64 << (shift - 1), val >> shift);
    q + u64::from(rem > half || (rem == half && (q & 1) != 0))
}
pub fn mode4_tile_rows(nrows: usize, ncols: usize) -> usize {
    if nrows == 0 { 0 }
    else if ncols == 1 { nrows.min(4096).max(1) }
    else if ncols < 8 { nrows.min(8192).max(1) }
    else { nrows.div_ceil(nrows.div_ceil(65_536).max(1)) }
}
pub fn slice_at<'a>(buf: &'a [u8], off: usize, len: usize) -> Result<&'a [u8], &'static str> {
    let end = off.checked_add(len).ok_or("overflow")?;
    buf.get(off..end).ok_or("oob")
}
pub const fn zz_encode_i64(v: i64) -> u64 { ((v << 1) ^ (v >> 63)) as u64 }
pub fn bias_i64(v: i64) -> u64 { (v as u64) ^ (1u64 << 63) }
pub fn take_be_slice<'a>(b: &'a [u8], pos: &mut usize) -> Option<&'a [u8]> {
    let n = u16::from_be_bytes([*b.get(*pos)?, *b.get(pos.checked_add(1)?)?]) as usize;
    let start = pos.checked_add(2)?;
    let end = start.checked_add(n)?;
    let out = b.get(start..end)?;
    *pos = end;
    Some(out)
}
"#;
    let rep_ok = verify_rust_functions_with_opts("prover_ok.rs", prover_ok, ArchProfile::X86_64Avx2, RefineConfig::default(), RustFeOptions::external_audit());
    assert_eq!(rep_ok.failed.len(), 0, "all 7 total patterns must prove cleanly: {:?}", rep_ok.failed);
    assert_eq!(rep_ok.proven.len(), 7, "expected all 7 functions proven: {:?}", rep_ok.proven);

    // Counterfactual prover knockouts: unguarded add, div_ceil(0), shift >= 64 must still fail.
    let prover_bad = r#"
pub fn bad_add(a: usize, b: usize) -> usize { a + b }
pub fn bad_div_ceil(a: usize, d: usize) -> usize { a.div_ceil(d) }
pub fn bad_shift(x: u64, s: u32) -> u64 { x << s }
"#;
    let rep_bad = verify_rust_functions_with_opts("prover_bad.rs", prover_bad, ArchProfile::X86_64Avx2, RefineConfig::default(), RustFeOptions::external_audit());
    assert_ne!(rep_ok.failed.len(), rep_bad.failed.len());
    assert_eq!(rep_bad.failed.len(), 3, "all 3 unguarded counterfactuals must fail: {:?}", rep_bad.failed);
}

#[test]
fn tokenize_multibyte_utf8_comments_no_panic_knockout() {
    let ok_src = concat!(
        "/* block comment with em-dash \u{2014}, arrow \u{2192}, and CJK \u{4e2d} */\n",
        "// line comment \u{2014} end\n",
        "/// doc comment \u{2014} note\n",
        "pub fn ok(x: u8) -> u16 { (x as u16) + 1 }\n",
    );
    let bad_src = concat!(
        "/* nested /* block \u{2014} */ comment \u{2192} before bug */\n",
        "pub fn bad(x: u32, d: u32) -> u32 { x / d }\n",
    );
    let rep_ok = verify_rust_functions_with_opts(
        "utf8_ok.rs",
        ok_src,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        RustFeOptions::external_audit(),
    );
    let rep_bad = verify_rust_functions_with_opts(
        "utf8_bad.rs",
        bad_src,
        ArchProfile::X86_64Avx2,
        RefineConfig::default(),
        RustFeOptions::external_audit(),
    );
    assert_eq!(rep_ok.failed.len(), 0, "UTF-8 comments must not panic or fail: {:?}", rep_ok.failed);
    assert_eq!(rep_ok.proven.len(), 1, "expected ok() proven: {:?}", rep_ok.proven);
    assert_ne!(rep_ok.failed.len(), rep_bad.failed.len(), "knockout: bad() after UTF-8 comment must fail");
    assert_eq!(rep_bad.failed.len(), 1, "expected DivZero failure in bad(): {:?}", rep_bad.failed);
}

#[test]
fn interprocedural_reachability_suppression_soundness_and_knockouts() {
    let opts = RustFeOptions::external_audit();
    let cfg = RefineConfig::default();
    let arch = ArchProfile::X86_64Avx2;

    // 1. All 4 Bun/robobun caller-guarded helper patterns cleanly suppressed.
    let pat1 = r#"
pub fn substring(self_: &[u8], start: Option<usize>, stop: Option<usize>) -> &[u8] {
    let sta = start.unwrap_or(0);
    let sto = stop.unwrap_or(self_.len());
    &self_[sta.min(self_.len())..sto.min(self_.len())]
}
pub fn caller_sub<'a>(s: &'a [u8]) -> &'a [u8] { substring(s, Some(0), None) }
"#;
    let r1 = verify_rust_functions_with_opts("p1.rs", pat1, arch, cfg, opts);
    assert_eq!(r1.failed.len(), 0, "pat1 stop=None should be suppressed: {:?}", r1.failed);
    assert_eq!(r1.suppressed_guarded.len(), 1, "pat1 suppressed count: {:?}", r1.suppressed_guarded);

    let pat2 = r#"
pub fn push_digit(acc: u64, digit: u64, bits_per_digit: u32) -> u64 {
    (acc << bits_per_digit) | digit
}
pub fn parse_int_radix(val: u64, d: u64, radix: i32) -> u64 {
    if radix != 0 && !(2..=36).contains(&radix) { return 0; }
    let radix = if radix == 0 { 10 } else { radix as u32 };
    if radix.is_power_of_two() { return push_digit(val, d, radix.trailing_zeros()); }
    0
}
"#;
    let r2 = verify_rust_functions_with_opts("p2.rs", pat2, arch, cfg, opts);
    assert_eq!(r2.failed.len(), 0, "pat2 pow2 trailing_zeros should be suppressed: {:?}", r2.failed);
    assert_eq!(r2.suppressed_guarded.len(), 1, "pat2 suppressed count: {:?}", r2.suppressed_guarded);

    let pat3_guarded = r#"
pub fn u32_from_bytes(b: &[u8]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}
pub fn dispatch(buf: &[u8], payload: &[u8]) -> u32 {
    if buf.len() != 4 { return 0; }
    let a = u32_from_bytes(buf);
    if payload.len() >= 4 { a ^ u32_from_bytes(&payload[0..4]) } else { a }
}
"#;
    let r3_ok = verify_rust_functions_with_opts("p3_ok.rs", pat3_guarded, arch, cfg, opts);
    assert_eq!(r3_ok.failed.len(), 0, "pat3 guarded u32_from_bytes should be suppressed: {:?}", r3_ok.failed);
    assert_eq!(r3_ok.suppressed_guarded.len(), 1, "pat3 suppressed count: {:?}", r3_ok.suppressed_guarded);

    // Counterfactual assert_ne! knockout: removing `if buf.len() != 4` flips failed 0 -> >=1 with ENTRY-TRACE.
    let pat3_unguarded = r#"
pub fn u32_from_bytes(b: &[u8]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}
pub fn dispatch(_tag: &str, buf: &[u8]) -> u32 { u32_from_bytes(buf) }
"#;
    let r3_bad = verify_rust_functions_with_opts("p3_bad.rs", pat3_unguarded, arch, cfg, opts);
    assert_ne!(r3_ok.failed.len(), r3_bad.failed.len(), "knockout: removing guard must flip failure");
    assert_eq!(r3_bad.failed.len(), 1);
    assert_eq!(r3_bad.failed[0].entrypoint_trace, Some(vec!["dispatch".to_string(), "u32_from_bytes".to_string()]));

    let pat4 = r#"
pub fn first_err(errors: &[u32]) -> u32 { errors[0] }
pub fn parse_wrap(errors: &[u32]) -> u32 {
    if !errors.is_empty() { return first_err(errors); }
    0
}
"#;
    let r4 = verify_rust_functions_with_opts("p4.rs", pat4, arch, cfg, opts);
    assert_eq!(r4.failed.len(), 0, "pat4 !is_empty() guard should be suppressed: {:?}", r4.failed);
    assert_eq!(r4.suppressed_guarded.len(), 1, "pat4 suppressed count: {:?}", r4.suppressed_guarded);

    // 2. Zero-caller pub fn soundness: NEVER suppressed when no caller exists.
    let zero_caller = r#"
pub fn u32_from_bytes(b: &[u8]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}
"#;
    let r_zc = verify_rust_functions_with_opts("zc.rs", zero_caller, arch, cfg, opts);
    assert_eq!(r_zc.failed.len(), 1, "zero-caller pub fn must NOT be suppressed");
    assert_eq!(r_zc.failed[0].entrypoint_trace, Some(vec!["u32_from_bytes".to_string()]));

    // 3. Multi-hop unguarded trace + PoC `// call-chain:` prefix.
    let multi_hop = r#"
pub fn read_u32_be(b: &[u8]) -> u32 {
    ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32)
}
pub fn decode_header(_ctx: &str, pkt: &[u8]) -> u32 { read_u32_be(pkt) }
pub fn parse_packet(ctx: &str, raw: &[u8]) -> u32 { decode_header(ctx, raw) }
"#;
    let r_mh = verify_rust_functions_with_opts("mh.rs", multi_hop, arch, cfg, opts);
    assert_eq!(r_mh.failed.len(), 1);
    assert_eq!(
        r_mh.failed[0].entrypoint_trace,
        Some(vec!["parse_packet".to_string(), "decode_header".to_string(), "read_u32_be".to_string()])
    );
    let poc = r_mh.failed[0].poc_test.as_deref().unwrap_or("");
    assert!(poc.starts_with("// call-chain: parse_packet -> decode_header -> read_u32_be\n"), "missing call-chain prefix in PoC:\n{poc}");

    // 4. Standalone published library soundness: pub fn NOT suppressed by internal wrapper; pub(crate) fn IS suppressed.
    let tmp = std::env::temp_dir().join(format!("zc_standalone_lib_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(tmp.join("src")).expect("mkdir");
    std::fs::write(tmp.join("Cargo.toml"), "[package]\nname = \"demo_pub_lib\"\nversion = \"0.1.0\"\nedition = \"2021\"\n").expect("write toml");
    std::fs::write(
        tmp.join("src/lib.rs"),
        r#"
pub fn pub_u32(b: &[u8]) -> u32 { ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32) }
pub(crate) fn crate_u32(b: &[u8]) -> u32 { ((b[0] as u32) << 24) | ((b[1] as u32) << 16) | ((b[2] as u32) << 8) | (b[3] as u32) }
pub fn internal_caller(buf: &[u8]) -> u32 {
    if buf.len() != 4 { return 0; }
    pub_u32(buf) ^ crate_u32(buf)
}
"#,
    ).expect("write lib.rs");
    let reps = zero_check::verify_crate_functions_with_opts(&tmp.join("src"), arch, cfg, &[], opts).expect("verify crate");
    let _ = std::fs::remove_dir_all(&tmp);
    assert_eq!(reps.len(), 1);
    assert_eq!(reps[0].failed.len(), 1, "standalone lib pub fn must NOT be suppressed: {:?}", reps[0].failed);
    assert_eq!(reps[0].failed[0].fn_name, "pub_u32");
    assert_eq!(reps[0].suppressed_guarded.len(), 1, "standalone lib pub(crate) fn MUST be suppressed: {:?}", reps[0].suppressed_guarded);
    assert_eq!(reps[0].suppressed_guarded[0].fn_name, "crate_u32");
}
