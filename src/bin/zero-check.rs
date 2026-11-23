#![forbid(unsafe_code)]

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use zero_check::{run_gauntlet, scan_crate_dir, AutopoieticLedger, Severity};

struct CliArgs {
    targets: Vec<PathBuf>,
    ledger_path: Option<PathBuf>,
    emit_json: bool,
    quiet: bool,
}

fn parse_args() -> Result<CliArgs, String> {
    let mut targets = Vec::new();
    let mut ledger_path = Some(env::temp_dir().join("zero_check_ledger.json"));
    let mut emit_json = false;
    let mut quiet = false;
    let mut it = env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--json" | "--ledger" => {
                let p = it.next().ok_or_else(|| format!("{arg} requires a file path"))?;
                ledger_path = Some(PathBuf::from(p));
            }
            "--no-ledger" => ledger_path = None,
            "--emit-json" => emit_json = true,
            "--quiet" | "-q" => quiet = true,
            "--help" | "-h" => return Err("usage: zero-check [--ledger <path>] [--no-ledger] [--emit-json] [--quiet] <dir1> [dir2 ...]".to_string()),
            other if other.starts_with('-') => return Err(format!("unknown flag: {other}")),
            path => targets.push(PathBuf::from(path)),
        }
    }
    if targets.is_empty() {
        return Err("usage: zero-check [--ledger <path>] [--no-ledger] [--emit-json] [--quiet] <dir1> [dir2 ...]".to_string());
    }
    Ok(CliArgs { targets, ledger_path, emit_json, quiet })
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(msg) => { eprintln!("{msg}"); return ExitCode::from(2); }
    };
    let t0 = Instant::now();
    let mut ledger = args.ledger_path.as_ref().map_or_else(AutopoieticLedger::default, |p| AutopoieticLedger::load_or_new(p));
    let mut crate_invariants = Vec::new();
    let mut crate_rows = Vec::new();
    let (mut total_files, mut total_lines, mut total_errors, mut total_warnings) = (0usize, 0usize, 0usize, 0usize);

    for dir in &args.targets {
        match scan_crate_dir(dir) {
            Ok(rep) => {
                let errs = rep.error_count();
                let warns = rep.warning_count();
                total_files += rep.files_scanned;
                total_lines += rep.lines_scanned;
                total_errors += errs;
                total_warnings += warns;
                let zero_unsafe = !rep.findings.iter().any(|f| f.severity == Severity::Error);
                if errs == 0 {
                    crate_invariants.push(format!(
                        "crate:{} files={} loc={} errors=0 zero_unsafe={zero_unsafe}",
                        dir.display(), rep.files_scanned, rep.lines_scanned
                    ));
                }
                crate_rows.push((dir.display().to_string(), rep.files_scanned, rep.lines_scanned, errs, warns, rep.elapsed_us, rep.findings));
            }
            Err(e) => { eprintln!("[ZERO-CHECK-ERR] {}: {e}", dir.display()); return ExitCode::from(1); }
        }
    }

    let gauntlet = run_gauntlet();
    let mut all_invariants = crate_invariants;
    all_invariants.extend(gauntlet.proven_invariants.clone());
    ledger.crates_verified = args.targets.len();
    ledger.files_scanned = total_files;
    ledger.lines_scanned = total_lines;
    ledger.lint_errors = total_errors;
    ledger.lint_warnings = total_warnings;
    ledger.gauntlet_passed = gauntlet.checks_passed;
    ledger.gauntlet_total = gauntlet.checks_total;
    ledger.absorb_invariants(all_invariants, gauntlet.learned_guards.clone());
    ledger.elapsed_us = t0.elapsed().as_micros() as u64;

    if let Some(ref lp) = args.ledger_path {
        if let Err(e) = ledger.save(lp) {
            eprintln!("[ZERO-CHECK-ERR] failed writing ledger: {e}");
            return ExitCode::from(1);
        }
    }
    ledger.elapsed_us = t0.elapsed().as_micros() as u64;
    let elapsed_ms = (ledger.elapsed_us as f64) / 1000.0;

    if args.emit_json {
        print!("{}", ledger.to_json());
    } else if !args.quiet {
        for (path, files, lines, errs, warns, us, findings) in &crate_rows {
            println!("[CRATE] {path}: {files} files, {lines} LOC, {errs} errors, {warns} warnings ({us} us)");
            for f in findings.iter().filter(|f| f.severity == Severity::Error) {
                eprintln!("  ERROR {}:{}:{} {:?}: {}", f.file, f.line, f.col, f.kind, f.snippet);
            }
        }
        for fail in &gauntlet.failures { eprintln!("  GAUNTLET-FAIL: {fail}"); }
        let lp_str = args.ledger_path.as_ref().map_or_else(|| "none".to_string(), |p| p.display().to_string());
        println!(
            "[ZERO-CHECK-V2] crates={} files={} loc={} errors={} warnings={} gauntlet={}/{} invariants={} guards={} epoch={} wall={:.3} ms ({} us) ledger={}",
            ledger.crates_verified, ledger.files_scanned, ledger.lines_scanned, ledger.lint_errors,
            ledger.lint_warnings, ledger.gauntlet_passed, ledger.gauntlet_total,
            ledger.proven_invariants.len(), ledger.learned_guards.len(), ledger.epochs,
            elapsed_ms, ledger.elapsed_us, lp_str
        );
    }

    if total_errors == 0 && gauntlet.is_clean() { ExitCode::SUCCESS } else { ExitCode::from(1) }
}
