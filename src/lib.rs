#![forbid(unsafe_code)]

pub mod abstract_eval;
pub mod gauntlet;
pub mod lint_rs;
pub mod ntf1;
pub mod rust_fe;
pub mod simd_fuzz;

use std::path::Path;

pub use abstract_eval::{
    AbstractReport, AllocState, ArchProfile, BufSpec, Domain, IrOp, NodeId, Op, Program,
    ProofStatus, RegBudget, ScheduleReport, VerifyError,
};
pub use gauntlet::{build_quad_mod16_kernel, run_gauntlet, AutopoieticLedger, GauntletSummary};
pub use lint_rs::{
    promote_kernel_strict, scan_crate_dir, scan_rust_source, LintFinding, LintKind, LintReport,
    Severity,
};
pub use ntf1::{
    check_svo_tax, emit_ntf1, parse_ntf1, verify_ntf1_file, verify_ntf1_source, Ntf1Doc, Ntf1Error,
    Ntf1Kind, Ntf1Report, Ntf1Stmt,
};
pub use rust_fe::{
    parse_rust_programs, verify_crate_functions, verify_rust_functions, ParsedRustUnit,
    RustFnFailure, RustProofReport,
};
pub use simd_fuzz::{
    eval_lanes_x8, fault_name, format_box_invariant, prove_exhaustive, refine_and_fuzz,
    sample_batch_x8, BatchEval, Counterexample, ProofVerdict, RefineConfig, RefineReport,
    FAULT_DIV0, FAULT_DOUBLE_FREE, FAULT_NONE, FAULT_OOB, FAULT_OVERFLOW, FAULT_SHIFT, FAULT_UAF,
    FAULT_UNINIT, LANES,
};

#[derive(Clone, Debug)]
pub struct ProgramReport {
    pub abstract_report: AbstractReport,
    pub refine_report: Option<RefineReport>,
    pub verdict: ProofVerdict,
}

/// Autodidactic verification: Miri `noalias` + ASan shadow-epoch + dual-arch AVX2/NEON spill + E-Graph + Kani branch-and-bound.
pub fn verify_program(prog: &Program, profile: ArchProfile, cfg: RefineConfig) -> Result<ProgramReport, VerifyError> {
    let abstract_report = prog.verify_abstract(profile)?;
    match &abstract_report.status {
        ProofStatus::ProvenSafe => {
            let inv = vec![format_box_invariant(&prog.param_domains, prog, &abstract_report.domains)];
            let verdict = ProofVerdict::ProvenTotal { boxes_discharged: 1, learned_invariants: inv };
            Ok(ProgramReport { abstract_report, refine_report: None, verdict })
        }
        ProofStatus::DefiniteBug(err) => Err(err.clone()),
        ProofStatus::Uncertain(err) => {
            let refine = refine_and_fuzz(prog, cfg);
            match &refine.verdict {
                ProofVerdict::Counterexample { input, node, fault, .. } => {
                    Err(VerifyError::CounterexampleFound { node: *node, fault: *fault, inputs: input.clone() })
                }
                ProofVerdict::ProvenTotal { .. } => {
                    let verdict = refine.verdict.clone();
                    Ok(ProgramReport { abstract_report, refine_report: Some(refine), verdict })
                }
                ProofVerdict::Incomplete { .. } => Err(err.clone()),
            }
        }
    }
}

fn require_clean(report: LintReport) -> Result<LintReport, VerifyError> {
    if report.is_clean() { Ok(report) } else { Err(VerifyError::LintViolations { count: report.error_count() }) }
}

/// Fail-closed static Rust lint gate over a crate directory.
pub fn verify_crate_dir(dir: &Path) -> Result<LintReport, VerifyError> { require_clean(scan_crate_dir(dir)?) }

/// Fail-closed static Rust lint gate over an in-memory Rust source file.
pub fn verify_rust_source(file: &str, src: &str) -> Result<LintReport, VerifyError> { require_clean(scan_rust_source(file, src)) }

/// Fail-closed kernel-strict Rust gate: promotes panic calls to hard errors and proves all kernel functions.
pub fn verify_kernel_rust_source(
    file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig,
) -> Result<(LintReport, RustProofReport), VerifyError> {
    let mut lint = scan_rust_source(file, src);
    promote_kernel_strict(&mut lint);
    let lint = require_clean(lint)?;
    let proofs = verify_rust_functions(file, src, profile, cfg);
    if let Some(first) = proofs.failed.first() { return Err(first.error.clone()); }
    Ok((lint, proofs))
}
