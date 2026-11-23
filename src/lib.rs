#![forbid(unsafe_code)]

macro_rules! define_errors {
    (@build $vis:vis $name:ident $f:ident [ $($vars:tt)* ] [ $($arms:tt)* ]) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        $vis enum $name { $($vars)* }
        impl std::fmt::Display for $name {
            fn fmt(&self, $f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { match self { $($arms)* } }
        }
        impl std::error::Error for $name {}
    };
    (@parse $vis:vis $name:ident $f:ident $v:tt $a:tt) => { $crate::define_errors!(@build $vis $name $f $v $a); };
    (@parse $vis:vis $name:ident $f:ident [$($v:tt)*] [$($a:tt)*] $var:ident ( $($tf:ident : $tt:ty),+ ) => ($fmt:expr $(, $arg:expr)*) $(, $($rest:tt)*)?) => {
        $crate::define_errors!(@parse $vis $name $f [$($v)* $var($($tt),+),] [$($a)* Self::$var($($tf),+) => write!($f, $fmt $(, $arg)*),] $($($rest)*)?);
    };
    (@parse $vis:vis $name:ident $f:ident [$($v:tt)*] [$($a:tt)*] $var:ident { $($sf:ident : $st:ty),+ } => ($fmt:expr $(, $arg:expr)*) $(, $($rest:tt)*)?) => {
        $crate::define_errors!(@parse $vis $name $f [$($v)* $var { $($sf : $st),+ },] [$($a)* Self::$var { $($sf),+ } => write!($f, $fmt $(, $arg)*),] $($($rest)*)?);
    };
    (@parse $vis:vis $name:ident $f:ident [$($v:tt)*] [$($a:tt)*] $var:ident => ($fmt:expr $(, $arg:expr)*) $(, $($rest:tt)*)?) => {
        $crate::define_errors!(@parse $vis $name $f [$($v)* $var,] [$($a)* Self::$var => write!($f, $fmt $(, $arg)*),] $($($rest)*)?);
    };
    ($vis:vis $name:ident { $($rest:tt)* }) => { $crate::define_errors!(@parse $vis $name f [] [] $($rest)*); };
}

macro_rules! define_ops {
    (@build $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*]) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum Op<Id> { $($v)* }
        impl<Id: Copy> Op<Id> {
            #[must_use] pub const fn is_pure(self) -> bool { !matches!(self, $($i)|*) }
            #[must_use] pub fn children(self) -> ([Id; 3], usize) where Id: Default {
                let $d = Id::default();
                match self { $($k)* }
            }
            pub fn map_ids<Out>(self, mut $f: impl FnMut(Id) -> Out) -> Op<Out> { match self { $($m)* } }
        }
    };
    (@parse $d:ident $f:ident $v:tt $i:tt $k:tt $m:tt) => { $crate::define_ops!(@build $d $f $v $i $k $m); };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @0 pure $n:ident($t:ty), $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n($t),] [$($i),*] [$($k)* Self::$n(_) => ([$d, $d, $d], 0),] [$($m)* Self::$n(x) => Op::$n(x),] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @0 eff $n:ident($t:ty), $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n($t),] [$($i,)* Self::$n(_)] [$($k)* Self::$n(_) => ([$d, $d, $d], 0),] [$($m)* Self::$n(x) => Op::$n(x),] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @0s eff $n:ident { $a:ident : $at:ty, $b:ident : $bt:ty }, $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n { $a: $at, $b: $bt },] [$($i,)* Self::$n { .. }] [$($k)* Self::$n { .. } => ([$d, $d, $d], 0),] [$($m)* Self::$n { $a, $b } => Op::$n { $a, $b },] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @1s eff $n:ident { $x:ident : $xt:ty, $id:ident : Id }, $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n { $x: $xt, $id: Id },] [$($i,)* Self::$n { .. }] [$($k)* Self::$n { $id, .. } => ([$id, $d, $d], 1),] [$($m)* Self::$n { $x, $id } => Op::$n { $x, $id: $f($id) },] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @1s pure $n:ident { $id:ident : Id, $x:ident : $xt:ty }, $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n { $id: Id, $x: $xt },] [$($i),*] [$($k)* Self::$n { $id, .. } => ([$id, $d, $d], 1),] [$($m)* Self::$n { $id, $x } => Op::$n { $id: $f($id), $x },] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @1t pure $n:ident(Id, $t:ty), $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n(Id, $t),] [$($i),*] [$($k)* Self::$n(a, _) => ([a, $d, $d], 1),] [$($m)* Self::$n(a, s) => Op::$n($f(a), s),] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @2 pure $n:ident(Id, Id), $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n(Id, Id),] [$($i),*] [$($k)* Self::$n(a, b) => ([a, b, $d], 2),] [$($m)* Self::$n(a, b) => Op::$n($f(a), $f(b)),] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @2k pure $n:ident($kty:ty, Id, Id), $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n($kty, Id, Id),] [$($i),*] [$($k)* Self::$n(_, a, b) => ([a, b, $d], 2),] [$($m)* Self::$n(k, a, b) => Op::$n(k, $f(a), $f(b)),] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @2s eff $n:ident { $x:ident : $xt:ty, $a:ident : Id, $b:ident : Id }, $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n { $x: $xt, $a: Id, $b: Id },] [$($i,)* Self::$n { .. }] [$($k)* Self::$n { $a, $b, .. } => ([$a, $b, $d], 2),] [$($m)* Self::$n { $x, $a, $b } => Op::$n { $x, $a: $f($a), $b: $f($b) },] $($r)*);
    };
    (@parse $d:ident $f:ident [$($v:tt)*] [$($i:pat),*] [$($k:tt)*] [$($m:tt)*] @3s pure $n:ident { $a:ident : Id, $b:ident : Id, $c:ident : Id }, $($r:tt)*) => {
        $crate::define_ops!(@parse $d $f [$($v)* $n { $a: Id, $b: Id, $c: Id },] [$($i),*] [$($k)* Self::$n { $a, $b, $c } => ([$a, $b, $c], 3),] [$($m)* Self::$n { $a, $b, $c } => Op::$n { $a: $f($a), $b: $f($b), $c: $f($c) },] $($r)*);
    };
    ($($r:tt)*) => { $crate::define_ops!(@parse d f [] [] [] [] $($r)*); };
}

pub(crate) use {define_errors, define_ops};

pub mod abstract_eval; pub mod gauntlet; pub mod lint_rs; pub mod ntf1; pub mod rust_fe; pub mod simd_fuzz;

use std::path::Path;
pub use abstract_eval::{AbstractReport, AllocState, ArchProfile, BufSpec, CmpKind, Domain, IrOp, NodeId, Op, Program, ProofStatus, RegBudget, ScheduleReport, VerifyError};
pub use gauntlet::{build_quad_mod16_kernel, run_gauntlet, AutopoieticLedger, GauntletSummary};
pub use lint_rs::{promote_kernel_strict, scan_crate_dir, scan_rust_source, LintFinding, LintKind, LintReport, Severity};
pub use ntf1::{check_svo_tax, emit_ntf1, parse_ntf1, verify_ntf1_file, verify_ntf1_source, Ntf1Doc, Ntf1Error, Ntf1Kind, Ntf1Report, Ntf1Stmt};
pub use rust_fe::{parse_rust_programs, verify_crate_functions, verify_rust_functions, ParsedRustUnit, RustFnFailure, RustProofReport};
pub use simd_fuzz::{eval_lanes_x8, fault_name, format_box_invariant, prove_exhaustive, refine_and_fuzz, sample_batch_x8, BatchEval, Counterexample, ProofVerdict, RefineConfig, RefineReport, FAULT_DIV0, FAULT_DOUBLE_FREE, FAULT_NONE, FAULT_OOB, FAULT_OVERFLOW, FAULT_SHIFT, FAULT_UAF, FAULT_UNINIT, LANES};

#[derive(Clone, Debug)]
pub struct ProgramReport { pub abstract_report: AbstractReport, pub refine_report: Option<RefineReport>, pub verdict: ProofVerdict }

/// Autodidactic verification: Miri `noalias` + ASan shadow-epoch + dual-arch AVX2/NEON spill + E-Graph + Kani branch-and-bound.
pub fn verify_program(prog: &Program, profile: ArchProfile, cfg: RefineConfig) -> Result<ProgramReport, VerifyError> {
    let abstract_report = prog.verify_abstract(profile)?;
    match &abstract_report.status {
        ProofStatus::ProvenSafe => {
            let inv = vec![format_box_invariant(&prog.param_domains, prog, &abstract_report.domains)];
            Ok(ProgramReport { abstract_report, refine_report: None, verdict: ProofVerdict::ProvenTotal { boxes_discharged: 1, learned_invariants: inv } })
        }
        ProofStatus::DefiniteBug(err) => Err(err.clone()),
        ProofStatus::Uncertain(err) => {
            let refine = refine_and_fuzz(prog, cfg);
            match &refine.verdict {
                ProofVerdict::Counterexample { input, node, fault, .. } => Err(VerifyError::CounterexampleFound { node: *node, fault: *fault, inputs: input.clone() }),
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

pub fn verify_crate_dir(dir: &Path) -> Result<LintReport, VerifyError> { require_clean(scan_crate_dir(dir)?) }
pub fn verify_rust_source(file: &str, src: &str) -> Result<LintReport, VerifyError> { require_clean(scan_rust_source(file, src)) }

/// Fail-closed kernel-strict Rust gate: promotes panic calls to hard errors and proves all kernel functions.
pub fn verify_kernel_rust_source(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> Result<(LintReport, RustProofReport), VerifyError> {
    let mut lint = scan_rust_source(file, src);
    promote_kernel_strict(&mut lint);
    let lint = require_clean(lint)?;
    let proofs = verify_rust_functions(file, src, profile, cfg);
    if let Some(first) = proofs.failed.first() { return Err(first.error.clone()); }
    Ok((lint, proofs))
}

/// Fail-closed kernel-strict + totality gate: also rejects any skipped non-kernel functions.
pub fn verify_kernel_rust_source_total(file: &str, src: &str, profile: ArchProfile, cfg: RefineConfig) -> Result<(LintReport, RustProofReport), VerifyError> {
    let (lint, proofs) = verify_kernel_rust_source(file, src, profile, cfg)?;
    if !proofs.skipped_non_kernel_fns.is_empty() { return Err(VerifyError::LintViolations { count: proofs.skipped_non_kernel_fns.len() }); }
    Ok((lint, proofs))
}
