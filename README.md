# zero-check

Zero-dependency, zero-spill Miri-class, ASan-class, and Kani-class autopoietic Rust safety verifier, raw `.rs` guarded-branch/call/arena semantic prover, NTF1 airlock prover, static linter, and CLI (`2,527` LOC across `src/`, ceiling `<= 2,550`, `#![forbid(unsafe_code)]`, `0` external crates).

## Architecture

- `src/lib.rs` (`132` LOC): Fail-closed facade plus CT-recursive `define_errors!`/`define_ops!` macros exporting `verify_program`, `verify_crate_dir`, `verify_rust_source`, `verify_kernel_rust_source`, `verify_kernel_rust_source_total`, `parse_rust_programs`, `verify_rust_functions`, `verify_crate_functions`, `verify_ntf1_source`, `verify_ntf1_file`, `prove_exhaustive`, `run_gauntlet`, and `AutopoieticLedger`.
- `src/rust_fe.rs` (`586` LOC): Zero-dependency recursive-descent Rust kernel parser and SSA lowerer parsing `pub fn`/`fn` items with scalar integer types (`i64`/`u64`/`u32`/`u16`/`u8`/`usize`), fixed-length array refs (`&[T; N]`/`&mut [T; N]`), `rustc`-compatible `/// @domain`, `/// @uninit`, and `/// @region` doc comments plus `#[zero_domain(...)]`/`#[zero_uninit]`/`#[zero_region(...)]` attributes, guarded `if`/`else`/`match` early-return lowering, bounded helper inlining with direct sub-slice alias checking (`&mut buf[a..b]` vs `&buf[c..d]`), exact Rust operator precedence, fail-closed negative `i64 -> usize` casts, wrapping ops, `assert!` bounds checks, and constant-bounded `for` loop unrolling (`<= 16` iterations) directly into `Program` IR for `verify_program`.
- `src/abstract_eval.rs` (`721` LOC):
  - **ASan-Class Shadow-Epoch Memory Prover:** Generation-tagged `AllocState { len, alive, init_mask, generation, all_init }` with guarded `Op::Alloc`, `Op::Free`, `Op::CheckGen`, `Op::Cmp`, and `Op::Select`, catching path-sensitive use-after-free, ABA stale-generation handles, double-free, and uninitialized reads statically and symbolically (`written_ec` E-class, `hi_init` for `slot >= 64`, and dynamic `may_init` tracking), plus dynamic `Store`-to-`Load` value forwarding (`bg_doms` + `exact_stores` strong/weak updates).
  - **Interval + Congruence + Quadratic Ring-Lifting Algebra (`Domain`):** Exact `i128` overflow-checked transfer functions with inward congruence tightening (`tighten`), congruence-preserving hull (`join`), disjoint parity splitting (`split_mod2`), path-sensitive guard narrowing (`GuardCtx`), fail-closed contradictory-domain validation, constant-preserving congruence arithmetic (`eval_add_sub`, `eval_mul`, `eval_div_rem`), and quadratic ring lifting (`(mk + r)^2 == r^2 (mod m * gcd(m + 2r, 2m))`).
  - **Miri-Class `noalias` & Pointer-Offset Wrap Guard (`Program::check_noalias`):** Rejects overlapping `&mut`/`&` and `&mut`/`&mut` slices across initial, sub-sliced, and dynamically grown `Op::Alloc` spans, plus `usize` offset+length wraparound.
  - **Pure-Only E-Graph Equivalence Pass:** Breaks interval dependency blowup (`(x + c) - x == c`, `x ^ x == 0`, `(x << s) >> s == x`, `(x * c) / c == x`, constant folding, distributive factoring) while excluding stateful memory ops from CSE.
  - **Dual-Arch Sethi-Ullman Zero-Spill Guard:** Uses Sethi-Ullman subtree register weights (`su[u]`) and consumer-readiness tie-breaking (`helps`) to enforce both `ArchProfile::X86_64Avx2` (`14` GPR / `16` YMM, 256-bit) and `ArchProfile::Aarch64Neon` (`28` GPR / `32` V-regs, 128-bit).
- `src/simd_fuzz.rs` (`362` LOC):
  - **Branchless 8-Lane SIMD Replay (`eval_lanes_x8`):** Tracks per-lane `AllocState` shadow epochs, path guards, and exact per-lane `(slot, i64)` write logs for concrete `Store`-to-`Load` value forwarding (including `slot >= 64`), catching UAF, double-free, uninitialized read, OOB, signed `i64` overflow, shift UB, and div/rem-by-zero (`i64::MIN / -1` included) with zero panics.
  - **Kani-Class Exhaustive Branch-and-Bound Prover (`prove_exhaustive`, `refine_and_fuzz`):** Combines guard-targeted comparison splitting, congruence-targeted parity splitting (`split_mod2`), and interval bisection (`split_mid`), discharging safe sub-boxes algebraically and emitting `ProofVerdict::ProvenTotal` or `ProofVerdict::Counterexample` with an exact parity-absorbing safe-subdomain coalescer.
- `src/lint_rs.rs` (`232` LOC):
  - Single-pass lifetime-safe Rust comment/string/raw-string/char masker (`mask_rust_source`) and linear scanner catching `unsafe`, `transmute`, raw-pointer provenance, `get_unchecked`, `assume_init*`/`set_len`/`uninitialized`, shift-width UB (bit-width aware so legal `u128 >> 64` has zero false positives), literal `/ 0` and `% 0`, dot/path `clamp(` calls, `#[allow(...)]` and `#[expect(...)]` lint-suppression attributes, unused `_var` stage-prop bindings, unfinished macros, panic calls (`--kernel-strict`), and non-ASCII bytes.
- `src/ntf1.rs` (`185` LOC) & `specs/zero_check.ntf1`:
  - Zero-SVO `NTF1` v1 parser, canonical emitter, and fail-closed verifier (`+t ->` forward morphisms, `-t <-` retro-causal fault traps, `0t ><` symmetric airlock fixed-points, `|>` pipelines, retro-causal `Fault.*` coverage, `0t` endpoint grounding, canonical round-trip idempotence, and 11-word English SVO prose-tax rejection including `#` comments).
- `src/gauntlet.rs` (`192` LOC):
  - Self-verifying 11-check Miri + ASan + Kani + AVX2/NEON + NTF1 + raw-`.rs` gauntlet (`run_gauntlet`, `build_quad_mod16_kernel`) and zero-dep `AutopoieticLedger` JSON persister accumulating proven invariants and learned guards across epochs.
- `src/bin/zero-check.rs` (`117` LOC):
  - Zero-dep CLI (`zero-check [--prove-fns] [--kernel-strict] [--require-totality] [--arch avx2|neon] [--ledger <path>] [--no-ledger] [--ntf1 <file>] [--emit-json] [--quiet] <target1> [target2 ...]`) scanning real crates and `.ntf1` specs + proving raw `.rs` kernel functions + running the 11-check gauntlet + persisting the autopoietic JSON ledger in `< 10 ms`.

## Verified Live Head-to-Head vs `rustc` and `cargo +nightly miri` (AMD Ryzen 9 3900X)

Reproduced live in `tests/blindcheck_test.rs` (`knockout_15_raw_rs_semantic_verifier_and_kernel_strict` and `knockout_16_live_miri_head_to_head_and_guarded_branches`) on standalone 0-dep `.rs` kernel modules:

### 1. Path-Sensitive Branch / Call / Arena Suite vs `cargo +nightly miri test`

Evaluated on a 4-bug kernel crate containing conditional use-after-free (`if cmd == 221 { zero_free(buf); } buf[0]`), conditional uninitialized read (`/// @uninit scratch` on odd `mode`), overlapping `&mut`/`&` region aliasing (`/// @region a: 1, 0` + `/// @region b: 1, 8` and `&mut buf[0..16]` vs `&buf[8..24]`), and inlined helper division-by-zero (`helper_div0` at `x == 4099` with `match`):

| Verifier | Exit Code (Buggy Crate) | Wall Time | Coverage & Findings Across Input Space |
| :--- | :---: | :---: | :--- |
| `cargo +nightly miri test --offline` (`cmd=0,1`, `mode=0`, `x=7`) | `0` (Missed `4 / 4`) | `1,688.9 ms` | Single concrete trace per test; blind to unexecuted branches |
| `zero-check --prove-fns --kernel-strict --require-totality` (Buggy) | `1` (**Caught `4 / 4`**) | **`1.91 ms` (`0.432 ms` core)** | `ce=[221]` UAF, `ce=[255]` Uninit, `NoAliasViolation`, `ce=[4099]` Div0 (`skipped=0`) |
| `zero-check --prove-fns --kernel-strict --require-totality` (Patched + early `return` guard) | `0` (**`ProvenSafe`**) | **`1.54 ms` (`0.408 ms` core)** | `proven=6 failed=0 skipped=0` across all branches, `match` arms, & inlined calls |

### 2. Hardware Register-Spill & Cast-Wraparound Suite vs `rustc -D warnings`

| Tool | Exit Code | Wall Time | Faults Caught on Raw `.rs` Source |
| :--- | :---: | :---: | :--- |
| `rustc --crate-type lib -D warnings` | `0` (Missed `4 / 4`) | `~90 ms` | `0 / 4` |
| `zero-check --prove-fns --kernel-strict` (`avx2`) | `1` (**Caught `4 / 4`**) | **`0.389 ms` (`389 us`)** | `ce=[777]` Div0, `ce=[255]` OOB, `ce=[-5]` negative `i64 as usize` wrap, `avx2` spill `21/14` GPRs |
| `zero-check --prove-fns --kernel-strict --arch neon` | `1` (**Caught `3 / 3`; proved NEON**) | **`0.494 ms` (`494 us`)** | Proves `20`-live-val kernel fits `aarch64` NEON (`21/28` GPR, `21/32` V-regs) while rejecting the `3` bugs |

## NTF1 Co-Evolution & Compile-Time Recursive Footprint

- **`NTF1` (Native Token-Morphism Format v1):** `specs/zero_check.ntf1` and `../zero-cc/specs/zero_cc.ntf1` lock the compiler-verifier contract using `+t ->` forward morphisms, `-t <-` retro-causal fault traps, `0t ><` symmetric airlock fixed-points, `|>` pipelines, and a zero-SVO English prose-tax lexer (`2.64 ms` cross-crate check).
- **Compile-Time Recursive Compression (`2,527` LOC total):** Declarative `define_ops!` (`[Id; 3]` arity traversal), `define_errors!`, and the `prog!` TT-muncher DSL in `src/gauntlet.rs` keep the entire verifier, raw-`.rs` SSA frontend, static linter, and CLI under `2,550` LOC with `0` `ripwire` clones and `0` lint findings.
- **Scope Boundary:** Proves all $2^{64}$ inputs symbolically on bounded-loop (`<= 16` trips), non-recursive (`depth <= 4` inlined), fixed-array/arena integer/boolean kernel functions (`skipped_non_kernel_fns` records general heap/async/trait glue cleanly unless `--require-totality` is set).

## Verification Commands

```bash
env -u RUSTFLAGS cargo test --release --offline -- --nocapture
env -u RUSTFLAGS cargo +nightly miri test --offline
env -u RUSTFLAGS cargo clippy --all-targets --offline -- -D warnings
ripwire --clones src
ripwire --lint --lint-ignore=naming src
target/release/zero-check --prove-fns --kernel-strict --ntf1 specs/zero_check.ntf1 src ../zero-cc/specs/zero_cc.ntf1 ../zero-cc/src ../zero-proxy/src/blindbind ../zero-proxy/src/xdp ../zero-rans/src
```

## License

Licensed under the Apache License, Version 2.0 ([LICENSE](LICENSE) and [NOTICE](NOTICE)).

Copyright 2026 Blind Labs (https://blindlabs.ai).
