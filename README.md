# zero-check

Zero-dependency, zero-spill Miri-class, ASan-class, and Kani-class autopoietic Rust safety verifier, NTF1 airlock prover, static linter, and CLI (`2,486` LOC across `src/`, `#![forbid(unsafe_code)]`, `0` external crates).

## Architecture

- `src/lib.rs` (`69` LOC): Fail-closed facade exporting `verify_program`, `verify_crate_dir`, `verify_rust_source`, `verify_ntf1_source`, `verify_ntf1_file`, `prove_exhaustive`, `run_gauntlet`, and `AutopoieticLedger`.
- `src/abstract_eval.rs` (`847` LOC):
  - **ASan-Class Shadow-Epoch Memory Prover:** Generation-tagged `AllocState { len, alive, init_mask, generation, all_init }` with `Op::Alloc`, `Op::Free`, and `Op::CheckGen`, catching use-after-free, ABA stale-generation handles, double-free, and uninitialized reads statically and symbolically (`written_ec` E-class, `hi_init` for `slot >= 64`, and dynamic `may_init` tracking), plus dynamic `Store`-to-`Load` value forwarding (`bg_doms` + `exact_stores` strong/weak updates).
  - **Interval + Congruence + Quadratic Ring-Lifting Algebra (`Domain`):** Exact `i128` overflow-checked transfer functions with inward congruence tightening (`tighten`), congruence-preserving hull (`join`), disjoint parity splitting (`split_mod2`), fail-closed contradictory-domain validation, constant-preserving congruence arithmetic (`eval_add_sub`, `eval_mul`, `eval_div_rem`), and quadratic ring lifting (`(mk + r)^2 == r^2 (mod m * gcd(m + 2r, 2m))`).
  - **Miri-Class `noalias` & Pointer-Offset Wrap Guard (`Program::check_noalias`):** Rejects overlapping `&mut`/`&` and `&mut`/`&mut` slices across initial and dynamically grown `Op::Alloc` spans, plus `usize` offset+length wraparound.
  - **Pure-Only E-Graph Equivalence Pass:** Breaks interval dependency blowup (`(x + c) - x == c`, `x ^ x == 0`, `(x << s) >> s == x`, `(x * c) / c == x`, constant folding, distributive factoring) while excluding stateful memory ops from CSE.
  - **Dual-Arch Sethi-Ullman Zero-Spill Guard:** Uses Sethi-Ullman subtree register weights (`su[u]`) and consumer-readiness tie-breaking (`helps`) to enforce both `ArchProfile::X86_64Avx2` (`14` GPR / `16` YMM, 256-bit) and `ArchProfile::Aarch64Neon` (`28` GPR / `32` V-regs, 128-bit).
- `src/simd_fuzz.rs` (`527` LOC):
  - **Branchless 8-Lane SIMD Replay (`eval_lanes_x8`):** Tracks per-lane `AllocState` shadow epochs and exact per-lane `(slot, i64)` write logs for concrete `Store`-to-`Load` value forwarding (including `slot >= 64`), catching UAF, double-free, uninitialized read, OOB, signed `i64` overflow, shift UB, and div/rem-by-zero (`i64::MIN / -1` included) with zero panics.
  - **Kani-Class Exhaustive Branch-and-Bound Prover (`prove_exhaustive`, `refine_and_fuzz`):** Combines congruence-targeted parity splitting (`split_mod2`) and interval bisection (`split_mid`), discharging safe sub-boxes algebraically and emitting `ProofVerdict::ProvenTotal` or `ProofVerdict::Counterexample` with an exact parity-absorbing safe-subdomain coalescer.
- `src/lint_rs.rs` (`301` LOC):
  - Single-pass lifetime-safe Rust comment/string/raw-string/char masker (`mask_rust_source`) and linear scanner catching `unsafe`, `transmute`, raw-pointer provenance, `get_unchecked`, `assume_init*`/`set_len`/`uninitialized`, shift-width UB (bit-width aware so legal `u128 >> 64` has zero false positives), literal `/ 0` and `% 0`, dot/path `clamp(` calls, `#[allow(...)]` and `#[expect(...)]` lint-suppression attributes, unused `_var` stage-prop bindings, unfinished macros, and non-ASCII bytes.
- `src/ntf1.rs` (`221` LOC) & `specs/zero_check.ntf1`:
  - Zero-SVO `NTF1` v1 parser, canonical emitter, and fail-closed verifier (`+t ->` forward morphisms, `-t <-` retro-causal fault traps, `0t ><` symmetric airlock fixed-points, `|>` pipelines, retro-causal `Fault.*` coverage, `0t` endpoint grounding, canonical round-trip idempotence, and 11-word English SVO prose-tax rejection including `#` comments).
- `src/gauntlet.rs` (`379` LOC):
  - Self-verifying 10-check Miri + ASan + Kani + AVX2/NEON + NTF1 gauntlet (`run_gauntlet`, `build_quad_mod16_kernel`) and zero-dep `AutopoieticLedger` JSON persister accumulating proven invariants and learned guards across epochs.
- `src/bin/zero-check.rs` (`142` LOC):
  - Zero-dep CLI (`zero-check [--ledger <path>] [--no-ledger] [--ntf1 <file>] [--emit-json] [--quiet] <target1> [target2 ...]`) scanning real crates and `.ntf1` specs + running the 10-check gauntlet + persisting the autopoietic JSON ledger in `< 10 ms`.

## Verification Commands

```bash
env -u RUSTFLAGS cargo test --release --offline -- --nocapture
env -u RUSTFLAGS cargo +nightly miri test --offline
env -u RUSTFLAGS cargo clippy --all-targets --offline -- -D warnings
ripwire --clones src
ripwire --lint --lint-ignore=naming src
target/release/zero-check --ntf1 specs/zero_check.ntf1 src ../zero-cc/specs/zero_cc.ntf1 ../zero-cc/src ../zero-proxy/src/blindbind ../zero-proxy/src/xdp ../zero-rans/src
```

## License

Licensed under the Apache License, Version 2.0 ([LICENSE](LICENSE) and [NOTICE](NOTICE)).

Copyright 2026 Blind Labs (https://blindlabs.ai).
