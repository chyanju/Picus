# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

Older entries (v1.8.22 and earlier) are archived in [docs/changelogs/CHANGELOG-1.8.22-and-earlier.md](docs/changelogs/CHANGELOG-1.8.22-and-earlier.md).

## [Unreleased]
- Refactor: `picus_smt::poly_ir::PolyIR` slimmed to a use-agnostic GF(p) constraint system; the uniqueness overlay (two-copy layout, `n_wires`/`input_indices`/`known_signals`/`target_signal`, wire methods, R1CS lowering, `LowerError`) moves to new `picus_analysis::uniqueness::{UniquenessQuery, r1cs_to_uniqueness_query}`; lemmas + DPVL take `&UniquenessQuery`. Verdicts unchanged.
- New: `picus::solve(&PolyIR, config) -> SolverResult` decides a caller-built constraint system directly (no R1CS/uniqueness layer); `PolyIR::new` + builder mutators; `picus` re-exports `PolyIR`/`FfPolyRing`/`PrimeField`/`IrPoly`/`SolverResult`.
- `cvc5_ff`/`cvc5_nia`/`z3_nia` emit the disequality from generic `PolyIR::disequalities` (was `target_signal`/`x_name`/`y_name`), matching `native_ff`.
- Test env var `PICUS_SKIP_PLDI_SMOKE` → `PICUS_TEST_SKIP_SMOKE`; picus-smt unit tests lower locally via `src/test_lowering.rs` (no picus-analysis dep), lowering/wire tests moved to `uniqueness_tests`.
