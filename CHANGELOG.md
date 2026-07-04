# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

Older entries (v1.8.22 and earlier) are archived in [docs/changelogs/CHANGELOG-1.8.22-and-earlier.md](docs/changelogs/CHANGELOG-1.8.22-and-earlier.md).

## [1.8.24] - 2026-07-04
- API: `picus::PolyIR` (module `picus::ir`) is now the ergonomic public constraint-system builder over GF(p) — `Copy` `Var` handles + a ring-free symbolic `Expr` with `std::ops` operator overloading (`x*x - x`, `2*x + 3*y - 5`, `x.pow(3)`), constants via `Into`; `eq`/`ne`/`assert_zero`/`assert`/`assign`/`or`/`bitsum`/`field_polys`; `solve`/`solve_with` → `Solution { Unsat, Sat(Model), Unknown }` with `Model` indexable by handle (`m[x]`) or name (`m["x"]`). `Arc`/`FfPolyRing`/`Poly` hidden (lowered in `ir::lower`); solver unchanged. `ne` uses the native disequality primitive for bare-var pairs, else a Rabinowitsch witness.
- The former low-level `PolyIR` (ring + `Vec<Poly>`) is renamed `PolySystem` (module `picus_smt::poly_system`) and is no longer a top-level public builder; `PolyIR::lower()` is the power-user bridge and the internal `solve_system` decides it. Removed the top-level `picus::{solve, FfPolyRing, PrimeField, IrPoly}` re-exports; `solve_api` test replaced by `ir_api` + a runnable `PolyIR` doctest.

## [1.8.23] - 2026-07-04
- Refactor: `picus_smt::poly_ir::PolyIR` slimmed to a use-agnostic GF(p) constraint system; the uniqueness overlay (two-copy layout, `n_wires`/`input_indices`/`known_signals`/`target_signal`, wire methods, R1CS lowering, `LowerError`) moves to new `picus_analysis::uniqueness::{UniquenessQuery, r1cs_to_uniqueness_query}`; lemmas + DPVL take `&UniquenessQuery`. Verdicts unchanged.
- New: `picus::solve(&PolyIR, config) -> SolverResult` decides a caller-built constraint system directly (no R1CS/uniqueness layer); `PolyIR::new` + builder mutators; `picus` re-exports `PolyIR`/`FfPolyRing`/`PrimeField`/`IrPoly`/`SolverResult`. Documented in `docs/usage.md`.
- `cvc5_ff`/`cvc5_nia`/`z3_nia` emit the disequality from generic `PolyIR::disequalities` (was `target_signal`/`x_name`/`y_name`), matching `native_ff`.
- Test env var `PICUS_SKIP_PLDI_SMOKE` → `PICUS_TEST_SKIP_SMOKE`; picus-smt unit tests lower locally via `src/test_lowering.rs` (no picus-analysis dep), lowering/wire tests moved to `uniqueness_tests`.
- Maintainability: doc/inline comments across the workspace trimmed to pure-technical prose — removed benchmark anecdotes (PLDI A/B wall-clock deltas), changelog-style historical narration, and non-technical asides; soundness/algorithm rationale kept.
- Test: `picus-smt/tests/external_solve.rs` (feature-gated) — real cvc5/z3 backend solves over a GF(7) suite (SAT/model, UNSAT, and both disequality paths), verifying the `PolyIR::disequalities` backend change end to end.
