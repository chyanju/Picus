# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

Older entries (v1.8.22 and earlier) are archived in [docs/changelogs/CHANGELOG-1.8.22-and-earlier.md](docs/changelogs/CHANGELOG-1.8.22-and-earlier.md).

## [Unreleased]

### Maintainability refactor (per `chat/plan2.md`)
- Refactor: removed the redundant `picus_core::poly::IrPoly` alias — it was a second public name for `Polynomial`, identical to `Poly`, and 11 of 13 use sites re-imported it as `IrPoly as Poly`. All sites now use `Poly`; also removes the `PolyIR`/`IrPoly` word-reversal collision. (T1)
- API: `check_circuit`/`check_r1cs_bytes` now take `PicusConfig` (matching `check_r1cs`/`solve_with`) instead of the `Config` alias, for one consistent config type in signatures; the `Config` alias stays exported (non-breaking). `CancelToken::none()` doc corrected to state it is an alias of `new()`/`default()`, not an uncancellable token. (T3)
- Refactor: dropped the never-constructed `R1csParseError::BadFieldSize` variant and the denormalized `ConstraintBlock.nnz` field (it always equalled `wire_ids.len()`); `constraint_to_string` now tests `wire_ids.is_empty()`. (T10)
- API: trimmed the `PolyIR` builder surface — removed `assert_zero` (fully subsumed by `assert`, no call sites); `fresh_var` and `SystemId` are now `pub(crate)` (internal-only; `SystemId` was unconstructable from outside anyway). (T16)
- Cleanup: removed dead `picus-core` API — `PrimeField::{characteristic, add_ref, sub_ref, add_assign_owned}` (zero callers; duplicates of `prime`/`add`/`sub`/`add_assign`) and `MatrixOrder::{from_rows, n_rows}` (zero callers); `MatrixOrder::{lex, is_admissible}` are now `#[cfg(test)]`. (T6)
- Docs: corrected the `metric` module doc (removed nonexistent `record_add`/`GbStatsLayer`; documented all 13 macros and the three distinct gating flags), fixed the `#[metric]`-under-gb-stats misfiling, and marked the 13 `__metric_*` `#[macro_export]` macros `#[doc(hidden)]`. (T5)
- Naming: renamed `tecomplete`'s private `type Mono = Vec<(usize,u16)>` to `ExpVec` so `Mono` unambiguously means `Monomial` workspace-wide; clarified `PolyRingType`'s solver-only doc. (T2, partial — core-alias removal deferred, needs picus-solver edits)
- API boundary: added `publish = false` to the internal substrate crates (`picus-core`/`picus-r1cs`/`picus-smt`/`picus-analysis`/`picus-solver`/`cvc5-ff`/`cvc5-ff-sys`/`picus-metric-macros`); replaced the facade's blanket `pub use picus_r1cs/picus_smt/picus_analysis/picus_solver` with a curated `picus::advanced` module (`parse_var_index`, `validate_combination`, `create_backend`, `SolverBackend`, `PolySystem`). `picus-cli` reach-throughs now go through `picus::advanced`. (T13)

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
