# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

Older entries (v1.8.22 and earlier) are archived in [docs/changelogs/CHANGELOG-1.8.22-and-earlier.md](docs/changelogs/CHANGELOG-1.8.22-and-earlier.md).

## [Unreleased]

### API
- `PolyIR::check_uniqueness` returns a scoped `UniquenessError` (`Config` | `Analysis`) instead of the broad `PicusError`.
- `CheckResult::Unknown` / `DpvlResult::Unknown` carry a `DpvlUnknown` reason (`Timeout` | `BackendError` | `Exhausted`); the CLI surfaces it.
- Removed the never-constructed `PicusError::Solver` variant.
- Shared cvc5/z3 backend helpers are `pub(crate)`; `build_poly_cvc5` no longer leaks `cvc5-ff` types onto picus-smt's public surface.

### Naming
- Unified the wire vocabulary in picus-analysis: `UniquenessQuery.{known_signals,target_signal,input_indices}` → `{known_wires,target_wire,input_wires}`; DPVL `sid` and selector "signal" → "wire". The 0..2n ring `var` domain is unchanged.
- `RangeValue::Bottom` → `Unconstrained` (was documented as the lattice top).
- Generated engine overlay `EngineOverlay` → `RuntimeOverlay` (stem-symmetric with `RuntimeConfig`); facade re-exports it as `EngineOverlay`.

### Extensibility
- Signal selectors register via `inventory` (`SelectorDescriptor`); `--selector` is validated against the registry — no `SelectorKind` enum or hardcoded CLI list. `DpvlConfig.selector` is a name `String`.
- `GbStrategy`/`ReprKind` gained `FromStr`; the CLI parses via it instead of inline matches that silently defaulted on bad input.
- `Theory` derives `Ord` (dropped the sort-only `theory_key`); `--theory` / `--lemmas` valid-name lists are derived from the enum/registry, not hand-maintained.

### Structure
- Dropped the inert `native` Cargo feature (the native FF engine is always compiled; cvc5/z3 stay opt-in).
- Removed the phantom `picus` → `picus-solver` and `picus-smt` → `picus-r1cs` dependency edges (picus-r1cs is dev-only in picus-smt).
- Moved the analysis knob `aboz_emit_disjunctions` from the engine config into `DpvlConfig`, threaded via a new `PropagationLemma::configure` hook instead of an ambient thread-local; the TOML key moves `[engine]` → `[analysis]`.

## [1.8.26] - 2026-07-05

### API
- `PolyIR::check_uniqueness(inputs, outputs, known, cfg)`: DPVL uniqueness analysis (two-copy lowering + propagation) from the IR, no R1CS round-trip; witnesses keyed by variable name.
- `uniqueness::polysystem_to_uniqueness_query`: doubles a single-copy `PolySystem` into a two-copy `UniquenessQuery`; `r1cs_to_uniqueness_query` wraps it.
- `dpvl::run_dpvl_on_query`: run DPVL on a pre-built `UniquenessQuery`; `run_dpvl` wraps it.
- `UniquenessQuery.base_disequalities`: source disequalities preserved across `set_target`.

## [1.8.25] - 2026-07-05

Workspace-wide maintainability refactor. No verdict or behaviour changes.

### API
- Removed the redundant `poly::IrPoly` alias (identical to `Poly`); all sites use `Poly`.
- `PolyIR`: removed `assert_zero` (subsumed by `assert`); `fresh_var` and `SystemId` are now `pub(crate)`.
- `check_circuit`/`check_r1cs_bytes` take `PicusConfig` (was the `Config` alias, still exported).
- `publish = false` on the internal crates; replaced the facade's blanket sub-crate `pub use` with a curated `picus::advanced` (`parse_var_index`, `validate_combination`, `create_backend`, `SolverBackend`, `PolySystem`).
- Errors: removed the dead `SolverError::Unsupported`; narrowed `IrError::Solver` to a new `picus::SolveError`; re-exported `SolverError`.
- Added `Theory::as_str`/`Theory::smtlib_name`; the CLI solver/theory header is derived from the enums.

### Cleanup
- Removed dead `PrimeField::{characteristic, add_ref, sub_ref, add_assign_owned}` and `MatrixOrder::{from_rows, n_rows}`; gated `MatrixOrder::{lex, is_admissible}` behind `#[cfg(test)]`.
- Removed the never-constructed `R1csParseError::BadFieldSize` and the denormalized `ConstraintBlock.nnz` field.
- Removed the redundant `field_reduce` double-reduction (and the dead `prime` param) in the R1CS lowering; removed the test-only `bn128_prime()` public fn (now `testkit::bn128()`).
- Renamed `tecomplete`'s private `Mono` to `ExpVec` (frees `Mono` = `Monomial`).
- Corrected the `metric` module docs and `#[doc(hidden)]`'d the 13 `__metric_*` macros.

### Deduplication
- `propagation::shape::linear_form`: one linear-combination parser, replacing 6 hand-rolled copies.
- `PropagationCtx::mark_known`, `LenGatedCache<T>`, and shared `all_bits_binary`/`decomp_is_faithful`; `legendre` moved onto `PrimeField`; `SelectorState` fields private.
- Single-sourced lemma names (dropped `PropagationLemma::name()`; the driver uses `LemmaDescriptor.name`).
- Shared the geobucket `capacity`/`fitting_bucket` in `geobucket_params`.
- cvc5/z3 backends: shared `dump_smt_nia`, `preflight`, `resolve_disequalities`, `build_poly_cvc5`.
- cvc5-ff: `ffi_util` (`cstr_to_string`/`cstr_to_str`, `collect_raw_array`); dropped 10 redundant `copy()` methods.
- `atomic_counters!` and `runtime_config!` macros: the counter structs and the 28 engine knobs are each declared once; `on_off` helper for the CLI tri-state flags.

### Structure
- Split `picus-cli/main.rs` into `args`/`output`/`commands`; split `picus-core/profile.rs` into `profile/{counters,metric,phase}` (behind re-exports).
- Broke the `picus-smt → picus-analysis` dev-dependency cycle; added the feature-gated `picus_r1cs::testkit` fixtures (removed 21 duplicated helpers).

### Fixes
- cvc5-ff: `Statistics`/`Stat` now carry a `'tm` lifetime tying them to their owner, fixing a latent use-after-free.
- `run_dpvl` counts backend hard errors and warns when an `Unknown` verdict stems from a systematically-failing solver.

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
