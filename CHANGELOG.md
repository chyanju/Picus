# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

Older entries (v1.8.22 and earlier) are archived in [docs/changelogs/CHANGELOG-1.8.22-and-earlier.md](docs/changelogs/CHANGELOG-1.8.22-and-earlier.md).

## [1.8.29] - 2026-07-06

picus-solver second architecture pass. Verdict-preserving; native + cvc5/z3 suites green.

### Fixed
- `split_triangular` triangular DFS verifies the full assignment at the leaf (a stray root sequence could surface as a model / be replayed as an exhaustive candidate set → wrong UNSAT).
- `find_zero` re-verifies extracted assignments against the inputs; a failing point rejects the node and exhaustion degrades to Unknown (a corrupted node basis is no longer trusted for UNSAT).
- The cdclt incremental theory re-verifies the facade-ring model before forwarding Sat; the multi-prime model join degrades to Unknown on a cross-slot name collision instead of last-writer-wins.
- Equality-engine polarity migration across a union is trailed (with its witness), so it cannot survive a pop below its decision level.
- `timeout_ms` bounds the `linear_elim` pre-elimination phase (it ran on a never-firing token); the backend panic guard covers it too.
- The incremental cache fingerprints the basis-shaping knobs (`poly_repr`, `gb_strategy`, `use_f4`, `dynamic_order`, `matrix_elim_order`); a digest hit after a config flip rebuilds instead of serving a torn config.
- Cached-base builds scan `bitsum_polys` into BitProp (bitsum-derived propagation was silently absent on every cache-backed solve).
- SMT-LIB tokenizer: string literals are one atom (`""` escape honoured); unterminated `"` / `|` are parse errors instead of silent absorption to EOF.

### Diagnostics
- `SolveOutcome::Unknown(UnknownCause)` threads the cause (cancelled / iter cap / dnf cap / bounded search / degraded theory / engine failure / encoding failure / model validation) to the backend seam; only token-fired cases map to `UnknownReason::Timeout` (caps → IncompleteTheory, defects → BackendError with the message).
- Encoder rejections are logged with their message and counted (previously silent "timeouts"); cap hits get gb-stats debug lines + counters; SAT fail-closed give-ups log at error with the broken invariant named; incremental-theory degradations log with the `EngineError` preserved.
- The caught-panic net in the native backend keeps the payload, logs at error, and counts (`backend_panics`); gb-stats dump gains `[ideal]` and `[unknown-causes]` lines; CLI default log filter raised `error` → `warn`.

### Config
- Panel text corrected to the wiring: the dense-engine knob group's real liveness (stateless/traced solves consult it under the default sparse repr), `cache_enabled`'s engine-routing coupling, the `cdclt_*` trio's disjunction-query engagement on the R1CS path, landed incremental-theory model extraction, and the GB core's DegRevLex request on elimination-order rings.
- usage.md gains the five wired-but-undocumented flags (`membership-fastpath`, `radical-membership`, `matrix-elim-order`, `dynamic-order`, `zech-log-small-fp`).
- Every boolean CLI knob flag overrides in both directions (`--use-f4 [on|off]` etc.; new `--cache`/`--aboz-disj`; `--no-cache`/`--no-aboz-disj` stay as off shorthands).
- `run_smt2`/`cvc5_compare` `--config` accepts the `[engine]`-table panel form as well as the flat overlay.
- No knob was removed, renamed, or re-defaulted.

### Structure
- The GF(p) algebra is spelled `crate::ff` outside `engine/`; `use crate::engine` marks a genuine kernel dependency (four consumers).
- Bit/linear recognizers move to a crate-root `bits` module shared by the encoder and split-GB sides; picus-smt imports through the root facade (now load-bearing); the unused `solve as core` alias is removed.
- GB dispatch is one choke point: representation routing lives inside the `GbAlgorithm` impls; the trait gains `supports_incremental`/`extend_incremental` opt-in; telemetry records the route actually executed.
- `solve_order()` owns the GB core's term-order request (DegRevLex today); computing under an encoder-pinned elimination order instead stays gated on an EdDSA-class benchmark A/B.
- One owner each for: the small-prime field-poly policy (`ff::field::small_prime_field_polys`, five sites), the smt2 literal-prime inference, and the Bool `b·b = b` emission; `ReprKind` routing is exhaustive; matrix-order interning dedups structurally equal orders; `IncrementalIdeal` wraps the incremental engine in `Poly` vocabulary (adopted by the cdclt incremental theory).
- `Theory` gains a defaulted `early_check` hook (all shipped impls keep the default).

### Performance (result-identical, knob-neutral; perf corpus spot-check flat)
- Sparse reductions borrow same-arm divisors (no per-call deep clone of the divisor basis); GB routes move owned generators into the sparse engine; dense reduction gains by-value entries for owning callers; univariate mul/div_rem accumulate in place; `min_poly` probes coefficients natively per arm; dense interreduce precomputes LTs; Frobenius cache hits skip the vector clone; `bit_sums` indexes by coefficient above 32 entries.
- Hilbert numerator: budgeted explicit worklist (BCR recursion could run unbounded inside a deadline; callers decline soundly); sparse interreduce and BitProp bit-membership proofs are cancel-aware inside elements.

### Tests
- New `knob_grid_soundness` harness: exhaustive-enumeration ground truth (GF(7)/GF(17), 42 systems) × 22 configs covering every solve-core knob's non-default value; verdict must match or be Unknown, models re-evaluated, anti-vacuity floors.
- Three knob parity tests actually flip their knob off now; `cache_enabled=false` / `linear_elim=true` get backend-level coverage; always-run scaled-down F4 LT-parity covers `f4_hilbert_select=off` / `f4_sparse_reducer_cache=off`; BN254 bitsum probe gains an always-run 8-bit sibling; engine-parity suites gain decided-baseline floors.

## [1.8.28] - 2026-07-06

picus-solver architecture pass. Verdict-preserving; native + cvc5/z3 suites green.

### Fixed
- F4 + `f4_hilbert_select`: batch generators were labelled `lowest_sugar` instead of the drained `chosen_sugar` (debug: assert → Unknown; release: corrupted S-pair queue order).
- The cdclt incremental theory runs its inner GB engine under the solve deadline's cancel token; an extend error degrades to Unknown instead of being swallowed with a desynced trail.
- `sat::add_theory_lemma_with_trail` enforces its all-literals-False precondition (fail closed to `give_up`, never wrong root UNSAT / corrupted 1-UIP).
- Resumable partial builds: non-timeout engine errors, fixpoint-cap exhaustion, and repeated stalled resumes drop the partial (stateless fallback) instead of pinning the digest to permanent Unknown.

### API (picus-solver internal seam)
- `SolveOutcome::Unsat(Option<UnsatCore>)`: fabricated index-frame cores are gone (`None` = proved without an attributable core); the index frame is documented on the type. CDCL(T) maps `None` to the full asserted-fact set, never Unknown.
- `CheckOutcome::Sat(model)`: the theory hands its model with the verdict; `collect_model` and the per-impl `has_model`/`last_model` bookkeeping removed.
- GB entry points return `GbOutcome { Basis | Cancelled | Failed }` instead of a tri-state `Vec<Poly>` sentinel; the defensive generator backup-clone per GB call is deleted.
- Encoding errors are typed (`EngineError::Encoding`) end to end; caught engine panics keep site + payload (`EngineError::EnginePanic`); `EngineError` documents the `panic = "unwind"` assumption.

### Structure
- Public surface shrunk to the measured seam: `engine` (ex-`ff`) and `split_gb` are `pub(crate)`; cdclt exposes only `solve_formula`; a curated `lib.rs` facade re-exports what picus-smt consumes; `#![warn(unreachable_pub)]` enforces the boundary (~320 items downgraded).
- `core` → `solve` (alias kept); `ff` → `engine`; `gb_homog` → `homog`; the Boolean layer splits into `frontend::formula` (IR) / `dnf` (strategy) / `boolean` (router + shims), removing the `boolean ↔ cdclt` cycle; `bitprop` moves into `split_gb`; the push/pop rebuild harness moves to `push_pop` as `RebuildOnCheckSolver`.
- One fixpoint body (`run_fixpoint_impl`) drives the traced and untraced split-GB drivers; candidates scanned by reference in all three drivers (no per-iteration basis deep-clone); `route_query_polys` gives the partition layout a single owner.
- One `integrate_new_element` for the dense engine's four integration sites; the F4 fallback honours `reducer_index_cache`; one `Solver::handle_conflict` step drives both CDCL loops.

### Removed
- The production-unreachable single-GB solver mode (`solve_single_gb`, the `gb` root API, `track_inter_reduce_deps` knob + tracer inter-reduce hooks).
- The GVW signature path (`signature_criterion` knob, `gvw.rs`, `signature.rs`; its activating dispatch had zero test coverage).
- The legacy SMT2 conjunctive pipeline (`parse`/`handle_assert`/`build_poly`) — one operator table (`parse_boolean`) remains; multi-prime (`parse_boolean_multi`/`solve_formula_multi`) is explicitly parked (`#[doc(hidden)]`).
- Never-read `BuchbergerConfig.order`/`GBasis.order`; phantom `rug`/`num-integer`/`env_logger` manifest deps.

### Config
- `BuchbergerConfig` snapshots all engine knobs at construction (no mid-run thread-local reads); GB dispatch routes by the repr recorded on the ring (`new_with_repr` honoured); `incremental_engine()` owns the incremental policy (`use_f4` off) for all consumers; one `TheoryChoice` resolution warns on shadowed cdclt knobs; the four dense-engine-only knobs are documented as such (CLI stub labels fixed).

### Tests
- New oracles: engine-matrix parity (router/EE/F4 strict; incremental soundness-modulo-Unknown), 250-case brute-force SAT differential, UNSAT-core re-solve battery + S-pair-derived traced core.
- One fixture DSL (`testkit` feature, `picus_r1cs::testkit` pattern); the two different ideals both named `katsura_n` are now `katsura_faugere` / `katsura_reduced_vars`; test files converge on `x_tests` / `x_tests_<topic>`.

### Diagnostics
- `[picus-gb-stats]` / fixpoint-trace dumps emit via `log` targets `picus::gb_stats` / `picus::gb_trace` (CLI defaults them on; embedders can redirect); split_gb speaks one "partition" vocabulary and the split-GB citation is corrected to CAV 2024; rustdoc intra-doc links at zero warnings; `run_smt2`/`cvc5_compare` accept `--config <knobs.toml>`.

## [1.8.27] - 2026-07-05

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
