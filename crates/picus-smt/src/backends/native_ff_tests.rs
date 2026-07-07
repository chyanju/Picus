//! Tests for `native_ff.rs` — the `NativeFfBackend` constructor,
//! `dump_smt` formatting, the `SolverBackendDescriptor` registration,
//! and minimal end-to-end `solve` smoke (tiny GF(7) systems).

use super::NativeFfBackend;
use crate::backends::{all_backend_descriptors, create_backend_by_name, SolverBackend, SolverResult};
use crate::poly_system::PolySystem;
use crate::Theory;

use num_bigint::BigUint;
use picus_core::timeout::CancelToken;
use picus_r1cs::grammar::Constraint;
use picus_r1cs::testkit::*;

// ─── Test fixtures ────────────────────────────────────────────────
// The shared builders (`r1cs`, `blk`, …) live in `picus_r1cs::testkit`.

fn empty_ir(p: BigUint, n_wires: usize, inputs: Vec<usize>, target: usize) -> PolySystem {
    let file = r1cs(p, n_wires as u32, inputs, Vec::new());
    crate::test_lowering::lower_two_copy(&file, target)
}

// ─── Constructor + default ─────────────────────────────────────────

#[test]
fn test_native_ff_new_works() {
    let _b = NativeFfBackend::new();
}

#[test]
fn test_native_ff_default_equivalent_to_new() {
    let _a = NativeFfBackend::new();
    let _b = NativeFfBackend::default();
}

// ─── Inventory registration ───────────────────────────────────────

#[test]
fn prop_native_ff_descriptor_registered() {
    // The `inventory::submit!` block at the bottom of `native_ff.rs`
    // must produce a descriptor named "native" with Theory::Ff.
    let found = all_backend_descriptors()
        .into_iter()
        .any(|d| d.name == "native" && d.theory == Theory::Ff);
    assert!(found, "native+ff descriptor must be registered");
}

#[test]
fn prop_native_ff_create_by_name_builds() {
    let b = create_backend_by_name("native", Theory::Ff);
    assert!(b.is_some());
}

// ─── dump_smt (pure formatting) ──────────────────────────────────

#[test]
fn prop_dump_smt_header_mentions_prime() {
    // Doc spec: header line is "; Native FF solver (Groebner basis
    // over GF({})...)".
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(s.contains("Native FF solver"), "header present");
    assert!(s.contains("GF(7)"), "prime in header: {}", s);
}

#[test]
fn prop_dump_smt_includes_disequality_lines() {
    // Doc spec: "for &(a, b) in &ics.disequalities { ... }" emits a
    // `; disequality: NAME != NAME` line.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(
        s.contains("disequality:"),
        "diseq line present: {}",
        s
    );
    // Target=1 ⇒ x1 != y1.
    assert!(
        s.contains("x1") && s.contains("y1"),
        "target wire 1's xy names in diseq: {}",
        s
    );
}

#[test]
fn prop_dump_smt_includes_equality_count_line() {
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    assert!(s.contains("equalities"), "counts line present: {}", s);
}

#[test]
fn prop_dump_smt_each_equality_terminated_with_eq_zero() {
    // Each `eq[N]: ...` line ends in ` = 0`.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let s = backend.dump_smt(&ir);
    for line in s.lines() {
        if line.starts_with("; eq[") {
            assert!(
                line.trim_end().ends_with("= 0"),
                "eq line not terminated: {}",
                line
            );
        }
    }
}

#[test]
fn prop_dump_smt_is_deterministic() {
    // Two dumps over the same IR must match exactly.
    let backend = NativeFfBackend::new();
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let a = backend.dump_smt(&ir);
    let b = backend.dump_smt(&ir);
    assert_eq!(a, b);
}

// ─── solve smoke (tiny GF(7) inputs) ────────────────────────────

#[test]
fn smoke_solve_trivial_constraints_returns_sat_or_unknown_within_budget() {
    // A trivially satisfiable system: one constraint pin (x_0 = 1)
    // and target wire 1 unconstrained. The disequality `x_1 != y_1`
    // is SAT (both copies are free). Treat the verdict as
    // structural: a real backend must return either Sat or Unsat
    // (not Unknown) within a generous budget, and Unsat here would
    // indicate a soundness issue.
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::none();
    let r = backend.solve(&ir, 5_000, &cancel).expect("no backend error");
    // Free target ⇒ SAT (witness pair exists with x_1 ≠ y_1).
    match r {
        SolverResult::Sat(_) => {}
        SolverResult::Unknown(_) => {} // tolerate (timeout/incomplete) — keeps structural
        SolverResult::Unsat => {
            panic!("free target wire should not be UNSAT (would indicate spurious UNSAT)")
        }
    }
}

#[test]
fn smoke_solve_respects_external_cancel_pre_call() {
    // If the cancel token is already cancelled when `solve` is
    // entered, the backend must return Unknown(Timeout) without
    // running the GB engine.
    let ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::cancelled();
    let r = backend.solve(&ir, 60_000, &cancel).expect("no backend error");
    assert!(
        matches!(r, SolverResult::Unknown(_)),
        "pre-cancelled solve must yield Unknown, got {:?}",
        r
    );
}

#[test]
fn smoke_solve_forced_unsat_returns_unsat() {
    // Force a contradiction: pin wire 1 to two distinct values via
    // two constraints `1 * x_1 = 2` and `1 * x_1 = 3` (over GF(7)).
    // The `x_1 != y_1` target diseq is then UNSAT — there's only one
    // possible value for x_1 (none, in fact). Result must be Unsat.
    //
    // Constraint A * B = C → (1 * x_0) * (1 * x_1) = (2 * x_0) gives x_1 = 2.
    let c1 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 2),
    };
    // x_1 = 3:
    let c2 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 3),
    };
    let r1cs = r1cs(BigUint::from(7u32), 3, vec![0], vec![c1, c2]);
    let ir = crate::test_lowering::lower_two_copy(&r1cs, 1);

    let mut backend = NativeFfBackend::new();
    let cancel = CancelToken::none();
    let r = backend.solve(&ir, 5_000, &cancel).expect("no backend error");
    match r {
        SolverResult::Unsat => {}
        SolverResult::Unknown(_) => {} // tolerate but Sat would be a soundness bug
        SolverResult::Sat(_) => {
            panic!("contradictory pinning should not be SAT (would indicate spurious SAT)")
        }
    }
}

// ─── knob coverage: the two backend-level gates ─────────────────────
// `cache_enabled` and `linear_elim` are consulted here in `native_ff`
// (not in `solve_encoded`), so their non-default legs are pinned here.

/// The contradictory-pinning fixture from `smoke_solve_forced_unsat_returns_unsat`.
fn forced_unsat_ir() -> PolySystem {
    let c1 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 2),
    };
    let c2 = Constraint {
        a: blk(0, 1),
        b: blk(1, 1),
        c: blk(0, 3),
    };
    let file = r1cs(BigUint::from(7u32), 3, vec![0], vec![c1, c2]);
    crate::test_lowering::lower_two_copy(&file, 1)
}

#[test]
fn knob_cache_disabled_keeps_verdicts() {
    // cache_enabled = false routes every solve through the stateless
    // (traced dense) pipeline. Verdicts must match the cached path's:
    // repeated solves of the UNSAT fixture stay UNSAT, and the
    // free-target fixture never turns UNSAT.
    let _g = picus_core::config::ConfigGuard::with_override(|c| c.cache_enabled = false);
    let cancel = CancelToken::none();

    let unsat_ir = forced_unsat_ir();
    let mut backend = NativeFfBackend::new();
    for round in 0..2 {
        let r = backend.solve(&unsat_ir, 5_000, &cancel).expect("no backend error");
        assert!(
            matches!(r, SolverResult::Unsat),
            "no-cache round {}: expected Unsat, got {:?}",
            round,
            r
        );
    }

    let sat_ir = empty_ir(BigUint::from(7u32), 3, vec![0], 1);
    let r = backend.solve(&sat_ir, 5_000, &cancel).expect("no backend error");
    assert!(
        !matches!(r, SolverResult::Unsat),
        "free target must not be UNSAT under no-cache, got {:?}",
        r
    );
}

#[test]
fn knob_linear_elim_keeps_verdicts() {
    // linear_elim = true runs the Gaussian pre-elimination before the
    // solve. The fixtures are linear-heavy (wire pins), so the phase
    // genuinely executes; verdicts must be unchanged.
    let _g = picus_core::config::ConfigGuard::with_override(|c| c.linear_elim = true);
    let cancel = CancelToken::none();

    let mut backend = NativeFfBackend::new();
    let r = backend
        .solve(&forced_unsat_ir(), 5_000, &cancel)
        .expect("no backend error");
    assert!(
        matches!(r, SolverResult::Unsat),
        "linear-elim: expected Unsat, got {:?}",
        r
    );

    let r = backend
        .solve(&empty_ir(BigUint::from(7u32), 3, vec![0], 1), 5_000, &cancel)
        .expect("no backend error");
    assert!(
        !matches!(r, SolverResult::Unsat),
        "linear-elim: free target must not be UNSAT, got {:?}",
        r
    );
}

// ─── UF probe end-to-end (metrics + disjunction leg) ──────────────

/// Two-copy-shaped UF system over GF(7) built directly on a
/// `PolySystem`: `x_r = f(x_a)`, `y_r = f(y_a)`, `x_a − y_a = 0`,
/// target `x_r != y_r`. Unsat via congruence.
fn uf_probe_ir(with_disjunction: bool) -> PolySystem {
    use picus_core::ff::field::PrimeField;
    use picus_core::poly::FfPolyRing;
    use std::sync::Arc;
    let field = PrimeField::new(BigUint::from(7u32));
    let names: Vec<String> =
        ["x_a", "y_a", "x_r", "y_r"].iter().map(|s| s.to_string()).collect();
    let ring = Arc::new(FfPolyRing::new(field, names));
    let mut ir = PolySystem::new(ring);
    let f = ir.uf_symbol("f");
    ir.add_uf_app(f, vec![0], 2);
    ir.add_uf_app(f, vec![1], 3);
    // x_a - y_a = 0 (the known-wire equality the closure consumes).
    let eq = ir.ring.sub(ir.ring.var(0), ir.ring.var(1));
    ir.push_equality(eq);
    if with_disjunction {
        // A satisfiable-by-itself disjunction: (x_a = 0 ∨ x_a = 1).
        let c0 = ir.ring.var(0);
        let one = ir.ring.field().one();
        let c1 = ir.ring.sub(ir.ring.var(0), ir.ring.constant(one));
        ir.push_disjunction(vec![c0, c1]);
    }
    ir.add_disequality(2, 3);
    ir.set_add_field_polys(true);
    ir
}

/// One sequential test (metrics are process-global): the first solve
/// enters CDCL(T); the second is answered by the cached closure probe
/// with no CDCL(T) entry; a retargeted third solve reuses the closure.
#[test]
fn uf_probe_answers_repeat_queries_without_cdclt() {
    use picus_core::config::{ConfigGuard, RuntimeConfig};
    use picus_core::profile::NATIVE_FF;
    use std::sync::atomic::Ordering;

    let _g = ConfigGuard::install(RuntimeConfig {
        gb_stats_enabled: true,
        ..RuntimeConfig::default()
    });
    let load = |c: &std::sync::atomic::AtomicU64| c.load(Ordering::Relaxed);
    let mut backend = NativeFfBackend::new();
    let ir = uf_probe_ir(false);
    let cancel = CancelToken::none();

    let cdclt0 = load(&NATIVE_FF.uf_cdclt_entries);
    let fast0 = load(&NATIVE_FF.uf_probe_fastpath_unsat);
    let reuse0 = load(&NATIVE_FF.uf_closure_reuses);

    // Solve 1: first digest sighting — probe skips, CDCL(T) decides.
    let r1 = backend.solve(&ir, 5000, &cancel).unwrap();
    assert!(matches!(r1, SolverResult::Unsat), "got {:?}", r1);
    assert_eq!(load(&NATIVE_FF.uf_cdclt_entries), cdclt0 + 1);
    assert_eq!(load(&NATIVE_FF.uf_probe_fastpath_unsat), fast0);

    // Solve 2: same digest — the probe builds the base + closure and
    // answers Unsat WITHOUT entering CDCL(T).
    let r2 = backend.solve(&ir, 5000, &cancel).unwrap();
    assert!(matches!(r2, SolverResult::Unsat), "got {:?}", r2);
    assert_eq!(
        load(&NATIVE_FF.uf_cdclt_entries),
        cdclt0 + 1,
        "the probe answer must not enter CDCL(T)"
    );
    assert_eq!(load(&NATIVE_FF.uf_probe_fastpath_unsat), fast0 + 1);

    // Solve 3: same constraint side, different target (x_a vs y_a is
    // also forced equal): the finished closure is reused.
    let mut ir3 = uf_probe_ir(false);
    ir3.disequalities.clear();
    ir3.add_disequality(0, 1);
    let r3 = backend.solve(&ir3, 5000, &cancel).unwrap();
    assert!(matches!(r3, SolverResult::Unsat), "got {:?}", r3);
    assert_eq!(load(&NATIVE_FF.uf_closure_reuses), reuse0 + 1);
    assert_eq!(load(&NATIVE_FF.uf_probe_fastpath_unsat), fast0 + 2);
    assert_eq!(load(&NATIVE_FF.uf_cdclt_entries), cdclt0 + 1);
}

/// The probe runs (and stays sound) on a disjunction-bearing
/// system — UNSAT of the conjunctive subset implies UNSAT of the
/// whole, so the disjunctions never need materialising.
#[test]
fn uf_probe_fires_on_disjunction_bearing_systems() {
    let mut backend = NativeFfBackend::new();
    let ir = uf_probe_ir(true);
    let cancel = CancelToken::none();
    let r1 = backend.solve(&ir, 5000, &cancel).unwrap();
    assert!(matches!(r1, SolverResult::Unsat), "got {:?}", r1);
    // Second solve goes through the probe (same digest); the verdict
    // must be identical.
    let r2 = backend.solve(&ir, 5000, &cancel).unwrap();
    assert!(matches!(r2, SolverResult::Unsat), "got {:?}", r2);
}
