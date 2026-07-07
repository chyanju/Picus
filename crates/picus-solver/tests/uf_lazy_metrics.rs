//! Lifecycle effectiveness of the lazy pipeline, metric-asserted
//! (own integration binary: the counters are process-global statics).

use num_bigint::BigUint;
use picus_core::config::{ConfigGuard, RuntimeConfig};
use picus_core::profile::NATIVE_FF;
use picus_core::timeout::CancelToken;
use picus_solver::{ConstraintSystemBuilder, IncrementalSolverContext, PolyTerm, SolveOutcome};
use std::sync::atomic::Ordering;

fn load(c: &std::sync::atomic::AtomicU64) -> u64 {
    c.load(Ordering::Relaxed)
}

/// One sequential test (shared statics): both cross-copy refutation
/// scenarios decide UNSAT with zero GB post_check builds.
#[test]
fn lazy_refutes_cross_copy_scenarios_without_gb_work() {
    let _g = ConfigGuard::install(RuntimeConfig {
        gb_stats_enabled: true,
        ..RuntimeConfig::default()
    });
    let cancel = CancelToken::none();

    // Scenario A (shared input): x_r = f(x_in), y_r = f(x_in), target
    // x_r != y_r. The setup closure unit-asserts (x_r = y_r); the
    // formula asserts its negation — root Unsat by BCP: zero
    // decisions, zero GB calls, not even a hub conflict.
    let post0 = load(&NATIVE_FF.cdclt_post_checks);
    let hub0 = load(&NATIVE_FF.uf_hub_early_conflicts);
    {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x_in = b.var("x_in");
        let x_r = b.var("x_r");
        let y_r = b.var("y_r");
        let f = b.uf_symbol("f");
        b.add_uf_app(f, vec![x_in], x_r);
        b.add_uf_app(f, vec![x_in], y_r);
        b.add_disequality(x_r, y_r);
        b.set_add_field_polys(true);
        let out = IncrementalSolverContext::new().solve(&b.build(), &cancel);
        assert!(matches!(out, SolveOutcome::Unsat(_)), "got {:?}", out);
    }
    assert_eq!(
        load(&NATIVE_FF.cdclt_post_checks),
        post0,
        "shared-input refutation must need zero GB post_checks"
    );

    // Scenario B (non-shared args + known-wire equality): x_a = y_a
    // arrives as an asserted atom; the hub merges, congruence fires,
    // and the conflict surfaces through early_check — still zero GB.
    let post1 = load(&NATIVE_FF.cdclt_post_checks);
    {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x_a = b.var("x_a");
        let y_a = b.var("y_a");
        let x_r = b.var("x_r");
        let y_r = b.var("y_r");
        let f = b.uf_symbol("f");
        b.add_uf_app(f, vec![x_a], x_r);
        b.add_uf_app(f, vec![y_a], y_r);
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x_a, 1)] },
            PolyTerm { coeff: BigUint::from(6u32), vars: vec![(y_a, 1)] },
        ]);
        b.add_disequality(x_r, y_r);
        b.set_add_field_polys(true);
        let out = IncrementalSolverContext::new().solve(&b.build(), &cancel);
        assert!(matches!(out, SolveOutcome::Unsat(_)), "got {:?}", out);
    }
    assert_eq!(
        load(&NATIVE_FF.cdclt_post_checks),
        post1,
        "known-wire congruence refutation must need zero GB post_checks"
    );
    assert!(
        load(&NATIVE_FF.uf_hub_early_conflicts) > hub0,
        "the hub's early_check conflict channel must have fired"
    );
}
