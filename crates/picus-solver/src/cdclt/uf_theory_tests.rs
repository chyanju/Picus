use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;

use super::*;
use crate::cdclt::egraph::EGraph;
use crate::frontend::encoder::UfApp;
use crate::sat::Var;

/// Stub inner theory with scriptable early_check/post_check outcomes.
struct StubTheory {
    early: Option<CheckOutcome>,
    post: Option<CheckOutcome>,
    notified: Vec<(Var, bool)>,
}

impl StubTheory {
    fn new() -> Self {
        StubTheory { early: None, post: None, notified: Vec::new() }
    }
}

impl Theory for StubTheory {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        self.notified.push((atom, polarity));
    }

    fn early_check(&mut self) -> Option<CheckOutcome> {
        self.early.take()
    }

    fn post_check(&mut self) -> CheckOutcome {
        self.post.take().unwrap_or(CheckOutcome::Unknown)
    }
}

fn model(pairs: &[(&str, u64)]) -> HashMap<String, BigUint> {
    pairs.iter().map(|&(k, v)| (k.to_string(), BigUint::from(v))).collect()
}

/// Frame: v0=a, v1=b, v2=r1, v3=r2; apps r1 = f(a), r2 = f(b).
fn setup_two_apps(care_complete: bool) -> (UfSetup, Rc<UfOutcomeFlags>) {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let r1 = eg.add_var(2);
    let r2 = eg.add_var(3);
    let f1 = eg.add_app(0, &[a]);
    let f2 = eg.add_app(0, &[b]);
    eg.merge_definitional(f1, r1);
    eg.merge_definitional(f2, r2);
    // Care atoms: (a = b) -> Var(10), (r1 = r2) -> Var(11).
    eg.register_trigger_atom(a, b, Var(10));
    eg.register_trigger_atom(r1, r2, Var(11));
    let mut atom_view = HashMap::new();
    atom_view.insert(Var(10), (a, b));
    atom_view.insert(Var(11), (r1, r2));
    let apps = vec![
        UfApp { symbol: 0, args: vec![0], result: 2 },
        UfApp { symbol: 0, args: vec![1], result: 3 },
    ];
    let flags = Rc::new(UfOutcomeFlags::default());
    let setup = UfSetup {
        eg,
        atom_view,
        apps,
        symbols: vec!["f".to_string()],
        var_names: vec!["a".into(), "b".into(), "r1".into(), "r2".into()],
        prime: BigUint::from(7u32),
        care_complete,
        flags: Rc::clone(&flags),
    };
    (setup, flags)
}

#[test]
fn inner_early_sat_is_downgraded_to_none() {
    // The orchestrator treats an early Sat as TERMINAL; forwarding it
    // would bypass congruence certification, so the hub downgrades it.
    let (setup, _flags) = setup_two_apps(true);
    let mut inner = StubTheory::new();
    inner.early = Some(CheckOutcome::Sat(model(&[])));
    let mut th = UfCombinedTheory::new(inner, setup);
    assert!(th.early_check().is_none(), "inner early Sat must not surface");
}

#[test]
fn inner_early_unsat_passes_through() {
    let (setup, _flags) = setup_two_apps(true);
    let mut inner = StubTheory::new();
    inner.early = Some(CheckOutcome::Unsat { core: vec![Var(3)] });
    let mut th = UfCombinedTheory::new(inner, setup);
    match th.early_check() {
        Some(CheckOutcome::Unsat { core }) => assert_eq!(core, vec![Var(3)]),
        other => panic!("expected pass-through Unsat, got {:?}", other.is_some()),
    }
}

#[test]
fn hub_conflict_beats_inner_early_check() {
    let (setup, _flags) = setup_two_apps(true);
    let mut th = UfCombinedTheory::new(StubTheory::new(), setup);
    th.push();
    // a = b (Var 10 true), then r1 != r2 (Var 11 false): after
    // congruence merges r1 ~ r2, the diseq is same-class — conflict.
    th.notify_fact(Var(10), true);
    th.notify_fact(Var(11), false);
    match th.early_check() {
        Some(CheckOutcome::Unsat { core }) => {
            assert!(core.contains(&Var(10)) && core.contains(&Var(11)));
        }
        _ => panic!("expected hub conflict"),
    }
}

#[test]
fn congruence_propagates_result_atom_with_explanation() {
    let (setup, _flags) = setup_two_apps(true);
    let mut th = UfCombinedTheory::new(StubTheory::new(), setup);
    th.push();
    th.notify_fact(Var(10), true); // a = b
    let props = th.propagate();
    assert_eq!(props, vec![(Var(11), true)], "r1 = r2 propagates");
    let expl = th.explain(Var(11), true);
    assert_eq!(expl, vec![(Var(10), true)]);
}

#[test]
fn certifies_and_completes_the_model() {
    // Model from the inner theory covers only a, b (atom vars); the
    // hub completes r1/r2 from the classes and certifies.
    let (setup, _flags) = setup_two_apps(true);
    let mut inner = StubTheory::new();
    inner.post = Some(CheckOutcome::Sat(model(&[("a", 1), ("b", 2)])));
    let mut th = UfCombinedTheory::new(inner, setup);
    match th.post_check() {
        CheckOutcome::Sat(m) => {
            // r1 and r2 got injective fresh values (pure-UF classes,
            // a != b so no congruence duty).
            assert!(m.contains_key("r1") && m.contains_key("r2"));
        }
        other => panic!("expected certified Sat, got {:?}", matches!(other, CheckOutcome::Unknown)),
    }
}

#[test]
fn rejects_congruence_violation_as_unknown_never_sat() {
    // a = b assigned equal values but r1, r2 pinned different: the
    // candidate violates congruence and must degrade to Unknown.
    let (setup, flags) = setup_two_apps(true);
    let mut inner = StubTheory::new();
    inner.post = Some(CheckOutcome::Sat(model(&[
        ("a", 1),
        ("b", 1),
        ("r1", 2),
        ("r2", 3),
    ])));
    let mut th = UfCombinedTheory::new(inner, setup);
    assert!(matches!(th.post_check(), CheckOutcome::Unknown));
    // Complete care: defect-class, NOT the cap flag.
    assert!(!flags.degraded_by_cap.get());
}

#[test]
fn classifies_degraded_prefix_failures_as_cap() {
    let (setup, flags) = setup_two_apps(false);
    let mut inner = StubTheory::new();
    inner.post = Some(CheckOutcome::Sat(model(&[
        ("a", 1),
        ("b", 1),
        ("r1", 2),
        ("r2", 3),
    ])));
    let mut th = UfCombinedTheory::new(inner, setup);
    assert!(matches!(th.post_check(), CheckOutcome::Unknown));
    assert!(flags.degraded_by_cap.get(), "degraded prefix sets the cap flag");
}

#[test]
fn pop_restores_hub_state_for_renotification() {
    let (setup, _flags) = setup_two_apps(true);
    let mut th = UfCombinedTheory::new(StubTheory::new(), setup);
    th.push();
    th.notify_fact(Var(10), true);
    let _ = th.propagate();
    th.pop();
    // Re-notify after the backjump (the orchestrator's resync
    // pattern): idempotent, and the propagation re-derives.
    th.push();
    th.notify_fact(Var(10), true);
    let props = th.propagate();
    assert_eq!(props, vec![(Var(11), true)], "re-derived after pop/re-notify");
}

#[test]
fn tiny_p_fallback_zero_fills_and_certifies() {
    // GF(2), empty model, four pure classes but only two field values:
    // fresh values exhaust and the remainder 0-fills. With two
    // DISTINCT single-application symbols a collision is structurally
    // impossible, so the fallback must certify regardless of class
    // iteration order.
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let r1 = eg.add_var(2);
    let r2 = eg.add_var(3);
    let f1 = eg.add_app(0, &[a]);
    let g1 = eg.add_app(1, &[b]);
    eg.merge_definitional(f1, r1);
    eg.merge_definitional(g1, r2);
    let apps = vec![
        UfApp { symbol: 0, args: vec![0], result: 2 },
        UfApp { symbol: 1, args: vec![1], result: 3 },
    ];
    let flags = Rc::new(UfOutcomeFlags::default());
    let setup = UfSetup {
        eg,
        atom_view: HashMap::new(),
        apps,
        symbols: vec!["f".to_string(), "g".to_string()],
        var_names: vec!["a".into(), "b".into(), "r1".into(), "r2".into()],
        prime: BigUint::from(2u32),
        care_complete: true,
        flags,
    };
    let mut inner = StubTheory::new();
    inner.post = Some(CheckOutcome::Sat(model(&[])));
    let mut th = UfCombinedTheory::new(inner, setup);
    match th.post_check() {
        CheckOutcome::Sat(m) => {
            for name in ["a", "b", "r1", "r2"] {
                assert!(m.contains_key(name), "completion fills {}", name);
            }
        }
        _ => panic!("expected tiny-p fallback Sat"),
    }
}

#[test]
fn tiny_p_infeasible_sets_the_flag() {
    // GF(2) with results pinned apart and args left pure: fresh values
    // exhaust, the 0-fill makes both args 0, and the table check
    // rejects — infeasible, not Sat, not a cap outcome.
    let (mut setup, flags) = setup_two_apps(true);
    setup.prime = BigUint::from(2u32);
    let mut inner = StubTheory::new();
    inner.post = Some(CheckOutcome::Sat(model(&[("r1", 0), ("r2", 1)])));
    let mut th = UfCombinedTheory::new(inner, setup);
    assert!(matches!(th.post_check(), CheckOutcome::Unknown));
    assert!(flags.infeasible.get(), "fresh-value exhaustion marks infeasible");
    assert!(!flags.degraded_by_cap.get());
}
