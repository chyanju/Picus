//! Bit-identity regression for the UF feature: UF-free queries must
//! behave byte-identically to the pre-UF solver under every `uf_*`
//! knob setting.
//!
//! Three legs:
//! 1. Golden pinned digest — `digest_constraint_side` of a fixed
//!    UF-free system equals the constant recorded on the pre-change
//!    tree (the UF digest section is empty-guarded, so the byte stream
//!    must be unchanged), and a digest separation check (adding an app
//!    changes it; app-differing systems differ).
//! 2. Verdict + digest identity of a UF-free corpus across the `uf_*`
//!    knob grid.
//! 3. `cdclt_iter_cap` boundary pin — digests cover only the cache
//!    path and are computed before the cdclt loop, so they cannot see
//!    loop re-timing; the minimal deciding cap N recorded pre-change
//!    (and Unknown(IterCap) at N−1) observes it directly through
//!    public knobs and SolveOutcome.

use num_bigint::BigUint;
use picus_core::config::{ConfigGuard, RuntimeConfig};
use picus_core::timeout::CancelToken;
use picus_solver::{
    digest_constraint_side, solve_boolean_query, BooleanQuery, ConstraintSystem,
    ConstraintSystemBuilder, Formula, Literal, PolyTerm, SolveOutcome, UnknownCause,
};

/// Recorded on the pre-change tree (feat/ufff @ 3d0a7da) by solving
/// `golden_system()` through the identical construction below.
const GOLDEN_DIGEST: u128 = 0xc097e55c59a508a3340256f0a2dcb64b;

/// Minimal deciding `cdclt_iter_cap` per corpus query, recorded on the
/// pre-change tree: (N, decided-verdict-is-sat). At N−1 each query
/// returns Unknown(IterCap).
const ITER_CAP_PINS: [(u64, bool); 3] = [(4, true), (3, false), (8, false)];

/// The fixed UF-free system whose constraint-side digest is pinned.
/// Deliberately exercises every digest-covered field: prime,
/// var_names, equalities, assignments, bitsums, add_field_polys.
fn golden_system() -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(101u32));
    let x = b.var("x");
    let y = b.var("y");
    let z = b.var("z");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    // x + 2y - 3 = 0
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(y, 1)] },
        PolyTerm { coeff: BigUint::from(98u32), vars: vec![] },
    ]);
    // x*y^2 - z = 0
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1), (y, 2)] },
        PolyTerm { coeff: BigUint::from(100u32), vars: vec![(z, 1)] },
    ]);
    b.add_assignment(z, BigUint::from(5u32));
    b.add_bitsum(vec![b0, b1]);
    b.add_disequality(x, y);
    b.set_add_field_polys(true);
    b.build()
}

#[test]
fn golden_digest_is_unchanged() {
    assert_eq!(
        digest_constraint_side(&golden_system()),
        GOLDEN_DIGEST,
        "UF-free digest byte stream drifted from the pre-UF constant"
    );
}

#[test]
fn digest_separates_uf_sections() {
    let base = digest_constraint_side(&golden_system());

    let with_app = |arg: u32, result: u32| {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(101u32));
        let x = b.var("x");
        let y = b.var("y");
        let z = b.var("z");
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(2u32), vars: vec![(y, 1)] },
            PolyTerm { coeff: BigUint::from(98u32), vars: vec![] },
        ]);
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1), (y, 2)] },
            PolyTerm { coeff: BigUint::from(100u32), vars: vec![(z, 1)] },
        ]);
        b.add_assignment(z, BigUint::from(5u32));
        b.add_bitsum(vec![b0, b1]);
        b.add_disequality(x, y);
        b.set_add_field_polys(true);
        let f = b.uf_symbol("f");
        b.add_uf_app(f, vec![arg], result);
        b.build()
    };

    let d1 = digest_constraint_side(&with_app(0, 2));
    let d2 = digest_constraint_side(&with_app(1, 2));
    assert_ne!(base, d1, "adding an app must change the digest");
    assert_ne!(d1, d2, "systems differing in one app must not share a digest");
}

/// Fixed UF-free disjunction-bearing corpus for the cdclt_iter_cap
/// boundary pin. Byte-identical to the pre-change recording probe.
fn iter_cap_corpus() -> Vec<BooleanQuery> {
    let p = BigUint::from(7u32);
    let one = || BigUint::from(1u32);
    let lin = |v: u32, c: u64| {
        Literal::Eq(
            vec![PolyTerm { coeff: one(), vars: vec![(v, 1)] }],
            vec![PolyTerm { coeff: BigUint::from(c), vars: vec![] }],
        )
    };
    let mut out = Vec::new();

    // q0 (SAT): (x=1 ∨ x=2) ∧ (y=x ∨ y=3) ∧ x+y=4
    {
        let mut b = ConstraintSystemBuilder::new(p.clone());
        let x = b.var("x");
        let y = b.var("y");
        let f = Formula::And(vec![
            Formula::Or(vec![
                Formula::Lit(lin(x, 1)),
                Formula::Lit(lin(x, 2)),
            ]),
            Formula::Or(vec![
                Formula::Lit(Literal::Eq(
                    vec![PolyTerm { coeff: one(), vars: vec![(y, 1)] }],
                    vec![PolyTerm { coeff: one(), vars: vec![(x, 1)] }],
                )),
                Formula::Lit(lin(y, 3)),
            ]),
            Formula::Lit(Literal::Eq(
                vec![
                    PolyTerm { coeff: one(), vars: vec![(x, 1)] },
                    PolyTerm { coeff: one(), vars: vec![(y, 1)] },
                ],
                vec![PolyTerm { coeff: BigUint::from(4u32), vars: [].to_vec() }],
            )),
        ]);
        out.push(BooleanQuery::from_builder_and_formula(b, f));
    }

    // q1 (UNSAT): (x=1 ∨ x=2) ∧ (x=3 ∨ x=4)
    {
        let mut b = ConstraintSystemBuilder::new(p.clone());
        let x = b.var("x");
        let f = Formula::And(vec![
            Formula::Or(vec![Formula::Lit(lin(x, 1)), Formula::Lit(lin(x, 2))]),
            Formula::Or(vec![Formula::Lit(lin(x, 3)), Formula::Lit(lin(x, 4))]),
        ]);
        out.push(BooleanQuery::from_builder_and_formula(b, f));
    }

    // q2 (UNSAT, needs theory): (x=1 ∨ x=2) ∧ (y = x·x) ∧ y=3 ∧ (z=y ∨ z=0)
    {
        let mut b = ConstraintSystemBuilder::new(p.clone());
        let x = b.var("x");
        let y = b.var("y");
        let z = b.var("z");
        let f = Formula::And(vec![
            Formula::Or(vec![Formula::Lit(lin(x, 1)), Formula::Lit(lin(x, 2))]),
            Formula::Lit(Literal::Eq(
                vec![PolyTerm { coeff: one(), vars: vec![(y, 1)] }],
                vec![PolyTerm { coeff: one(), vars: vec![(x, 2)] }],
            )),
            Formula::Lit(lin(y, 3)),
            Formula::Or(vec![
                Formula::Lit(Literal::Eq(
                    vec![PolyTerm { coeff: one(), vars: vec![(z, 1)] }],
                    vec![PolyTerm { coeff: one(), vars: vec![(y, 1)] }],
                )),
                Formula::Lit(lin(z, 0)),
            ]),
        ]);
        out.push(BooleanQuery::from_builder_and_formula(b, f));
    }

    out
}

/// The `uf_*` grid: every combination must leave UF-free behavior
/// untouched.
fn uf_knob_grid() -> Vec<RuntimeConfig> {
    let mut grid = Vec::new();
    for &uf_enabled in &[true, false] {
        for &uf_pair_cap in &[0u64, 4096] {
            for &uf_mode in &[picus_core::config::UfMode::Lazy, picus_core::config::UfMode::Ackermann] {
                for &uf_closure in &[true, false] {
                    grid.push(RuntimeConfig {
                        uf_enabled,
                        uf_pair_cap,
                        uf_mode,
                        uf_closure,
                        ..RuntimeConfig::default()
                    });
                }
            }
        }
    }
    grid
}

#[test]
fn uf_free_corpus_verdicts_and_digests_identical_across_uf_grid() {
    // Baseline verdicts under the compiled defaults.
    let baseline: Vec<SolveOutcome> = {
        let _g = ConfigGuard::install(RuntimeConfig::default());
        iter_cap_corpus()
            .iter()
            .map(|q| solve_boolean_query(q, &CancelToken::none()))
            .collect()
    };
    assert!(matches!(baseline[0], SolveOutcome::Sat(_)));
    assert!(matches!(baseline[1], SolveOutcome::Unsat(_)));
    assert!(matches!(baseline[2], SolveOutcome::Unsat(_)));

    for cfg in uf_knob_grid() {
        let _g = ConfigGuard::install(cfg.clone());
        assert_eq!(
            digest_constraint_side(&golden_system()),
            GOLDEN_DIGEST,
            "digest drifted under {:?}",
            cfg
        );
        for (i, q) in iter_cap_corpus().iter().enumerate() {
            let out = solve_boolean_query(q, &CancelToken::none());
            let same = matches!(
                (&baseline[i], &out),
                (SolveOutcome::Sat(_), SolveOutcome::Sat(_))
                    | (SolveOutcome::Unsat(_), SolveOutcome::Unsat(_))
            );
            assert!(
                same,
                "verdict changed on UF-free q{} under uf_enabled={} uf_pair_cap={}: {:?}",
                i, cfg.uf_enabled, cfg.uf_pair_cap, out
            );
        }
    }
}

#[test]
fn cdclt_iter_cap_boundary_pin() {
    // The pinned minimal cap must decide each query with the pinned
    // verdict, and N−1 must be Unknown(IterCap) — this observes
    // cdclt-loop re-timing that the digests cannot. Run under both a
    // default and a flipped uf_enabled to pin the orchestrator rewire.
    for &uf_enabled in &[true, false] {
        for (i, q) in iter_cap_corpus().iter().enumerate() {
            let (n, is_sat) = ITER_CAP_PINS[i];
            let at = |cap: u64| {
                let _g = ConfigGuard::install(RuntimeConfig {
                    cdclt_iter_cap: cap,
                    uf_enabled,
                    ..RuntimeConfig::default()
                });
                solve_boolean_query(q, &CancelToken::none())
            };
            let decided = at(n);
            match (is_sat, &decided) {
                (true, SolveOutcome::Sat(_)) | (false, SolveOutcome::Unsat(_)) => {}
                _ => panic!(
                    "q{} at pinned cap {} (uf_enabled={}): expected {} — got {:?} \
                     (cdclt loop re-timed?)",
                    i,
                    n,
                    uf_enabled,
                    if is_sat { "Sat" } else { "Unsat" },
                    decided
                ),
            }
            assert!(
                matches!(at(n - 1), SolveOutcome::Unknown(UnknownCause::IterCap)),
                "q{} at cap {} (uf_enabled={}): expected Unknown(IterCap)",
                i,
                n - 1,
                uf_enabled
            );
        }
    }
}
