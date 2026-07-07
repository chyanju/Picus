//! Phase-1 UF soundness harness.
//!
//! Ground truth comes from exhaustive point enumeration: a system with
//! UF applications is satisfiable iff SOME assignment over all
//! variables satisfies every polynomial/disequality/assignment AND,
//! per symbol, equal evaluated argument tuples map to equal results (a
//! congruence-consistent total function always extends the induced
//! partial table). Every solver verdict must equal the ground truth or
//! be Unknown; Sat models are independently re-checked against the
//! same semantics.

use std::collections::HashMap;

use num_bigint::BigUint;
use picus_core::config::{ConfigGuard, RuntimeConfig};
use picus_core::timeout::CancelToken;
use picus_solver::{
    encode, ConstraintSystem, ConstraintSystemBuilder, IncrementalSolverContext, PolyTerm,
    SolveOutcome, UnknownCause,
};

// ───────────────────────── brute-force oracle ─────────────────────────

fn coeff_mod(c: &BigUint, p: u64) -> u64 {
    (c % BigUint::from(p)).to_u64_digits().first().copied().unwrap_or(0)
}

fn eval_terms(terms: &[PolyTerm], point: &[u64], p: u64) -> u64 {
    let mut sum: u64 = 0;
    for t in terms {
        let mut v = coeff_mod(&t.coeff, p);
        for &(idx, exp) in &t.vars {
            for _ in 0..exp {
                v = v * point[idx as usize] % p;
            }
        }
        sum = (sum + v) % p;
    }
    sum
}

/// Full UF-aware satisfaction check of `cs` at `point` (user-variable
/// frame; Rabinowitsch witnesses are semantic here, not encoded).
fn point_satisfies(cs: &ConstraintSystem, point: &[u64], p: u64) -> bool {
    for eq in &cs.equalities {
        if eval_terms(eq, point, p) != 0 {
            return false;
        }
    }
    for (v, val) in &cs.assignments {
        if point[*v as usize] != coeff_mod(val, p) {
            return false;
        }
    }
    for &(a, b) in &cs.disequalities {
        if point[a as usize] == point[b as usize] {
            return false;
        }
    }
    let mut table: HashMap<(u32, Vec<u64>), u64> = HashMap::new();
    for app in &cs.uf_apps {
        let args: Vec<u64> = app.args.iter().map(|&a| point[a as usize]).collect();
        let r = point[app.result as usize];
        match table.entry((app.symbol, args)) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(r);
            }
            std::collections::hash_map::Entry::Occupied(e) => {
                if *e.get() != r {
                    return false;
                }
            }
        }
    }
    true
}

fn brute_force_sat(cs: &ConstraintSystem, p: u64) -> bool {
    let n = cs.var_names.len();
    let total = (p as u128).pow(n as u32);
    assert!(total <= 6_000_000, "oracle corpus entry too large: {}^{}", p, n);
    let mut point = vec![0u64; n];
    for k in 0..total {
        let mut x = k;
        for slot in point.iter_mut() {
            *slot = (x % p as u128) as u64;
            x /= p as u128;
        }
        if point_satisfies(cs, &point, p) {
            return true;
        }
    }
    false
}

/// Re-check a solver Sat model independently. Every variable that
/// appears in a constraint or an application must be present.
fn model_satisfies(cs: &ConstraintSystem, model: &HashMap<String, BigUint>, p: u64) -> bool {
    let mut point = vec![0u64; cs.var_names.len()];
    let mut required = vec![false; cs.var_names.len()];
    for eq in &cs.equalities {
        for t in eq {
            for &(v, _) in &t.vars {
                required[v as usize] = true;
            }
        }
    }
    for &(a, b) in &cs.disequalities {
        required[a as usize] = true;
        required[b as usize] = true;
    }
    for (v, _) in &cs.assignments {
        required[*v as usize] = true;
    }
    for app in &cs.uf_apps {
        for &a in &app.args {
            required[a as usize] = true;
        }
        required[app.result as usize] = true;
    }
    for (i, name) in cs.var_names.iter().enumerate() {
        match model.get(name) {
            Some(v) => point[i] = coeff_mod(v, p),
            None if required[i] => return false,
            None => {}
        }
    }
    point_satisfies(cs, &point, p)
}

// ───────────────────────── corpus generation ─────────────────────────

/// Deterministic LCG so the corpus is stable across runs.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_system(rng: &mut Lcg, p: u64) -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(p));
    let n_vars = 2 + rng.below(3) as usize; // 2..=4
    let vars: Vec<u32> = (0..n_vars).map(|i| b.var(&format!("v{}", i))).collect();

    let n_polys = rng.below(4) as usize; // 0..=3
    for _ in 0..n_polys {
        let n_terms = 1 + rng.below(3) as usize;
        let mut terms = Vec::with_capacity(n_terms);
        for _ in 0..n_terms {
            let coeff = 1 + rng.below(p - 1);
            let deg = rng.below(3);
            let mut mono: Vec<(u32, u16)> = Vec::new();
            for _ in 0..deg {
                let v = vars[rng.below(n_vars as u64) as usize];
                match mono.iter_mut().find(|(idx, _)| *idx == v) {
                    Some((_, e)) => *e += 1,
                    None => mono.push((v, 1)),
                }
            }
            terms.push(PolyTerm { coeff: BigUint::from(coeff), vars: mono });
        }
        b.add_equality(terms);
    }

    let n_diseqs = rng.below(3) as usize; // 0..=2
    for _ in 0..n_diseqs {
        let a = vars[rng.below(n_vars as u64) as usize];
        let c = vars[rng.below(n_vars as u64) as usize];
        if a != c {
            b.add_disequality(a, c);
        }
    }

    let n_syms = 1 + rng.below(2) as usize; // 1..=2
    let syms: Vec<(u32, usize)> = (0..n_syms)
        .map(|i| (b.uf_symbol(&format!("f{}", i)), 1 + rng.below(2) as usize))
        .collect();
    let n_apps = 1 + rng.below(4) as usize; // 1..=4
    for _ in 0..n_apps {
        let (sym, arity) = syms[rng.below(n_syms as u64) as usize];
        let args: Vec<u32> = (0..arity)
            .map(|_| vars[rng.below(n_vars as u64) as usize])
            .collect();
        let result = vars[rng.below(n_vars as u64) as usize];
        b.add_uf_app(sym, args, result);
    }

    b.set_add_field_polys(true);
    b.build()
}

fn solve(cs: &ConstraintSystem) -> SolveOutcome {
    IncrementalSolverContext::new().solve(cs, &CancelToken::none())
}

fn run_corpus_leg(cfg: RuntimeConfig, n_per_prime: usize, seed: u64) {
    let _g = ConfigGuard::install(cfg);
    let mut decided = 0usize;
    let mut total = 0usize;
    let mut sat_seen = 0usize;
    let mut unsat_seen = 0usize;
    for &p in &[3u64, 5, 7] {
        let mut rng = Lcg(seed ^ p);
        for i in 0..n_per_prime {
            let cs = random_system(&mut rng, p);
            let truth = brute_force_sat(&cs, p);
            total += 1;
            match solve(&cs) {
                SolveOutcome::Sat(model) => {
                    assert!(truth, "solver said Sat but ground truth is Unsat (p={}, i={})", p, i);
                    assert!(
                        model_satisfies(&cs, &model, p),
                        "Sat model failed the independent re-check (p={}, i={})",
                        p,
                        i
                    );
                    decided += 1;
                    sat_seen += 1;
                }
                SolveOutcome::Unsat(_) => {
                    assert!(!truth, "solver said Unsat but ground truth is Sat (p={}, i={})", p, i);
                    decided += 1;
                    unsat_seen += 1;
                }
                SolveOutcome::Unknown(_) => {}
            }
        }
    }
    assert!(
        decided * 100 >= total * 95,
        "decision rate below 95%: {}/{}",
        decided,
        total
    );
    // Anti-vacuity: both verdicts must actually occur.
    assert!(sat_seen >= 10, "corpus too Unsat-heavy: {} Sat", sat_seen);
    assert!(unsat_seen >= 8, "corpus too Sat-heavy: {} Unsat", unsat_seen);
}

#[test]
fn brute_force_differential_cdclt_leg() {
    run_corpus_leg(RuntimeConfig::default(), 60, 0x5F5C);
}

#[test]
fn brute_force_differential_dnf_leg() {
    run_corpus_leg(
        RuntimeConfig { dnf_enabled: true, ..RuntimeConfig::default() },
        30,
        0xD8F,
    );
}

// ───────────────────────── targeted cases ─────────────────────────

fn b7() -> ConstraintSystemBuilder {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
    b.set_add_field_polys(true);
    b
}

/// Pin `a - b = 0`.
fn add_eq_vars(b: &mut ConstraintSystemBuilder, x: u32, y: u32, p: u64) {
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
        PolyTerm { coeff: BigUint::from(p - 1), vars: vec![(y, 1)] },
    ]);
}

#[test]
fn congruence_forces_unsat_on_equal_args() {
    // a1 = a2 (poly), r1 = f(a1), r2 = f(a2), r1 != r2 => Unsat purely
    // via congruence.
    let mut b = b7();
    let a1 = b.var("a1");
    let a2 = b.var("a2");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let f = b.uf_symbol("f");
    add_eq_vars(&mut b, a1, a2, 7);
    b.add_uf_app(f, vec![a1], r1);
    b.add_uf_app(f, vec![a2], r2);
    b.add_disequality(r1, r2);
    assert!(matches!(solve(&b.build()), SolveOutcome::Unsat(_)));
}

#[test]
fn nested_congruence_chains_through_derived_equality() {
    // a1 = a2, r_i = f(a_i), t_i = g(r_i), t1 != t2: needs the derived
    // r1 = r2 to trigger the second congruence step.
    let mut b = b7();
    let a1 = b.var("a1");
    let a2 = b.var("a2");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let t1 = b.var("t1");
    let t2 = b.var("t2");
    let f = b.uf_symbol("f");
    let g = b.uf_symbol("g");
    add_eq_vars(&mut b, a1, a2, 7);
    b.add_uf_app(f, vec![a1], r1);
    b.add_uf_app(f, vec![a2], r2);
    b.add_uf_app(g, vec![r1], t1);
    b.add_uf_app(g, vec![r2], t2);
    b.add_disequality(t1, t2);
    assert!(matches!(solve(&b.build()), SolveOutcome::Unsat(_)));
}

#[test]
fn pigeonhole_gf3_four_distinct_args() {
    // GF(3): f on 4 pairwise-distinct args with pairwise-distinct
    // results — Unsat (only 3 field values exist).
    let mut b = ConstraintSystemBuilder::new(BigUint::from(3u32));
    b.set_add_field_polys(true);
    let f = b.uf_symbol("f");
    let mut args = Vec::new();
    let mut results = Vec::new();
    for i in 0..4 {
        let a = b.var(&format!("a{}", i));
        let r = b.var(&format!("r{}", i));
        b.add_uf_app(f, vec![a], r);
        args.push(a);
        results.push(r);
    }
    for i in 0..4 {
        for j in (i + 1)..4 {
            b.add_disequality(args[i], args[j]);
            b.add_disequality(results[i], results[j]);
        }
    }
    assert!(matches!(solve(&b.build()), SolveOutcome::Unsat(_)));
}

#[test]
fn cross_copy_shared_input_unsat() {
    // Hand-doubled shared-input shape: x_r = f(x_in), y_r = f(x_in),
    // target x_r != y_r => Unsat (same input, one function).
    let mut b = b7();
    let x_in = b.var("x_in");
    let x_r = b.var("x_r");
    let y_r = b.var("y_r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![x_in], x_r);
    b.add_uf_app(f, vec![x_in], y_r);
    b.add_disequality(x_r, y_r);
    assert!(matches!(solve(&b.build()), SolveOutcome::Unsat(_)));
}

#[test]
fn cross_copy_non_shared_args_sat_then_unsat_with_known_wire() {
    // Non-shared args: x_r = f(x_a), y_r = f(y_a), x_r != y_r is Sat
    // (inputs may differ) ...
    let mut b = b7();
    let x_a = b.var("x_a");
    let y_a = b.var("y_a");
    let x_r = b.var("x_r");
    let y_r = b.var("y_r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![x_a], x_r);
    b.add_uf_app(f, vec![y_a], y_r);
    b.add_disequality(x_r, y_r);
    let sat_side = b.clone().build();
    assert!(matches!(solve(&sat_side), SolveOutcome::Sat(_)));

    // ... and flips to Unsat once the known-wire equality x_a = y_a
    // arrives ("same inputs => same outputs", the point of the
    // abstraction).
    add_eq_vars(&mut b, x_a, y_a, 7);
    assert!(matches!(solve(&b.build()), SolveOutcome::Unsat(_)));
}

#[test]
fn distinct_symbols_do_not_force_equality() {
    // Negative control: f and g share the argument, but nothing links
    // their results.
    let mut b = b7();
    let a = b.var("a");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let f = b.uf_symbol("f");
    let g = b.uf_symbol("g");
    b.add_uf_app(f, vec![a], r1);
    b.add_uf_app(g, vec![a], r2);
    b.add_disequality(r1, r2);
    assert!(matches!(solve(&b.build()), SolveOutcome::Sat(_)));
}

#[test]
fn shared_arg_sat_pin_via_g4_completion() {
    // The cross-copy shape with NO polynomial mentioning the
    // shared argument: the post-check model cannot contain it, so only
    // G4's 0-fill completion makes this decide Sat instead of Unknown.
    let mut b = b7();
    let x_in = b.var("x_in");
    let x_r = b.var("x_r");
    let y_r = b.var("y_r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![x_in], x_r);
    b.add_uf_app(f, vec![x_in], y_r);
    match solve(&b.build()) {
        SolveOutcome::Sat(model) => {
            assert_eq!(model.get("x_r"), model.get("y_r"), "congruence in the model");
        }
        other => panic!("expected Sat via G4 completion, got {:?}", other),
    }
}

#[test]
fn trivially_true_formula_with_apps_returns_completed_model() {
    // Constant(true)-shortcut bypass: a single app and no constraints
    // must yield a completed, certified model — never a bare empty map.
    let mut b = b7();
    let x_in = b.var("x_in");
    let x_r = b.var("x_r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![x_in], x_r);
    match solve(&b.build()) {
        SolveOutcome::Sat(model) => {
            assert!(model.contains_key("x_in") && model.contains_key("x_r"));
        }
        other => panic!("expected completed Sat, got {:?}", other),
    }
}

#[test]
fn pair_cap_zero_returns_unknown_ufcap() {
    let _g = ConfigGuard::install(RuntimeConfig {
        uf_pair_cap: 0,
        ..RuntimeConfig::default()
    });
    let mut b = b7();
    let a = b.var("a");
    let r = b.var("r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![a], r);
    assert!(matches!(
        solve(&b.build()),
        SolveOutcome::Unknown(UnknownCause::UfCap)
    ));
}

#[test]
fn uf_disabled_returns_unknown_ufunsupported() {
    let _g = ConfigGuard::install(RuntimeConfig {
        uf_enabled: false,
        ..RuntimeConfig::default()
    });
    let mut b = b7();
    let a = b.var("a");
    let r = b.var("r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![a], r);
    assert!(matches!(
        solve(&b.build()),
        SolveOutcome::Unknown(UnknownCause::UfUnsupported)
    ));
}

/// Degraded-continue under a tiny cap: emission order for one symbol's
/// pairs is (0,1), (0,2), (1,2); cap = 1 covers only (0,1).
fn degraded_base() -> (ConstraintSystemBuilder, [u32; 6]) {
    let mut b = b7();
    let a = b.var("a");
    let c = b.var("c");
    let d = b.var("d");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let r3 = b.var("r3");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![a], r1);
    b.add_uf_app(f, vec![c], r2);
    b.add_uf_app(f, vec![d], r3);
    (b, [a, c, d, r1, r2, r3])
}

#[test]
fn degraded_continue_certifies_a_clean_sat() {
    // Args pinned pairwise distinct, so no congruence duty exists and
    // certification must pass deterministically even though only the
    // (0,1) pair was expanded.
    let _g = ConfigGuard::install(RuntimeConfig {
        uf_pair_cap: 1,
        ..RuntimeConfig::default()
    });
    let pinned = || {
        let (mut b, [a, c, d, _r1, _r2, _r3]) = degraded_base();
        b.add_assignment(a, BigUint::from(0u32));
        b.add_assignment(c, BigUint::from(1u32));
        b.add_assignment(d, BigUint::from(2u32));
        b.build()
    };
    match solve(&pinned()) {
        SolveOutcome::Sat(model) => {
            // Independent congruence re-check of the certified model.
            assert!(model_satisfies(&pinned(), &model, 7));
        }
        other => panic!("expected certified Sat under a degraded prefix, got {:?}", other),
    }
}

#[test]
fn degraded_continue_rejects_violating_sat_as_ufcap() {
    // Pin an uncovered pair into violation: a = 0, c = 1 (covered pair
    // (0,1) trivially satisfied), d = 0 = a, r1 = 1, r3 = 2 — the
    // uncovered pair (0,2) has equal args and distinct results. The
    // system is genuinely UNSAT under congruence.
    let pinned = || {
        let (mut b, [a, c, d, r1, _r2, r3]) = degraded_base();
        b.add_assignment(a, BigUint::from(0u32));
        b.add_assignment(c, BigUint::from(1u32));
        b.add_assignment(d, BigUint::from(0u32));
        b.add_assignment(r1, BigUint::from(1u32));
        b.add_assignment(r3, BigUint::from(2u32));
        b.build()
    };
    // Eager leg, cap 1: the violating pair is outside the expanded
    // prefix, so the candidate reaches certification and must fail as
    // the expected Unknown(UfCap) — not Sat, not a defect class.
    {
        let _g = ConfigGuard::install(RuntimeConfig {
            uf_pair_cap: 1,
            uf_mode: picus_core::config::UfMode::Ackermann,
            ..RuntimeConfig::default()
        });
        assert!(matches!(
            solve(&pinned()),
            SolveOutcome::Unknown(UnknownCause::UfCap)
        ));
    }
    // Lazy leg, same cap: the equality hub ingests the pinned
    // constants and derives f(a) ~ f(d) by congruence REGARDLESS of
    // the care prefix — strictly more complete: a sound Unsat.
    {
        let _g = ConfigGuard::install(RuntimeConfig {
            uf_pair_cap: 1,
            ..RuntimeConfig::default()
        });
        assert!(matches!(solve(&pinned()), SolveOutcome::Unsat(_)));
    }
}

#[test]
fn arity_mismatch_is_a_typed_refusal() {
    let mut b = b7();
    let a = b.var("a");
    let c = b.var("c");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![a], r1);
    b.add_uf_app(f, vec![a, c], r2);
    let cs = b.build();
    // encode refuses ...
    assert!(matches!(encode(&cs), Err(picus_solver::EngineError::Encoding(_))));
    // ... and the solve entry refuses too (never a silent drop).
    assert!(matches!(
        solve(&cs),
        SolveOutcome::Unknown(UnknownCause::EncodingFailure)
    ));
}

#[test]
fn encoded_uf_apps_survive_bitsum_extraction() {
    // A bitsum-shaped system (bit constraints + chain equality) plus an
    // app: the extraction rebuild must carry the apps through to the
    // EncodedSystem, in a frame where the indices still resolve.
    let mut b = b7();
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let s = b.var("s");
    let r = b.var("r");
    let one = BigUint::from(1u32);
    // b0^2 - b0 = 0, b1^2 - b1 = 0 (bit constraints)
    for &bit in &[b0, b1] {
        b.add_equality(vec![
            PolyTerm { coeff: one.clone(), vars: vec![(bit, 2)] },
            PolyTerm { coeff: BigUint::from(6u32), vars: vec![(bit, 1)] },
        ]);
    }
    // b0 + 2*b1 - s = 0 (chain of length 2 = MIN_AUTO_BITSUM_LEN)
    b.add_equality(vec![
        PolyTerm { coeff: one.clone(), vars: vec![(b0, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(b1, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(s, 1)] },
    ]);
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![s], r);
    let encoded = encode(&b.build()).expect("encodes");
    assert_eq!(encoded.uf_apps.len(), 1, "apps must survive the bitsum rebuild");
    let names = encoded.poly_ring.var_names();
    let app = &encoded.uf_apps[0];
    assert_eq!(names[app.args[0] as usize], "s");
    assert_eq!(names[app.result as usize], "r");
}

#[test]
fn abstraction_contract_sat_is_abstract() {
    // A query Sat under the UF abstraction whose witness is spurious
    // for a concrete refinement (e.g. f = const 0 forces x_r = y_r):
    // the solver still answers Sat — the ABSTRACTED system is
    // satisfiable — and the has_uf marker on the system is what tells
    // consumers the Sat-is-abstract rule applies.
    let mut b = b7();
    let x_a = b.var("x_a");
    let y_a = b.var("y_a");
    let x_r = b.var("x_r");
    let y_r = b.var("y_r");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![x_a], x_r);
    b.add_uf_app(f, vec![y_a], y_r);
    b.add_disequality(x_r, y_r);
    let cs = b.build();
    assert!(cs.has_uf(), "the abstraction marker consumers must read");
    match solve(&cs) {
        SolveOutcome::Sat(model) => {
            assert!(model_satisfies(&cs, &model, 7), "abstract witness is congruence-consistent");
            assert_ne!(model.get("x_a"), model.get("y_a"), "witness distinguishes the inputs");
        }
        other => panic!("expected abstract Sat, got {:?}", other),
    }
}

#[test]
fn brute_force_differential_ackermann_leg() {
    // Three-way parity: the eager leg must agree with the same ground
    // truth the lazy leg (default corpus leg above) is held to.
    run_corpus_leg(
        RuntimeConfig {
            uf_mode: picus_core::config::UfMode::Ackermann,
            ..RuntimeConfig::default()
        },
        40,
        0x5F5C, // same seed as the lazy leg: identical corpus
    );
}
