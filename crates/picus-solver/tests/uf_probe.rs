//! `probe_unsat_uf` soundness: the probe may only answer Unsat, and
//! every answer must agree with exhaustive ground truth over the full
//! UF semantics (polys + disequalities + per-symbol congruence).

use std::collections::HashMap;

use num_bigint::BigUint;
use picus_core::timeout::CancelToken;
use picus_solver::{
    ConstraintSystem, ConstraintSystemBuilder, IncrementalSolverContext, PolyTerm, SolveOutcome,
};

fn coeff_mod(c: &BigUint, p: u64) -> u64 {
    (c % BigUint::from(p)).to_u64_digits().first().copied().unwrap_or(0)
}

fn point_satisfies(cs: &ConstraintSystem, point: &[u64], p: u64) -> bool {
    for eq in &cs.equalities {
        let mut sum: u64 = 0;
        for t in eq {
            let mut v = coeff_mod(&t.coeff, p);
            for &(idx, exp) in &t.vars {
                for _ in 0..exp {
                    v = v * point[idx as usize] % p;
                }
            }
            sum = (sum + v) % p;
        }
        if sum != 0 {
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
    assert!(total <= 6_000_000);
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

/// Doubled-shape corpus entry over GF(7): two applications of one
/// symbol, a target disequality on the results, an optional
/// argument-equating polynomial (the congruence trigger), and an
/// optional extra random polynomial.
fn corpus_entry(rng: &mut Lcg) -> ConstraintSystem {
    let p = 7u64;
    let mut b = ConstraintSystemBuilder::new(BigUint::from(p));
    let a1 = b.var("a1");
    let a2 = b.var("a2");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let f = b.uf_symbol("f");
    b.add_uf_app(f, vec![a1], r1);
    b.add_uf_app(f, vec![a2], r2);
    b.add_disequality(r1, r2);
    if rng.below(2) == 0 {
        // a1 - a2 = 0: makes the target Unsat via congruence, and the
        // equality lands in the cached basis so the probe can see it.
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(a1, 1)] },
            PolyTerm { coeff: BigUint::from(p - 1), vars: vec![(a2, 1)] },
        ]);
    }
    if rng.below(2) == 0 {
        // Random extra linear polynomial over the frame.
        let vars = [a1, a2, r1, r2];
        let x = vars[rng.below(4) as usize];
        let y = vars[rng.below(4) as usize];
        if x != y {
            let c = 1 + rng.below(p - 1);
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
                PolyTerm { coeff: BigUint::from(c), vars: vec![(y, 1)] },
            ]);
        }
    }
    b.set_add_field_polys(true);
    b.build()
}

#[test]
fn probe_answers_are_sound_and_not_vacuous() {
    let mut rng = Lcg(0xBEE5);
    let cancel = CancelToken::none();
    let mut hits = 0usize;
    let mut misses = 0usize;
    for i in 0..60 {
        let cs = corpus_entry(&mut rng);
        let truth = brute_force_sat(&cs, 7);
        let mut ctx = IncrementalSolverContext::new();
        // Build-on-second-consecutive-digest: the first call only
        // registers the digest.
        assert!(
            ctx.probe_unsat_uf(&cs, &cancel).is_none(),
            "first sighting must not build (entry {})",
            i
        );
        match ctx.probe_unsat_uf(&cs, &cancel) {
            Some(SolveOutcome::Unsat(_)) => {
                assert!(!truth, "probe said Unsat but ground truth is Sat (entry {})", i);
                hits += 1;
            }
            Some(other) => panic!("probe may only answer Unsat, got {:?}", other),
            None => misses += 1,
        }
    }
    // Anti-vacuity: the congruence-triggered entries must actually
    // produce probe hits, and some entries must fall through.
    assert!(hits >= 10, "probe never fires: {} hits", hits);
    assert!(misses >= 10, "probe unexpectedly decides everything: {} misses", misses);
}

#[test]
fn probe_respects_the_uf_closure_kill_switch() {
    use picus_core::config::{ConfigGuard, RuntimeConfig};
    let _g = ConfigGuard::install(RuntimeConfig {
        uf_closure: false,
        ..RuntimeConfig::default()
    });
    let mut rng = Lcg(1);
    let cs = corpus_entry(&mut rng);
    let mut ctx = IncrementalSolverContext::new();
    let cancel = CancelToken::none();
    assert!(ctx.probe_unsat_uf(&cs, &cancel).is_none());
    assert!(ctx.probe_unsat_uf(&cs, &cancel).is_none(), "knob off: never builds");
}

#[test]
fn probe_derives_nested_congruence() {
    // a1 = a2, r_i = f(a_i), t_i = g(r_i), target t1 != t2: needs the
    // derived r1 - r2 to feed the second congruence round.
    let p = 7u64;
    let mut b = ConstraintSystemBuilder::new(BigUint::from(p));
    let a1 = b.var("a1");
    let a2 = b.var("a2");
    let r1 = b.var("r1");
    let r2 = b.var("r2");
    let t1 = b.var("t1");
    let t2 = b.var("t2");
    let f = b.uf_symbol("f");
    let g = b.uf_symbol("g");
    b.add_uf_app(f, vec![a1], r1);
    b.add_uf_app(f, vec![a2], r2);
    b.add_uf_app(g, vec![r1], t1);
    b.add_uf_app(g, vec![r2], t2);
    b.add_disequality(t1, t2);
    b.add_equality(vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(a1, 1)] },
        PolyTerm { coeff: BigUint::from(p - 1), vars: vec![(a2, 1)] },
    ]);
    b.set_add_field_polys(true);
    let cs = b.build();
    let mut ctx = IncrementalSolverContext::new();
    let cancel = CancelToken::none();
    assert!(ctx.probe_unsat_uf(&cs, &cancel).is_none());
    assert!(
        matches!(ctx.probe_unsat_uf(&cs, &cancel), Some(SolveOutcome::Unsat(_))),
        "two-round closure must refute the nested target"
    );
}
