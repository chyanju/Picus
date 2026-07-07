//! Knob-grid soundness for UF-bearing queries: the lazy pipeline must
//! stay sound (verdict = ground truth or Unknown) under every wiring
//! wiring knob the lazy hub composes with — incremental theory, equality engine,
//! multi-prime router, DNF, cache, linear elimination — and the lazy
//! and eager legs must agree modulo Unknown.

use std::collections::HashMap;

use num_bigint::BigUint;
use picus_core::config::{ConfigGuard, RuntimeConfig, UfMode};
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

fn random_system(rng: &mut Lcg, p: u64) -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(p));
    // A small variable pool with several applications and both
    // equality and disequality constraints biases the corpus toward a
    // healthy Sat/Unsat mix (congruence conflicts need collisions).
    let n_vars = 2 + rng.below(3) as usize; // 2..=4
    let vars: Vec<u32> = (0..n_vars).map(|i| b.var(&format!("v{}", i))).collect();
    let f = b.uf_symbol("f");
    for _ in 0..(2 + rng.below(2) as usize) {
        let arg = vars[rng.below(n_vars as u64) as usize];
        let result = vars[rng.below(n_vars as u64) as usize];
        b.add_uf_app(f, vec![arg], result);
    }
    for _ in 0..rng.below(3) {
        let x = vars[rng.below(n_vars as u64) as usize];
        let y = vars[rng.below(n_vars as u64) as usize];
        if x != y {
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
                PolyTerm { coeff: BigUint::from(p - 1), vars: vec![(y, 1)] },
            ]);
        }
    }
    for _ in 0..rng.below(3) {
        let x = vars[rng.below(n_vars as u64) as usize];
        let y = vars[rng.below(n_vars as u64) as usize];
        if x != y {
            b.add_disequality(x, y);
        }
    }
    b.set_add_field_polys(true);
    b.build()
}

fn run_grid_leg(name: &str, cfg: RuntimeConfig) {
    run_grid_leg_with_floors(name, cfg, 10, 8, 3);
}

/// `unknown_denom`: Unknowns must be <= total / unknown_denom.
fn run_grid_leg_with_floors(
    name: &str,
    cfg: RuntimeConfig,
    sat_floor: usize,
    unsat_floor: usize,
    unknown_denom: usize,
) {
    let _g = ConfigGuard::install(cfg);
    let mut rng = Lcg(0x6811D ^ name.len() as u64);
    let mut sat_seen = 0usize;
    let mut unsat_seen = 0usize;
    let mut unknowns = 0usize;
    let total = 40usize;
    for i in 0..total {
        let p = if i % 2 == 0 { 5 } else { 7 };
        let cs = random_system(&mut rng, p);
        let truth = brute_force_sat(&cs, p);
        match IncrementalSolverContext::new().solve(&cs, &CancelToken::none()) {
            SolveOutcome::Sat(_) => {
                assert!(truth, "[{}] Sat but ground truth Unsat (entry {})", name, i);
                sat_seen += 1;
            }
            SolveOutcome::Unsat(_) => {
                assert!(!truth, "[{}] Unsat but ground truth Sat (entry {})", name, i);
                unsat_seen += 1;
            }
            SolveOutcome::Unknown(_) => unknowns += 1,
        }
    }
    // Anti-vacuity floors mirroring knob_grid_soundness.rs.
    assert!(sat_seen >= sat_floor, "[{}] too few SAT decisions: {}", name, sat_seen);
    assert!(unsat_seen >= unsat_floor, "[{}] too few UNSAT decisions: {}", name, unsat_seen);
    assert!(
        unknowns * unknown_denom <= total,
        "[{}] too many Unknowns: {}/{}",
        name,
        unknowns,
        total
    );
}

#[test]
fn grid_lazy_default() {
    run_grid_leg("lazy", RuntimeConfig::default());
}

#[test]
fn grid_lazy_incremental_theory() {
    run_grid_leg(
        "lazy+incremental",
        RuntimeConfig { cdclt_incremental_theory: true, ..RuntimeConfig::default() },
    );
}

#[test]
fn grid_lazy_equality_engine() {
    run_grid_leg(
        "lazy+ee",
        RuntimeConfig { cdclt_equality_engine: true, ..RuntimeConfig::default() },
    );
}

#[test]
fn grid_lazy_multi_prime_router() {
    // The router wraps like any inner theory — pinned, not assumed.
    // It forwards no FF theory propagation, so
    // its decision floor is documented-lower; soundness (never a
    // wrong verdict) is what this leg pins.
    run_grid_leg_with_floors(
        "lazy+router",
        RuntimeConfig { cdclt_multi_prime_router: true, ..RuntimeConfig::default() },
        8,
        4,
        2,
    );
}

#[test]
fn grid_ackermann_dnf() {
    run_grid_leg(
        "ackermann+dnf",
        RuntimeConfig {
            dnf_enabled: true,
            uf_mode: UfMode::Ackermann,
            ..RuntimeConfig::default()
        },
    );
}

#[test]
fn grid_lazy_cache_off() {
    run_grid_leg(
        "lazy+no-cache",
        RuntimeConfig { cache_enabled: false, ..RuntimeConfig::default() },
    );
}

#[test]
fn grid_lazy_linear_elim() {
    run_grid_leg(
        "lazy+linear-elim",
        RuntimeConfig { linear_elim: true, ..RuntimeConfig::default() },
    );
}

#[test]
fn grid_lazy_small_pair_cap() {
    run_grid_leg(
        "lazy+cap-2",
        RuntimeConfig { uf_pair_cap: 2, ..RuntimeConfig::default() },
    );
}

#[test]
fn lazy_and_ackermann_agree_modulo_unknown() {
    let mut rng = Lcg(0xA9EE);
    let mut compared = 0usize;
    for i in 0..60 {
        let p = if i % 2 == 0 { 5 } else { 7 };
        let cs = random_system(&mut rng, p);
        let lazy = {
            let _g = ConfigGuard::install(RuntimeConfig::default());
            IncrementalSolverContext::new().solve(&cs, &CancelToken::none())
        };
        let eager = {
            let _g = ConfigGuard::install(RuntimeConfig {
                uf_mode: UfMode::Ackermann,
                ..RuntimeConfig::default()
            });
            IncrementalSolverContext::new().solve(&cs, &CancelToken::none())
        };
        match (&lazy, &eager) {
            (SolveOutcome::Sat(_), SolveOutcome::Unsat(_))
            | (SolveOutcome::Unsat(_), SolveOutcome::Sat(_)) => {
                panic!("lazy/eager verdict contradiction on entry {}", i)
            }
            (SolveOutcome::Unknown(_), _) | (_, SolveOutcome::Unknown(_)) => {}
            _ => compared += 1,
        }
    }
    assert!(compared >= 45, "too few comparable entries: {}", compared);
}
