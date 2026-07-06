//! Never-wrong-verdict harness across the engine knob grid.
//!
//! Ground truth comes from exhaustive point enumeration of the encoded
//! system over small fields (GF(7) / GF(17)), so it is independent of
//! every solver code path. Each corpus entry is then solved under a
//! grid of configs — every conjunctive-path-live knob flipped away from
//! its default one at a time, plus multi-knob combinations — and the
//! verdict must equal the ground truth **or** be Unknown; the opposite
//! verdict is a soundness bug in that configuration. Sat models are
//! re-evaluated against the encoded polynomials.
//!
//! Knobs that the conjunctive `solve_encoded` entry never consults
//! (`cache_enabled`, `linear_elim`, `membership_fastpath`, the `cdclt_*`
//! trio, `dnf_*`) are exercised at their own consumer seams by other
//! suites; this grid covers the solve-core knobs.

mod common;

use std::collections::HashMap;

use num_bigint::BigUint;
use picus_core::config::{ConfigGuard, GbStrategy, ReprKind, RuntimeConfig};
use picus_core::timeout::CancelToken;
use picus_solver::{EncodedSystem, SolveOutcome};

use common::{ct, pt, svt, vt, NamedSystem};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Truth {
    Sat,
    Unsat,
}

/// Exhaustively enumerate all points of the encoded ring and decide
/// satisfiability of `polynomials ∪ bitsum_polys`. The encoded ring
/// includes Rabinowitsch witnesses and bitsum auxiliaries, so this is
/// the exact semantics of what `solve_encoded` decides.
fn enumerate_truth(encoded: &EncodedSystem) -> Truth {
    let pr = &encoded.poly_ring;
    let fp = pr.field();
    let n = pr.n_vars();
    let p: u64 = fp
        .prime()
        .to_string()
        .parse()
        .expect("corpus primes are small");
    let total = (p as u128).checked_pow(n as u32).expect("point count");
    assert!(
        total <= 2_000_000,
        "corpus entry too large for exhaustive enumeration: {}^{}",
        p,
        n
    );

    let all_polys: Vec<&picus_core::poly::Poly> = encoded
        .polynomials
        .iter()
        .chain(encoded.bitsum_polys.iter())
        .collect();

    let mut point: Vec<u64> = vec![0; n];
    loop {
        let elems: Vec<_> = point.iter().map(|&v| fp.from_int(v as i64)).collect();
        let mut all_zero = true;
        for poly in &all_polys {
            let mut acc = fp.zero();
            for (c, m) in pr.ring.terms(poly) {
                let mut t = fp.clone_el(c);
                for v in 0..n {
                    let e = pr.ring.exponent_at(&m, v);
                    for _ in 0..e {
                        t = fp.mul_ref(&t, &elems[v]);
                    }
                }
                fp.add_assign(&mut acc, t);
            }
            if !fp.is_zero(&acc) {
                all_zero = false;
                break;
            }
        }
        if all_zero {
            return Truth::Sat;
        }
        // Odometer increment.
        let mut i = 0;
        loop {
            if i == n {
                return Truth::Unsat;
            }
            point[i] += 1;
            if point[i] < p {
                break;
            }
            point[i] = 0;
            i += 1;
        }
    }
}

/// Evaluate every encoded polynomial under a name-keyed model; all must
/// vanish and every ring variable must be bound (the solver's contract
/// is a total model).
fn model_satisfies(encoded: &EncodedSystem, model: &HashMap<String, BigUint>) -> Result<(), String> {
    let pr = &encoded.poly_ring;
    let fp = pr.field();
    let n = pr.n_vars();
    let mut elems = Vec::with_capacity(n);
    for name in pr.var_names() {
        match model.get(name) {
            Some(v) => elems.push(fp.from_biguint(v)),
            None => return Err(format!("model missing variable {}", name)),
        }
    }
    for poly in encoded.polynomials.iter().chain(encoded.bitsum_polys.iter()) {
        let mut acc = fp.zero();
        for (c, m) in pr.ring.terms(poly) {
            let mut t = fp.clone_el(c);
            for v in 0..n {
                let e = pr.ring.exponent_at(&m, v);
                for _ in 0..e {
                    t = fp.mul_ref(&t, &elems[v]);
                }
            }
            fp.add_assign(&mut acc, t);
        }
        if !fp.is_zero(&acc) {
            return Err("model does not zero an encoded polynomial".into());
        }
    }
    Ok(())
}

fn sys(prime: u64) -> NamedSystem {
    let mut s = NamedSystem::new(BigUint::from(prime));
    s.add_field_polys = true;
    s
}

fn neg(prime: u64, c: u64) -> u64 {
    (prime - (c % prime)) % prime
}

/// Pinned fixtures with hand-checkable semantics.
fn pinned_corpus() -> Vec<(String, NamedSystem)> {
    let mut out: Vec<(String, NamedSystem)> = Vec::new();

    // GF(7): x + y - 3 = 0 (SAT).
    let mut s = sys(7);
    s.equalities.push(vec![vt("x"), vt("y"), ct(neg(7, 3))]);
    out.push(("sat-linear".into(), s));

    // GF(7): x - 1 = 0 and x - 2 = 0 (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![vt("x"), ct(neg(7, 1))]);
    s.equalities.push(vec![vt("x"), ct(neg(7, 2))]);
    out.push(("unsat-two-values".into(), s));

    // GF(7): x^2 - x = 0 and x - 1 = 0 (SAT).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "x"]), svt(neg(7, 1), "x")]);
    s.equalities.push(vec![vt("x"), ct(neg(7, 1))]);
    out.push(("sat-bit-pinned".into(), s));

    // GF(7): x^2 - x = 0 and x - 2 = 0 (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "x"]), svt(neg(7, 1), "x")]);
    s.equalities.push(vec![vt("x"), ct(neg(7, 2))]);
    out.push(("unsat-bit-pinned".into(), s));

    // GF(7): x*y - 1 = 0 and x - 2 = 0 (SAT: y = 4).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "y"]), ct(neg(7, 1))]);
    s.equalities.push(vec![vt("x"), ct(neg(7, 2))]);
    out.push(("sat-inverse".into(), s));

    // GF(7): x*y - 1 = 0 and x = 0 (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "y"]), ct(neg(7, 1))]);
    s.equalities.push(vec![vt("x")]);
    out.push(("unsat-zero-inverse".into(), s));

    // GF(7): x^2 - 2 = 0 (SAT: 3, 4).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "x"]), ct(neg(7, 2))]);
    out.push(("sat-residue".into(), s));

    // GF(7): x^2 - 3 = 0 (UNSAT: 3 is a non-residue mod 7).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "x"]), ct(neg(7, 3))]);
    out.push(("unsat-nonresidue".into(), s));

    // GF(7): x*y - 1 = 0 with x != y (SAT: x=2, y=4).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "y"]), ct(neg(7, 1))]);
    s.disequalities.push(("x".into(), "y".into()));
    out.push(("sat-diseq".into(), s));

    // GF(7): x = 3, y = 3, x != y (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![vt("x"), ct(neg(7, 3))]);
    s.equalities.push(vec![vt("y"), ct(neg(7, 3))]);
    s.disequalities.push(("x".into(), "y".into()));
    out.push(("unsat-diseq".into(), s));

    // GF(7): bits b0, b1 with b0 + 2*b1 - 3 = 0 (SAT: b0=1, b1=1).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["b0", "b0"]), svt(neg(7, 1), "b0")]);
    s.equalities.push(vec![pt(1, &["b1", "b1"]), svt(neg(7, 1), "b1")]);
    s.equalities
        .push(vec![vt("b0"), svt(2, "b1"), ct(neg(7, 3))]);
    out.push(("sat-bitsum".into(), s));

    // GF(7): bits b0, b1 with b0 + 2*b1 - 5 = 0 (UNSAT: range is 0..=3).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["b0", "b0"]), svt(neg(7, 1), "b0")]);
    s.equalities.push(vec![pt(1, &["b1", "b1"]), svt(neg(7, 1), "b1")]);
    s.equalities
        .push(vec![vt("b0"), svt(2, "b1"), ct(neg(7, 5))]);
    out.push(("unsat-bitsum".into(), s));

    // GF(17): x^2 + y^2 - 2 = 0 and x - 1 = 0 (SAT: y = ±1).
    let mut s = sys(17);
    s.equalities.push(vec![
        pt(1, &["x", "x"]),
        pt(1, &["y", "y"]),
        ct(neg(17, 2)),
    ]);
    s.equalities.push(vec![vt("x"), ct(neg(17, 1))]);
    out.push(("sat-circle-gf17".into(), s));

    // GF(17): x^2 - 3 = 0 (UNSAT: 3 is a non-residue mod 17).
    let mut s = sys(17);
    s.equalities.push(vec![pt(1, &["x", "x"]), ct(neg(17, 3))]);
    out.push(("unsat-nonresidue-gf17".into(), s));

    // GF(7): x + y + z - 1 = 0 and x*y - z = 0 (SAT: x=0, y=1, z=0).
    let mut s = sys(7);
    s.equalities
        .push(vec![vt("x"), vt("y"), vt("z"), ct(neg(7, 1))]);
    s.equalities
        .push(vec![pt(1, &["x", "y"]), svt(neg(7, 1), "z")]);
    out.push(("sat-three-vars".into(), s));

    // GF(7): x + y - 1 = 0 and x + y - 2 = 0 (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![vt("x"), vt("y"), ct(neg(7, 1))]);
    s.equalities.push(vec![vt("x"), vt("y"), ct(neg(7, 2))]);
    out.push(("unsat-parallel".into(), s));

    // GF(7): x^3 - 1 = 0 (SAT: 1, 2, 4).
    let mut s = sys(7);
    s.equalities
        .push(vec![pt(1, &["x", "x", "x"]), ct(neg(7, 1))]);
    out.push(("sat-cubic".into(), s));

    // GF(7): x^2 - x = 0, y - x = 0, y^2 + 1 = 0 (UNSAT).
    let mut s = sys(7);
    s.equalities.push(vec![pt(1, &["x", "x"]), svt(neg(7, 1), "x")]);
    s.equalities.push(vec![vt("y"), svt(neg(7, 1), "x")]);
    s.equalities.push(vec![pt(1, &["y", "y"]), ct(1)]);
    out.push(("unsat-bit-image".into(), s));

    out
}

/// Deterministic LCG (same recipe as the parity suite's corpus).
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 33
}

/// Seeded random small systems: 2-3 variables, 2-3 polynomials of
/// degree <= 2, sometimes a pinned assignment or a disequality.
fn random_corpus() -> Vec<(String, NamedSystem)> {
    let mut out = Vec::new();
    for seed in 0..25u64 {
        let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(11);
        let prime: u64 = if seed % 2 == 0 { 7 } else { 17 };
        let n_vars = 2 + (lcg(&mut state) % 2) as usize; // 2..=3
        let names: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
        let mut s = sys(prime);
        let n_polys = 2 + (lcg(&mut state) % 2) as usize; // 2..=3
        for _ in 0..n_polys {
            let n_terms = 1 + (lcg(&mut state) % 3) as usize; // 1..=3
            let mut eq = Vec::new();
            for _ in 0..n_terms {
                let coeff = 1 + lcg(&mut state) % (prime - 1);
                let deg = (lcg(&mut state) % 3) as usize; // 0..=2
                let vars: Vec<&str> = (0..deg)
                    .map(|_| names[(lcg(&mut state) as usize) % n_vars].as_str())
                    .collect();
                let mut term = pt(1, &vars);
                term.coeff = BigUint::from(coeff);
                eq.push(term);
            }
            s.equalities.push(eq);
        }
        if lcg(&mut state) % 2 == 0 {
            let v = (lcg(&mut state) as usize) % n_vars;
            let val = lcg(&mut state) % prime;
            s.equalities
                .push(vec![vt(&names[v]), ct(neg(prime, val))]);
        }
        if n_vars >= 2 && lcg(&mut state) % 3 == 0 {
            s.disequalities
                .push((names[0].clone(), names[1].clone()));
        }
        out.push((format!("rand-{}", seed), s));
    }
    out
}

/// The knob grid: every conjunctive-path-live knob flipped away from
/// its default (enum knobs get one entry per non-default variant),
/// plus multi-knob combinations.
fn grid() -> Vec<(&'static str, RuntimeConfig)> {
    let mut out: Vec<(&'static str, RuntimeConfig)> = Vec::new();
    let base = RuntimeConfig::default;

    let mut c = base();
    out.push(("default", c.clone()));

    c = base();
    c.gb_strategy = GbStrategy::ByHomog;
    out.push(("gb_strategy=by-homog", c.clone()));

    c = base();
    c.gb_strategy = GbStrategy::Auto;
    out.push(("gb_strategy=auto", c.clone()));

    c = base();
    c.use_f4 = true;
    out.push(("use_f4", c.clone()));

    c = base();
    c.poly_repr = ReprKind::Dense;
    out.push(("poly_repr=dense", c.clone()));

    c = base();
    c.split_triangular = true;
    out.push(("split_triangular", c.clone()));

    c = base();
    c.radical_membership = true;
    out.push(("radical_membership", c.clone()));

    c = base();
    c.matrix_elim_order = true;
    out.push(("matrix_elim_order", c.clone()));

    c = base();
    c.dynamic_order = false;
    out.push(("dynamic_order=off", c.clone()));

    c = base();
    c.zech_log_small_fp = true;
    out.push(("zech_log_small_fp", c.clone()));

    c = base();
    c.reducer_index_cache = true;
    out.push(("reducer_index_cache", c.clone()));

    c = base();
    c.frobenius_cache = false;
    out.push(("frobenius_cache=off", c.clone()));

    c = base();
    c.branching_incremental_gb = false;
    out.push(("branching_incremental_gb=off", c.clone()));

    // The F4 sub-knobs are dense-engine-only, so their off-legs are
    // paired with poly_repr=dense to actually execute on the main solve.
    c = base();
    c.use_f4 = true;
    c.poly_repr = ReprKind::Dense;
    c.f4_hilbert_select = false;
    out.push(("f4+dense+hilbert_select=off", c.clone()));

    c = base();
    c.use_f4 = true;
    c.poly_repr = ReprKind::Dense;
    c.f4_sparse_reducer_cache = false;
    out.push(("f4+dense+sparse_reducer_cache=off", c.clone()));

    c = base();
    c.profile_enabled = true;
    out.push(("profile_enabled", c.clone()));

    c = base();
    c.use_f4 = true;
    c.poly_repr = ReprKind::Dense;
    out.push(("use_f4+dense", c.clone()));

    // Multi-knob combinations.
    c = base();
    c.poly_repr = ReprKind::Dense;
    c.use_f4 = true;
    c.reducer_index_cache = true;
    out.push(("dense+f4+reducer_index_cache", c.clone()));

    c = base();
    c.gb_strategy = GbStrategy::ByHomog;
    c.poly_repr = ReprKind::Dense;
    out.push(("by-homog+dense", c.clone()));

    c = base();
    c.split_triangular = true;
    c.branching_incremental_gb = false;
    out.push(("split_triangular+branching_incr=off", c.clone()));

    c = base();
    c.matrix_elim_order = true;
    c.poly_repr = ReprKind::Dense;
    out.push(("matrix_elim_order+dense", c.clone()));

    c = base();
    c.dynamic_order = false;
    c.frobenius_cache = false;
    c.zech_log_small_fp = true;
    out.push(("dynamic=off+frobenius=off+zech", c));

    out
}

#[test]
fn knob_grid_never_wrong_verdict() {
    let mut corpus = pinned_corpus();
    corpus.extend(random_corpus());

    // Ground truth from the default-config encoding, computed once per
    // corpus entry (verdicts are encoding-invariant).
    let mut truths: Vec<(String, NamedSystem, Truth)> = Vec::new();
    {
        let _guard = ConfigGuard::install(RuntimeConfig::default());
        for (name, s) in corpus {
            let encoded = s.encode().expect("encode");
            let truth = enumerate_truth(&encoded);
            truths.push((name, s, truth));
        }
    }
    let n_sat = truths.iter().filter(|(_, _, t)| *t == Truth::Sat).count();
    let n_unsat = truths.len() - n_sat;
    // Anti-vacuity floor: the corpus must exercise both verdicts.
    assert!(n_sat >= 10, "corpus skew: only {} SAT cases", n_sat);
    assert!(n_unsat >= 8, "corpus skew: only {} UNSAT cases", n_unsat);

    let mut checked = 0usize;
    let mut unknowns = 0usize;
    for (cfg_name, cfg) in grid() {
        let _guard = ConfigGuard::install(cfg);
        for (case_name, s, truth) in &truths {
            // Re-encode under this config: the encoder itself reads
            // order/representation knobs.
            let encoded = s.encode().expect("encode");
            let cancel = CancelToken::with_timeout(std::time::Duration::from_secs(2));
            let outcome = picus_solver::solve_encoded_with_cancel(&encoded, &cancel);
            match outcome {
                SolveOutcome::Sat(model) => {
                    assert_eq!(
                        *truth,
                        Truth::Sat,
                        "[{}] {}: solver returned Sat but exhaustive enumeration \
                         proves UNSAT — wrong verdict",
                        cfg_name,
                        case_name
                    );
                    if let Err(e) = model_satisfies(&encoded, &model) {
                        panic!(
                            "[{}] {}: Sat model rejected: {}",
                            cfg_name, case_name, e
                        );
                    }
                }
                SolveOutcome::Unsat(_) => {
                    assert_eq!(
                        *truth,
                        Truth::Unsat,
                        "[{}] {}: solver returned Unsat but exhaustive enumeration \
                         found a model — wrong verdict",
                        cfg_name,
                        case_name
                    );
                }
                SolveOutcome::Unknown(_) => {
                    // Always sound; tracked so a config that degrades the
                    // whole corpus to Unknown cannot pass silently.
                    unknowns += 1;
                }
            }
            checked += 1;
        }
    }
    // Anti-vacuity floor: at most a third of all (config, case) runs may
    // degrade to Unknown; beyond that the grid is not testing verdicts.
    assert!(
        unknowns * 3 <= checked,
        "{} of {} grid runs returned Unknown — harness lost its teeth",
        unknowns,
        checked
    );
}
