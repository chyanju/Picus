//! Manual performance benchmarks for the dense Buchberger engine
//! (F4 vs per-pair, Hilbert selection, reducer cache). All `#[ignore]`:
//! run with `cargo test -p picus-solver --release -- --ignored --nocapture`.

use num_bigint::BigUint;

/// F4 vs per-pair on workloads sized to expose F4's amortisation
/// benefit: larger ideals, more variables, and the cyclic-N family
/// (a standard GB benchmark that produces many same-sugar S-pair
/// batches).
///
/// Run manually:
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   bench_f4_vs_per_pair_large -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_vs_per_pair_large() {
    use crate::engine::buchberger::{BuchbergerConfig, IncrementalGB};
    use crate::engine::monomial::MonomialOrder;
    use crate::engine::polynomial::PolyRing;
    use crate::engine::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    /// `cyclic-N`: the N-variable cyclic ideal. Classical GB benchmark
    /// known to produce many same-sugar batches and a large basis.
    fn cyclic_n(n: usize, ring: &Arc<PolyRing>) -> Vec<crate::engine::polynomial::Polynomial> {
        use crate::engine::polynomial::Polynomial;
        let xs: Vec<Polynomial> = (0..n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys: Vec<Polynomial> = Vec::new();
        // f_d = sum over rotation r of (product x_{(r+0)..r+d})  for d = 1..n
        for d in 1..n {
            let mut acc = Polynomial::zero();
            for r in 0..n {
                let mut prod = xs[r % n].clone();
                for k in 1..d {
                    prod = prod.mul(&xs[(r + k) % n], ring);
                }
                acc = acc.add(&prod, ring);
            }
            polys.push(acc);
        }
        // f_n = x_0 * x_1 * ... * x_{n-1} - 1
        let mut p = xs[0].clone();
        for k in 1..n {
            p = p.mul(&xs[k], ring);
        }
        let one = ring.field.one();
        p = p.sub(&Polynomial::constant(one, ring), ring);
        polys.push(p);
        polys
    }

    fn run_one(
        polys: &[crate::engine::polynomial::Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
    ) -> u128 {
        let cfg = BuchbergerConfig {
            cancel_token: None,
            abort_on_trivial: false,
            use_f4,
            ..BuchbergerConfig::default()
        };
        let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
        let t = Instant::now();
        igb.add_generators(polys.iter().map(|p| p.as_dense(ring).into_owned()).collect())
            .expect("add_generators");
        t.elapsed().as_micros()
    }

    println!();
    println!(
        "{:<18} | {:>8} | {:>10} | {:>10} | {}",
        "workload", "n_polys", "pp_us", "f4_us", "f4/pp"
    );
    println!("{}", "-".repeat(70));

    let primes_and_orders: Vec<(BigUint, usize)> = vec![
        (BigUint::from(7919u32), 4), // cyclic-4
        (BigUint::from(7919u32), 5), // cyclic-5 (heavier)
        (BigUint::from(7919u32), 6), // cyclic-6 (more same-sugar batches)
    ];

    for (prime, n_vars) in &primes_and_orders {
        let names: Vec<String> = (0..*n_vars).map(|i| format!("x{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = cyclic_n(*n_vars, &ring);
        // Warm-up + 3 iterations, take median.
        let _ = run_one(&polys, &ring, false);
        let mut pp_times = Vec::new();
        for _ in 0..3 {
            pp_times.push(run_one(&polys, &ring, false));
        }
        pp_times.sort();
        let _ = run_one(&polys, &ring, true);
        let mut f4_times = Vec::new();
        for _ in 0..3 {
            f4_times.push(run_one(&polys, &ring, true));
        }
        f4_times.sort();
        let pp_med = pp_times[1];
        let f4_med = f4_times[1];
        let ratio = if pp_med == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4_med as f64 / pp_med as f64)
        };
        println!(
            "{:<18} | {:>8} | {:>10} | {:>10} | {}",
            format!("cyclic-{}", n_vars),
            polys.len(),
            pp_med,
            f4_med,
            ratio
        );
    }

    // Dense random ideals: large basis, many overlapping monomials.
    {
        let prime = BigUint::from(7919u32);
        let n_vars = 4usize;
        let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime),
            names,
            MonomialOrder::DegRevLex,
        );
        let mut seed = 42u64;
        let mut rand = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed
        };
        for &n_polys in &[10usize, 20, 30] {
            let mut polys = Vec::new();
            for _ in 0..n_polys {
                let mut acc = crate::engine::polynomial::Polynomial::zero();
                for _ in 0..6 {
                    let coeff = ((rand() % 7000) + 1) as i64;
                    let c = ring.field.from_int(coeff);
                    let i = (rand() as usize) % n_vars;
                    let j = (rand() as usize) % n_vars;
                    let xi = crate::engine::polynomial::Polynomial::variable(i, &ring);
                    let xj = crate::engine::polynomial::Polynomial::variable(j, &ring);
                    let term = xi.mul(&xj, &ring);
                    let scaled = term.mul(
                        &crate::engine::polynomial::Polynomial::constant(c, &ring),
                        &ring,
                    );
                    acc = acc.add(&scaled, &ring);
                }
                let cc = ring.field.from_int(((rand() % 7) + 1) as i64);
                let cp = crate::engine::polynomial::Polynomial::constant(cc, &ring);
                acc = acc.add(&cp, &ring);
                if !acc.is_zero() {
                    polys.push(acc);
                }
            }
            let _ = run_one(&polys, &ring, false);
            let mut pp_times = Vec::new();
            for _ in 0..3 {
                pp_times.push(run_one(&polys, &ring, false));
            }
            pp_times.sort();
            let _ = run_one(&polys, &ring, true);
            let mut f4_times = Vec::new();
            for _ in 0..3 {
                f4_times.push(run_one(&polys, &ring, true));
            }
            f4_times.sort();
            let pp_med = pp_times[1];
            let f4_med = f4_times[1];
            let ratio = if pp_med == 0 {
                "inf".to_string()
            } else {
                format!("{:.2}x", f4_med as f64 / pp_med as f64)
            };
            println!(
                "{:<18} | {:>8} | {:>10} | {:>10} | {}",
                format!("dense-{}-{}vars", n_polys, n_vars),
                polys.len(),
                pp_med,
                f4_med,
                ratio
            );
        }
    }
}

/// F4-vs-per-pair bench on non-cyclic GB families: Katsura-3,
/// Katsura-4, and a 4-variable ideal whose S-pair LCMs share
/// substructure. Coverage for the medium-batch regime that the
/// cyclic-N corpus does not exercise.
///
/// Prints per-run F4 batch counters (the test enables `gb_stats`
/// internally via `ConfigGuard`):
///
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   bench_f4_non_cyclic_workloads -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_non_cyclic_workloads() {
    use crate::engine::buchberger::{BuchbergerConfig, IncrementalGB};
    use crate::engine::monomial::MonomialOrder;
    use crate::engine::polynomial::{PolyRing, Polynomial};
    use crate::engine::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    // Emit the per-run GB-engine counters for the duration of this bench.
    let _stats = picus_core::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);

    /// Katsura(n) in `n+1` variables `u_0, …, u_n` (degrevlex):
    /// ```text
    ///   P_i = Σ_{j=-n..n} u_{|j|} · u_{|i-j|} - u_i   for 0 ≤ i ≤ n-1
    ///   P_n = Σ_{j=-n..n} u_{|j|} - 1
    /// ```
    // Standard Faugère Katsura-n (n+1 variables, ±j convolution). A
    // DIFFERENT ideal from `katsura_reduced_vars` below — the two used
    // to share one name, silently making their printed timings
    // incomparable.
    fn katsura_faugere(n: usize, ring: &Arc<PolyRing>) -> Vec<Polynomial> {
        let xs: Vec<Polynomial> = (0..=n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys: Vec<Polynomial> = Vec::new();
        let two = ring.field.from_int(2);
        let two_poly = Polynomial::constant(two.clone(), ring);
        for i in 0..n {
            let mut acc = Polynomial::zero();
            for j in -(n as i32)..=(n as i32) {
                let aj = (j.unsigned_abs()) as usize;
                let ak = ((i as i32 - j).unsigned_abs()) as usize;
                if aj > n || ak > n {
                    continue;
                }
                let prod = xs[aj].mul(&xs[ak], ring);
                acc = acc.add(&prod, ring);
            }
            acc = acc.sub(&xs[i], ring);
            polys.push(acc);
        }
        // P_n: u_0 + 2·u_1 + 2·u_2 + … + 2·u_n - 1
        let mut tail = xs[0].clone();
        for k in 1..=n {
            let scaled = xs[k].mul(&two_poly, ring);
            tail = tail.add(&scaled, ring);
        }
        let one = ring.field.one();
        tail = tail.sub(&Polynomial::constant(one, ring), ring);
        polys.push(tail);
        polys
    }

    /// 4-variable degree-2/4 ideal whose S-pair LCMs cluster inside
    /// a single sugar batch. LTs `(x·y, x·z, y·z, w·x, w·y, w·z,
    /// w·x·y·z)` give `lcm(f_1, f_2) = lcm(f_1, f_3) = lcm(f_2, f_3)
    /// = x·y·z` (three pairs sharing a degree-3 LCM) plus the
    /// symmetric block on `(w, x, y, z)`.
    fn diffuse_ideal(ring: &Arc<PolyRing>) -> Vec<Polynomial> {
        let w = Polynomial::variable(0, ring);
        let x = Polynomial::variable(1, ring);
        let y = Polynomial::variable(2, ring);
        let z = Polynomial::variable(3, ring);
        let one = ring.field.one();
        let const_one = Polynomial::constant(one.clone(), ring);
        let f1 = x.mul(&y, ring).sub(&z, ring);
        let f2 = x.mul(&z, ring).sub(&y, ring);
        let f3 = y.mul(&z, ring).sub(&x, ring);
        let f4 = w.mul(&x, ring).sub(&const_one, ring);
        let f5 = w.mul(&y, ring).sub(&z, ring);
        let f6 = w.mul(&z, ring).sub(&y, ring);
        let f7 = w.mul(&x, ring).mul(&y, ring).mul(&z, ring).sub(&const_one, ring);
        vec![f1, f2, f3, f4, f5, f6, f7]
    }

    fn run_one(
        polys: &[Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
    ) -> u128 {
        let cfg = BuchbergerConfig {
            cancel_token: None,
            abort_on_trivial: false,
            use_f4,
            ..BuchbergerConfig::default()
        };
        let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
        let t = Instant::now();
        igb.add_generators(polys.iter().map(|p| p.as_dense(ring).into_owned()).collect()).expect("add_generators");
        t.elapsed().as_micros()
    }

    fn median_times(polys: &[Polynomial], ring: &Arc<PolyRing>, use_f4: bool) -> u128 {
        // Warm-up + 3 measured runs; report the median.
        let _ = run_one(polys, ring, use_f4);
        let mut ts = Vec::new();
        for _ in 0..3 {
            ts.push(run_one(polys, ring, use_f4));
        }
        ts.sort();
        ts[1]
    }

    println!();
    println!(
        "{:<24} | {:>8} | {:>10} | {:>10} | {}",
        "workload", "n_polys", "pp_us", "f4_us", "f4/pp"
    );
    println!("{}", "-".repeat(76));

    let prime = BigUint::from(7919u32);

    // Katsura-3, Katsura-4. Average batch sizes straddle
    // `F4_MIN_BATCH = 12`.
    for n in [3usize, 4] {
        let names: Vec<String> = (0..=n).map(|i| format!("u{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = katsura_faugere(n, &ring);
        let pp = median_times(&polys, &ring, false);
        let f4 = median_times(&polys, &ring, true);
        let ratio = if pp == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4 as f64 / pp as f64)
        };
        println!(
            "{:<24} | {:>8} | {:>10} | {:>10} | {}",
            format!("katsura-faugere-{}", n),
            polys.len(),
            pp,
            f4,
            ratio,
        );
    }

    // 4-variable ideal whose S-pair LCMs share substructure across
    // pairs (subject to coprime / GM / B pruning).
    {
        let names: Vec<String> = ["w", "x", "y", "z"].iter().map(|s| s.to_string()).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = diffuse_ideal(&ring);
        let pp = median_times(&polys, &ring, false);
        let f4 = median_times(&polys, &ring, true);
        let ratio = if pp == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4 as f64 / pp as f64)
        };
        println!(
            "{:<24} | {:>8} | {:>10} | {:>10} | {}",
            "diffuse-4vars",
            polys.len(),
            pp,
            f4,
            ratio,
        );
    }
}

/// F4 vs per-pair geobucket: run the same workloads on both engines
/// in-process (via `IncrementalGB` with different `BuchbergerConfig`s)
/// and report median timings. Each arm builds its own `BuchbergerConfig`
/// with an explicit `use_f4`, independent of any global config.
///
/// Run manually:
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   bench_f4_vs_per_pair -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_vs_per_pair() {
    use crate::engine::buchberger::{BuchbergerConfig, IncrementalGB};
    use crate::engine::monomial::MonomialOrder;
    use crate::engine::polynomial::PolyRing;
    use crate::engine::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    /// Build a synthetic ideal of size `n_polys` over `n_vars`
    /// variables in F_p, degree ≤ 2. Deterministic via `seed`.
    fn build_system(
        n_vars: usize,
        n_polys: usize,
        seed: u64,
        ring: &Arc<PolyRing>,
    ) -> Vec<crate::engine::polynomial::Polynomial> {
        let mut s = seed;
        let mut rand = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        let mut out = Vec::new();
        for _ in 0..n_polys {
            let mut acc = crate::engine::polynomial::Polynomial::zero();
            for _ in 0..6 {
                let coeff = ((rand() % 7000) + 1) as i64;
                let c = ring.field.from_int(coeff);
                let i = (rand() as usize) % n_vars;
                let j = (rand() as usize) % n_vars;
                let xi = crate::engine::polynomial::Polynomial::variable(i, ring);
                let xj = crate::engine::polynomial::Polynomial::variable(j, ring);
                let term = xi.mul(&xj, ring);
                let scaled = term.mul(
                    &crate::engine::polynomial::Polynomial::constant(c, ring),
                    ring,
                );
                acc = acc.add(&scaled, ring);
            }
            let cc = ring.field.from_int(((rand() % 7) + 1) as i64);
            let cp = crate::engine::polynomial::Polynomial::constant(cc, ring);
            acc = acc.add(&cp, ring);
            if !acc.is_zero() {
                out.push(acc);
            }
        }
        out
    }

    fn time_one(
        polys: &[crate::engine::polynomial::Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
        iters: usize,
    ) -> (u128, bool) {
        let mut times = Vec::with_capacity(iters);
        let mut trivial = false;
        for _ in 0..iters {
            let cfg = BuchbergerConfig {
                cancel_token: None,
                abort_on_trivial: false,
                use_f4,
                ..BuchbergerConfig::default()
            };
            let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
            let t = Instant::now();
            trivial = igb
                .add_generators(polys.iter().map(|p| p.as_dense(ring).into_owned()).collect())
                .expect("add_generators");
            times.push(t.elapsed().as_micros());
        }
        times.sort();
        (times[iters / 2], trivial)
    }

    let prime = BigUint::from(7919u32); // first prime > 7000
    let names = vec!["x".into(), "y".into(), "z".into(), "w".into()];
    let ring = PolyRing::new(PrimeField::new(prime), names, MonomialOrder::DegRevLex);

    println!();
    println!(
        "{:<10} | {:>6} | {:>10} | {:>10} | {:>10} | {}",
        "n_polys", "seed", "pp_us", "f4_us", "f4/pp", "verdict"
    );
    println!("{}", "-".repeat(72));

    for n_polys in &[3usize, 5, 8, 12] {
        for seed in 1..=3u64 {
            let polys = build_system(4, *n_polys, seed, &ring);
            if polys.is_empty() {
                continue;
            }
            let iters = 5;
            let (pp_med, pp_trivial) = time_one(&polys, &ring, false, iters);
            let (f4_med, f4_trivial) = time_one(&polys, &ring, true, iters);
            assert_eq!(pp_trivial, f4_trivial,
                "verdict disagreement n_polys={} seed={}", n_polys, seed);
            let ratio = if pp_med == 0 {
                "inf".to_string()
            } else {
                format!("{:.2}x", f4_med as f64 / pp_med as f64)
            };
            let verdict = if pp_trivial { "trivial" } else { "ok" };
            println!(
                "{:<10} | {:>6} | {:>10} | {:>10} | {:>10} | {}",
                n_polys, seed, pp_med, f4_med, ratio, verdict
            );
        }
    }
}

/// Cyclic-N ratios for three F4 configurations:
///   1. per-pair (no F4)
///   2. F4 (sugar selection + cross-batch dense reducer cache off)
///   3. F4 + Hilbert select + sparse cross-batch reducer cache
///
/// Asserts that config 3's F4/pp ratio is no worse than config 2's
/// (i.e. the Hilbert oracle + sparse cache do not regress the cyclic
/// benchmarks).
///
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   audit_p3_cyclic_n_hilbert_and_sparse_cache_do_not_regress \
///   -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn audit_p3_cyclic_n_hilbert_and_sparse_cache_do_not_regress() {
    use crate::engine::buchberger::{BuchbergerConfig, IncrementalGB};
    use crate::engine::monomial::MonomialOrder;
    use crate::engine::polynomial::PolyRing;
    use crate::engine::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    fn cyclic_n(n: usize, ring: &Arc<PolyRing>) -> Vec<crate::engine::polynomial::Polynomial> {
        use crate::engine::polynomial::Polynomial;
        let xs: Vec<Polynomial> = (0..n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys: Vec<Polynomial> = Vec::new();
        for d in 1..n {
            let mut acc = Polynomial::zero();
            for r in 0..n {
                let mut prod = xs[r % n].clone();
                for k in 1..d {
                    prod = prod.mul(&xs[(r + k) % n], ring);
                }
                acc = acc.add(&prod, ring);
            }
            polys.push(acc);
        }
        let mut p = xs[0].clone();
        for k in 1..n {
            p = p.mul(&xs[k], ring);
        }
        let one = ring.field.one();
        p = p.sub(&Polynomial::constant(one, ring), ring);
        polys.push(p);
        polys
    }

    fn run_one(
        polys: &[crate::engine::polynomial::Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
    ) -> u128 {
        let cfg = BuchbergerConfig {
            cancel_token: None,
            abort_on_trivial: false,
            use_f4,
            ..BuchbergerConfig::default()
        };
        let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
        let t = Instant::now();
        igb.add_generators(polys.iter().map(|p| p.as_dense(ring).into_owned()).collect())
            .expect("add_generators");
        t.elapsed().as_micros()
    }

    println!();
    println!(
        "{:<10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10}",
        "workload", "pp_us", "f4_us", "f4_h_us", "f4/pp", "f4_h/pp"
    );
    println!("{}", "-".repeat(75));

    let configs: Vec<(BigUint, usize)> = vec![
        (BigUint::from(7919u32), 4),
        (BigUint::from(7919u32), 5),
        (BigUint::from(7919u32), 6),
    ];

    for (prime, n_vars) in &configs {
        let names: Vec<String> = (0..*n_vars).map(|i| format!("x{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = cyclic_n(*n_vars, &ring);

        // (1) per-pair, default config.
        let pp_med = {
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, false);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, false)); }
            ts.sort();
            ts[1]
        };
        // (2) F4 with default config (f4_hilbert_select=off, f4_sparse_reducer_cache=off).
        let f4_med = {
            let _guard = picus_core::config::ConfigGuard::with_override(|c| {
                c.f4_hilbert_select = false;
                c.f4_sparse_reducer_cache = false;
            });
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, true);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, true)); }
            ts.sort();
            ts[1]
        };
        // (3) F4 with Hilbert select + sparse reducer cache ON.
        let f4_h_med = {
            let _guard = picus_core::config::ConfigGuard::with_override(|c| {
                c.f4_hilbert_select = true;
                c.f4_sparse_reducer_cache = true;
            });
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, true);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, true)); }
            ts.sort();
            ts[1]
        };
        let f4_ratio = f4_med as f64 / pp_med as f64;
        let f4_h_ratio = f4_h_med as f64 / pp_med as f64;
        println!(
            "{:<10} | {:>10} | {:>10} | {:>10} | {:>9.2}x | {:>9.2}x",
            format!("cyclic-{}", n_vars),
            pp_med, f4_med, f4_h_med, f4_ratio, f4_h_ratio
        );
        // Acceptance gate: Hilbert+sparse should not make F4
        // materially worse than the sugar-classical F4 path. Allow a
        // 20% noise band — the cyclic-N timings are noisy enough at
        // µs scale that a strict comparison fires false negatives.
        assert!(
            f4_h_ratio <= f4_ratio * 1.20 + 0.05,
            "cyclic-{}: Hilbert+sparse F4 (ratio {:.2}x) regressed >20% vs sugar F4 (ratio {:.2}x)",
            n_vars, f4_h_ratio, f4_ratio
        );
    }

    // Katsura-N: heterogeneous workload mixing a degree-1 linear
    // constraint with quadratic generators, so `self.open` carries
    // multiple sugar levels during the F4 main loop and the Hilbert
    // oracle has a real choice to rank instead of the single-sugar
    // batch cyclic-N produces. Definition (Faugère normalisation):
    //   u_n = 2 * (u_1 + u_2 + ... + u_{n-1}) + u_0,  u_0 + u_n = 1
    //   for k = 1..n-1: sum_{i+j=k, |i|,|j|≤n} u_|i| * u_|j| = u_k
    fn katsura_reduced_vars(n: usize, ring: &Arc<PolyRing>) -> Vec<crate::engine::polynomial::Polynomial> {
        use crate::engine::polynomial::Polynomial;
        // u_i is stored at index i (0..n).
        let us: Vec<Polynomial> = (0..n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys = Vec::new();
        let one = Polynomial::constant(ring.field.one(), ring);
        // Normalisation: u_0 + 2 * (u_1 + ... + u_{n-1}) − 1 = 0.
        let mut norm = us[0].clone();
        for i in 1..n {
            let two = ring.field.from_u64(2);
            let two_poly = Polynomial::constant(two, ring);
            norm = norm.add(&two_poly.mul(&us[i], ring), ring);
        }
        norm = norm.sub(&one, ring);
        polys.push(norm);
        // Quadratic relations for k = 0..n-2.
        for k in 0..(n - 1) {
            let mut acc = Polynomial::zero();
            for i in (-(n as isize - 1))..=(n as isize - 1) {
                let j = k as isize - i;
                if j < -(n as isize - 1) || j > (n as isize - 1) {
                    continue;
                }
                let ui = us[i.unsigned_abs()].clone();
                let uj = us[j.unsigned_abs()].clone();
                acc = acc.add(&ui.mul(&uj, ring), ring);
            }
            acc = acc.sub(&us[k], ring);
            polys.push(acc);
        }
        polys
    }

    println!();
    println!(
        "{:<10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10}",
        "workload", "pp_us", "f4_us", "f4_h_us", "f4/pp", "f4_h/pp"
    );
    println!("{}", "-".repeat(75));
    for &n_vars in &[4usize, 5] {
        let names: Vec<String> = (0..n_vars).map(|i| format!("u{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(BigUint::from(7919u32)),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = katsura_reduced_vars(n_vars, &ring);
        let pp_med = {
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, false);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, false)); }
            ts.sort();
            ts[1]
        };
        let f4_med = {
            let _guard = picus_core::config::ConfigGuard::with_override(|c| {
                c.f4_hilbert_select = false;
                c.f4_sparse_reducer_cache = false;
            });
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, true);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, true)); }
            ts.sort();
            ts[1]
        };
        let f4_h_med = {
            let _guard = picus_core::config::ConfigGuard::with_override(|c| {
                c.f4_hilbert_select = true;
                c.f4_sparse_reducer_cache = true;
            });
            let mut ts = Vec::new();
            let _ = run_one(&polys, &ring, true);
            for _ in 0..3 { ts.push(run_one(&polys, &ring, true)); }
            ts.sort();
            ts[1]
        };
        let f4_ratio = f4_med as f64 / pp_med as f64;
        let f4_h_ratio = f4_h_med as f64 / pp_med as f64;
        println!(
            "{:<10} | {:>10} | {:>10} | {:>10} | {:>9.2}x | {:>9.2}x",
            format!("katsura-reduced-{}", n_vars),
            pp_med, f4_med, f4_h_med, f4_ratio, f4_h_ratio
        );
        assert!(
            f4_h_ratio <= f4_ratio * 1.20 + 0.05,
            "katsura-reduced-{}: Hilbert+sparse F4 (ratio {:.2}x) regressed >20% vs sugar F4 (ratio {:.2}x)",
            n_vars, f4_h_ratio, f4_ratio
        );
    }
}
