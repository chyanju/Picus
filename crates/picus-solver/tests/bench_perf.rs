//! Performance benchmarks for picus-solver.
//! Run with: cargo test -p picus-solver --test bench_perf --release -- --ignored --nocapture

use picus_solver::solve::{solve_encoded, SolveOutcome};
mod common;
use common::{NamedSystem, NamedTerm};
use picus_core::ff::monomial::MonomialOrder;
use picus_core::timeout::CancelToken;
use picus_solver::gb::ideal::{compute_gb_with_order, GbOutcome};
use num_bigint::BigUint;
use num_traits::One;
use std::time::Instant;

fn pterm(coeff: u64, vars: &[&str]) -> NamedTerm {
    NamedTerm { coeff: BigUint::from(coeff), vars: vars.iter().map(|s| s.to_string()).collect() }
}

fn bn128_prime() -> BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
}

/// Benchmark: IsZero uniqueness over BN128 field
#[test]
#[ignore] // run manually with --ignored
fn bench_is_zero_bn128() {
    let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
    let pm1 = &p - BigUint::one();

    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pterm(1, &["m", "x"]), pterm(1, &["iz"]), NamedTerm { coeff: pm1.clone(), vars: vec![] }],
            vec![pterm(1, &["iz", "x"])],
            vec![pterm(1, &["mp", "x"]), pterm(1, &["izp"]), NamedTerm { coeff: pm1.clone(), vars: vec![] }],
            vec![pterm(1, &["izp", "x"])],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };

    let start = Instant::now();
    let encoded = system.encode().unwrap();
    let encode_time = start.elapsed();

    let start = Instant::now();
    let result = compute_gb_with_order(
        &encoded.poly_ring,
        encoded.polynomials,
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_time = start.elapsed();

    println!("BN128 IsZero uniqueness:");
    println!("  Encoding: {:?}", encode_time);
    println!("  GB computation: {:?}", gb_time);
    println!("  Total: {:?}", encode_time + gb_time);
    println!("  Result: {}", match result {
        GbOutcome::Basis(ref gb)
            if gb.iter().any(|p| !encoded.poly_ring.is_zero(p) && p.is_constant()) =>
        {
            "UNSAT"
        }
        GbOutcome::Basis(_) => "SAT/UNKNOWN",
        GbOutcome::Cancelled | GbOutcome::Failed => "TIMEOUT/FAILED",
    });
}

/// Benchmark: Multiple constraints over GF(17)
#[test]
#[ignore]
fn bench_multi_constraint_gf17() {
    let p = BigUint::from(17u32);

    // 5 binary constraints + sum constraint
    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pterm(1, &["b0", "b0"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b0".into()] }],
            vec![pterm(1, &["b1", "b1"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b1".into()] }],
            vec![pterm(1, &["b2", "b2"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b2".into()] }],
            vec![pterm(1, &["b3", "b3"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b3".into()] }],
            // s = b0 + 2*b1 + 4*b2 + 8*b3
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["s".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b0".into()] },
                NamedTerm { coeff: BigUint::from(15u32), vars: vec!["b1".into()] },
                NamedTerm { coeff: BigUint::from(13u32), vars: vec!["b2".into()] },
                NamedTerm { coeff: BigUint::from(9u32), vars: vec!["b3".into()] },
            ],
            // same for alt
            vec![pterm(1, &["b0p", "b0p"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b0p".into()] }],
            vec![pterm(1, &["b1p", "b1p"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b1p".into()] }],
            vec![pterm(1, &["b2p", "b2p"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b2p".into()] }],
            vec![pterm(1, &["b3p", "b3p"]), NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b3p".into()] }],
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["sp".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec!["b0p".into()] },
                NamedTerm { coeff: BigUint::from(15u32), vars: vec!["b1p".into()] },
                NamedTerm { coeff: BigUint::from(13u32), vars: vec!["b2p".into()] },
                NamedTerm { coeff: BigUint::from(9u32), vars: vec!["b3p".into()] },
            ],
        ],
        disequalities: vec![("s".into(), "sp".into())],
        assignments: vec![
            ("b0".into(), BigUint::one()),
            ("b1".into(), BigUint::from(0u32)),
            ("b2".into(), BigUint::one()),
            ("b3".into(), BigUint::from(0u32)),
            ("b0p".into(), BigUint::one()),
            ("b1p".into(), BigUint::from(0u32)),
            ("b2p".into(), BigUint::one()),
            ("b3p".into(), BigUint::from(0u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };

    let start = Instant::now();
    let encoded = system.encode().unwrap();
    let result = compute_gb_with_order(
        &encoded.poly_ring,
        encoded.polynomials,
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let total = start.elapsed();

    println!("GF(17) bit decomposition uniqueness:");
    println!("  Total: {:?}", total);
    println!("  Result: {}", match result {
        GbOutcome::Basis(ref gb)
            if gb.iter().any(|p| !encoded.poly_ring.is_zero(p) && p.is_constant()) =>
        {
            "UNSAT"
        }
        GbOutcome::Basis(_) => "SAT/UNKNOWN",
        GbOutcome::Cancelled | GbOutcome::Failed => "TIMEOUT/FAILED",
    });
}

/// Build a k-bit decomposition system over BN128:
///   - K bit constraints `b_i*(b_i - 1) = 0`
///   - one bitsum equality `b_0 + 2*b_1 + ... + 2^{K-1}*b_{K-1} - target = 0`
fn bitdecomp_bn128_system(k: usize, target: u64) -> NamedSystem {
    let p = bn128_prime();
    let pm1 = &p - BigUint::one();
    let mut equalities: Vec<Vec<NamedTerm>> = Vec::new();
    for i in 0..k {
        let bi = format!("b{}", i);
        equalities.push(vec![
            NamedTerm { coeff: BigUint::one(), vars: vec![bi.clone(), bi.clone()] },
            NamedTerm { coeff: pm1.clone(), vars: vec![bi] },
        ]);
    }
    let mut sum: Vec<NamedTerm> = Vec::with_capacity(k + 1);
    let mut coeff = BigUint::one();
    let two = BigUint::from(2u32);
    for i in 0..k {
        sum.push(NamedTerm { coeff: coeff.clone(), vars: vec![format!("b{}", i)] });
        coeff = (&coeff * &two) % &p;
    }
    sum.push(NamedTerm { coeff: &p - BigUint::from(target), vars: vec![] });
    equalities.push(sum);
    NamedSystem {
        prime: p,
        equalities,
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    }
}

fn time_solve_median(cs: &NamedSystem, iters: usize) -> (u128, &'static str) {
    let mut total_times: Vec<u128> = Vec::with_capacity(iters);
    let mut verdict = "unknown";
    for _ in 0..iters {
        let t = Instant::now();
        let enc = cs.encode().unwrap();
        let out = solve_encoded(&enc);
        total_times.push(t.elapsed().as_micros());
        verdict = match out {
            SolveOutcome::Sat(_) => "sat",
            SolveOutcome::Unsat(_) => "unsat",
            SolveOutcome::Unknown(_) => "unknown",
        };
    }
    total_times.sort();
    (total_times[iters / 2], verdict)
}

/// Bitdecomp solve timing across K ∈ {6, 8, 10, 12}. Marked `#[ignore]`:
/// `encode` runs `auto_extract_bitsums` unconditionally, so there is no
/// on/off toggle to compare against.
#[test]
#[ignore]
fn bench_bitdecomp_auto_extract() {
    let iters = 3;
    println!("{:>3} | {:>12} | {:<7} | {:>14}", "K", "target", "verdict", "us");
    println!("{}", "-".repeat(46));
    for &k in &[6usize, 8, 10, 12] {
        let target = if k < 64 { (1u64 << k) - 3 } else { (1u64 << 32) - 3 };
        let cs = bitdecomp_bn128_system(k, target);
        let (t, v) = time_solve_median(&cs, iters);
        println!("{:>3} | {:>12} | {:<7} | {:>14}", k, target, v, t);
    }
}




