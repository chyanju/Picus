//! End-to-end tests for `PolyIR::check_uniqueness` — the IR-native path into
//! the DPVL uniqueness analysis (two-copy lowering + propagation), reachable
//! without conversion to R1CS.

use picus::ir::PolyIR;
use picus::{CheckResult, PicusConfig};

#[test]
fn determined_output_is_safe() {
    // y = x*x over GF(7). Given input x, output y is uniquely determined, so
    // the two-copy search cannot make y differ across copies ⇒ Safe.
    let mut s = PolyIR::new(7u32);
    let [x, y] = s.vars(["x", "y"]);
    s.eq(y, x * x);
    s.field_polys(true);

    let r = s
        .check_uniqueness(&[x], &[y], &[], PicusConfig::default())
        .unwrap();
    assert!(matches!(r, CheckResult::Safe), "expected Safe, got {r:?}");
}

#[test]
fn underconstrained_output_is_unsafe() {
    // x = a*b over GF(7), with x an input and a an output. Given x, `a` is not
    // uniquely determined (e.g. x = 0 admits a = 0 or a = 1 with suitable b),
    // so the analysis finds a two-witness counter-example differing on `a`.
    let mut s = PolyIR::new(7u32);
    let [x, a, b] = s.vars(["x", "a", "b"]);
    s.eq(x, a * b);
    s.field_polys(true);

    let r = s
        .check_uniqueness(&[x], &[a], &[], PicusConfig::default())
        .unwrap();
    match r {
        CheckResult::Unsafe {
            witness_1,
            witness_2,
        } => {
            let a1 = witness_1.get("a").expect("witness_1 carries output `a`");
            let a2 = witness_2.get("a").expect("witness_2 carries output `a`");
            assert_ne!(a1, a2, "the two witnesses must differ on the checked output");
        }
        other => panic!("expected Unsafe, got {other:?}"),
    }
}

#[test]
fn known_signal_seed_makes_dependent_output_safe() {
    // z = w, with w an output and z an output; seeding `w` as known lets the
    // analysis conclude z is determined too. Sanity-check the `known` channel
    // is plumbed through (Safe either way here, but exercises the argument).
    let mut s = PolyIR::new(7u32);
    let [x, w, z] = s.vars(["x", "w", "z"]);
    s.eq(w, x);
    s.eq(z, w);
    s.field_polys(true);

    let r = s
        .check_uniqueness(&[x], &[w, z], &[w], PicusConfig::default())
        .unwrap();
    assert!(matches!(r, CheckResult::Safe), "expected Safe, got {r:?}");
}
