//! End-to-end tests for the ergonomic `picus::ir` API.

use num_bigint::BigUint;
use picus::ir::PolyIR;
use picus::{IrError, Solution};

fn bu(n: u32) -> BigUint {
    BigUint::from(n)
}

#[test]
fn headline_example() {
    // GF(7): x^2 - x = 0 pins x ∈ {0,1}; y = 1; x ≠ y forces x = 0.
    let mut s = PolyIR::new(7u32);
    let [x, y] = s.vars(["x", "y"]);
    s.eq(x * x - x, 0);
    s.eq(y, 1);
    s.ne(x, y);
    s.field_polys(true);

    let sol = s.solve().unwrap();
    assert!(sol.is_sat(), "expected Sat, got a non-Sat verdict");
    let m = sol.model().unwrap();
    assert_eq!(m[x], bu(0), "x should be pinned to 0");
    assert_eq!(m["y"], bu(1), "y should be 1");
}

#[test]
fn unsat_conflicting_assignments() {
    // x = 3 and x = 5 over GF(7) is contradictory.
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    s.eq(x, 3);
    s.eq(x, 5);
    assert!(matches!(s.solve().unwrap(), Solution::Unsat));
}

#[test]
fn expression_level_ne_unsat() {
    // 3*3 = 9 = 2 (mod 7), so x*x == 2 and `ne(x*x, 2)` is violated.
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    s.eq(x, 3);
    s.ne(x * x, 2);
    s.field_polys(true);
    assert!(matches!(s.solve().unwrap(), Solution::Unsat));
}

#[test]
fn expression_level_ne_sat() {
    // x*x = 2 != 3, so `ne(x*x, 3)` holds; x = 3 is a witness.
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    s.eq(x, 3);
    s.ne(x * x, 3);
    s.field_polys(true);

    let sol = s.solve().unwrap();
    assert!(sol.is_sat());
    assert_eq!(sol.model().unwrap()[x], bu(3));
}

#[test]
fn ops_compile_matrix() {
    // Purely a compile check: every documented operator shape must build.
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    let y = s.var("y");

    let _ = x * x;
    let _ = &x * &x;
    let _ = 2 * x;
    let _ = x - 1;
    let _ = x.pow(3);
    let _ = -x;
    let _ = (x + y) - (x - y);
    let _ = 2 * x + 3 * y - 5;
    let _ = &x + y;
    let _ = 2 + x;
    let _ = 2 - x;
    let _ = (x * x) * y; // expr * var
    let _ = (x + 1) * (y + 1); // expr * expr
    let _ = -(&x);

    // Nothing to assert; reaching here means all the impls resolved.
}

#[test]
fn model_handle_and_name_agree() {
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    // A Rabinowitsch disequality mints a hidden `__aux0` witness.
    s.eq(x, 3);
    s.ne(x * x, 3);
    s.field_polys(true);

    let sol = s.solve().unwrap();
    let m = sol.model().unwrap();

    // Handle-indexed and name-indexed lookups agree.
    assert_eq!(m[x], m["x"].clone());
    assert_eq!(m.get(x), m.name("x"));
    assert_eq!(m.u64(x), Some(3));

    // iter() exposes only user variables, never `__aux*`.
    let keys: Vec<&str> = m.iter().map(|(k, _)| k).collect();
    assert!(keys.contains(&"x"), "user var x missing from iter()");
    assert!(
        !keys.iter().any(|k| k.starts_with("__")),
        "iter() leaked an auxiliary variable: {keys:?}"
    );
}

#[test]
fn assign_and_or_and_bitsum_build_and_solve() {
    let mut s = PolyIR::new(7u32);
    let [a, b] = s.vars(["a", "b"]);
    s.assign(a, 2u32);
    // a == 2, so (a - 2 == 0) satisfies the disjunction.
    s.or([a - 2, b - 5]);
    s.field_polys(true);

    let sol = s.solve().unwrap();
    assert!(sol.is_sat());
    assert_eq!(sol.model().unwrap()[a], bu(2));
}

#[test]
fn try_var_rejects_duplicate_and_reserved() {
    let mut s = PolyIR::new(7u32);
    let _x = s.var("x");
    assert!(matches!(s.try_var("x"), Err(IrError::DuplicateVar(_))));
    assert!(matches!(s.try_var("__secret"), Err(IrError::ReservedName(_))));
    assert!(s.try_var("y").is_ok());
}

#[test]
fn var_is_idempotent() {
    let mut s = PolyIR::new(7u32);
    let x1 = s.var("x");
    let x2 = s.var("x");
    assert_eq!(x1, x2);
}

#[test]
fn from_prime_str_parsing() {
    assert!(PolyIR::from_prime_str("7").is_ok());
    assert!(matches!(
        PolyIR::from_prime_str("not-a-prime"),
        Err(IrError::BadPrime(_))
    ));
}

#[test]
fn lower_is_reachable() {
    // Power-user bridge: lowering yields a usable PolySystem over the ring.
    let mut s = PolyIR::new(7u32);
    let x = s.var("x");
    s.eq(x, 3);
    let ps = s.lower();
    assert_eq!(ps.ring.n_vars(), 1);
    assert_eq!(ps.equalities.len(), 1);
}

#[test]
#[should_panic(expected = "different PolyIR")]
fn cross_system_use_panics() {
    let mut s1 = PolyIR::new(7u32);
    let mut s2 = PolyIR::new(7u32);
    let x = s1.var("x");
    let y = s2.var("y");
    // Mixing handles from two systems must panic.
    let _ = x + y;
}
