//! Ring-free symbolic algebra for the [`crate::ir`] API: `Var`, `Expr`,
//! `Value`, `Constraint`, and the operator/`From` overloads that make natural
//! `x*x - 1` syntax build a normalized polynomial over `Z` (signed, unreduced —
//! the modular reduction happens only at lowering time).
//!
//! An [`Expr`] is a canonical sparse sum of monomials: `terms` is sorted by
//! monomial with every coefficient nonzero, and each monomial is a sorted
//! `Vec<(var_idx, exp)>` (empty == the constant term). Every operation
//! re-canonicalises, so equal expressions have equal `terms`.

use std::collections::BTreeMap;
use std::num::NonZeroU64;
use std::sync::atomic::{AtomicU64, Ordering};

use num_bigint::{BigInt, BigUint, Sign};

// ─────────────────────────────────────────────────────────────────────────
// SystemId — a process-wide nonce tying a `Var`/`Expr` to the `PolyIR` that
// minted it, so mixing handles from two different systems panics loudly.
// ─────────────────────────────────────────────────────────────────────────

static NEXT_SYSTEM_ID: AtomicU64 = AtomicU64::new(1);

/// Opaque per-`PolyIR` identity. Every [`PolyIR`](crate::ir::PolyIR) gets a
/// fresh one at construction; [`Var`] and [`Expr`] carry it so cross-system
/// mixing is caught. Crate-internal: it is unconstructable and unusable from
/// outside, so it is not part of the public surface.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct SystemId(NonZeroU64);

impl SystemId {
    /// Allocate the next process-wide-unique id.
    pub(crate) fn fresh() -> SystemId {
        let n = NEXT_SYSTEM_ID.fetch_add(1, Ordering::Relaxed);
        SystemId(NonZeroU64::new(n).expect("SystemId counter overflowed u64"))
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Var
// ─────────────────────────────────────────────────────────────────────────

/// A handle to a variable in a specific [`PolyIR`](crate::ir::PolyIR). `Copy`,
/// so it can be used freely in expressions.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Var {
    pub(crate) sys: SystemId,
    pub(crate) idx: u32,
}

impl Var {
    /// Build the constraint `self == rhs`.
    pub fn equals(self, rhs: impl Into<Expr>) -> Constraint {
        Expr::from(self).equals(rhs)
    }

    /// `self` raised to `exp` as an [`Expr`] (`exp == 0` ⇒ the constant `1`).
    pub fn pow(self, exp: u32) -> Expr {
        Expr::from(self).pow(exp)
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Expr
// ─────────────────────────────────────────────────────────────────────────

/// A ring-free symbolic polynomial over `Z`: a canonical sparse sum of
/// monomials with signed, unreduced coefficients. Modular reduction over GF(p)
/// happens only when a [`PolyIR`](crate::ir::PolyIR) lowers it.
#[derive(Clone, Debug, Default)]
pub struct Expr {
    /// The owning system, or `None` for a pure constant (which adopts the
    /// other operand's system when combined).
    pub(crate) sys: Option<SystemId>,
    /// Monomials paired with coefficients. Sorted by monomial; every
    /// coefficient nonzero; the empty monomial is the constant term.
    pub(crate) terms: Vec<(Vec<(u32, u32)>, BigInt)>,
}

impl Expr {
    /// `x` as an expression (coefficient `+1`, degree `1`).
    pub(crate) fn from_var(v: Var) -> Expr {
        Expr {
            sys: Some(v.sys),
            terms: vec![(vec![(v.idx, 1)], BigInt::from(1))],
        }
    }

    /// A pure constant expression (no owning system).
    pub(crate) fn from_bigint(c: BigInt) -> Expr {
        if c.sign() == Sign::NoSign {
            Expr { sys: None, terms: Vec::new() }
        } else {
            Expr { sys: None, terms: vec![(Vec::new(), c)] }
        }
    }

    /// Build the constraint `self == rhs`.
    pub fn equals(self, rhs: impl Into<Expr>) -> Constraint {
        Constraint(self.sub_expr(rhs.into()))
    }

    /// `self` raised to `exp` (`exp == 0` ⇒ the constant `1`).
    pub fn pow(&self, exp: u32) -> Expr {
        if exp == 0 {
            return Expr::from_bigint(BigInt::from(1));
        }
        let mut acc = self.clone();
        for _ in 1..exp {
            acc = acc.mul_expr(self.clone());
        }
        acc
    }

    /// True iff `self` has no variable terms (constant or zero).
    pub fn is_constant(&self) -> bool {
        self.terms.iter().all(|(mono, _)| mono.is_empty())
    }

    /// `Some(v)` iff `self` is exactly the bare variable `x_v` — a single term
    /// `1 * x_v` of degree 1 and no constant. Used to route `ne` onto the
    /// native disequality primitive.
    pub(crate) fn as_bare_var(&self) -> Option<u32> {
        if self.terms.len() != 1 {
            return None;
        }
        let (mono, coeff) = &self.terms[0];
        if mono.len() == 1 && mono[0].1 == 1 && *coeff == BigInt::from(1) {
            Some(mono[0].0)
        } else {
            None
        }
    }

    // ── internal ring-free arithmetic ──────────────────────────────────

    fn add_expr(self, other: Expr) -> Expr {
        let sys = unify_sys(self.sys, other.sys);
        let mut map: BTreeMap<Vec<(u32, u32)>, BigInt> = BTreeMap::new();
        for (mono, coeff) in self.terms.into_iter().chain(other.terms) {
            *map.entry(mono).or_insert_with(|| BigInt::from(0)) += coeff;
        }
        Expr { sys, terms: canonical(map) }
    }

    fn neg_expr(self) -> Expr {
        Expr {
            sys: self.sys,
            terms: self.terms.into_iter().map(|(m, c)| (m, -c)).collect(),
        }
    }

    fn sub_expr(self, other: Expr) -> Expr {
        self.add_expr(other.neg_expr())
    }

    fn mul_expr(self, other: Expr) -> Expr {
        let sys = unify_sys(self.sys, other.sys);
        let mut map: BTreeMap<Vec<(u32, u32)>, BigInt> = BTreeMap::new();
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                let mono = merge_mono(m1, m2);
                *map.entry(mono).or_insert_with(|| BigInt::from(0)) += c1 * c2;
            }
        }
        Expr { sys, terms: canonical(map) }
    }
}

/// Turn a monomial→coefficient map into a canonical term list: sorted by
/// monomial (`BTreeMap` order) with all zero coefficients dropped.
fn canonical(map: BTreeMap<Vec<(u32, u32)>, BigInt>) -> Vec<(Vec<(u32, u32)>, BigInt)> {
    map.into_iter()
        .filter(|(_, c)| c.sign() != Sign::NoSign)
        .collect()
}

/// Combine the owning systems of two operands: two differing `Some`s are a
/// cross-system mix and panic; otherwise the concrete one (if any) wins.
fn unify_sys(a: Option<SystemId>, b: Option<SystemId>) -> Option<SystemId> {
    match (a, b) {
        (Some(x), Some(y)) => {
            assert!(x == y, "cannot combine handles from different PolyIR systems");
            Some(x)
        }
        (Some(x), None) => Some(x),
        (None, other) => other,
    }
}

/// Multiply two sorted `(var, exp)` monomials, summing exponents of shared
/// variables. Inputs are sorted by var index; output stays sorted.
fn merge_mono(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

// ─────────────────────────────────────────────────────────────────────────
// Value & Constraint
// ─────────────────────────────────────────────────────────────────────────

/// A signed scalar, used only as the right-hand side of
/// [`PolyIR::assign`](crate::ir::PolyIR::assign).
#[derive(Clone, Debug)]
pub struct Value(pub(crate) BigInt);

/// A constraint. Invariant: the wrapped [`Expr`] must equal zero. `l == r`
/// lowers to `l - r`; a bare `Var`/`Expr`/integer means `that == 0`.
pub struct Constraint(pub(crate) Expr);

// ─────────────────────────────────────────────────────────────────────────
// `From` conversions
// ─────────────────────────────────────────────────────────────────────────

impl From<Var> for Expr {
    fn from(v: Var) -> Expr {
        Expr::from_var(v)
    }
}
impl From<&Var> for Expr {
    fn from(v: &Var) -> Expr {
        Expr::from_var(*v)
    }
}
impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Expr {
        e.clone()
    }
}

macro_rules! expr_from_int {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for Expr {
            fn from(v: $t) -> Expr { Expr::from_bigint(BigInt::from(v)) }
        }
    )*};
}
expr_from_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl From<BigInt> for Expr {
    fn from(v: BigInt) -> Expr {
        Expr::from_bigint(v)
    }
}
impl From<BigUint> for Expr {
    fn from(v: BigUint) -> Expr {
        Expr::from_bigint(BigInt::from(v))
    }
}
impl From<&BigUint> for Expr {
    fn from(v: &BigUint) -> Expr {
        Expr::from_bigint(BigInt::from(v.clone()))
    }
}

macro_rules! value_from_int {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for Value {
            fn from(v: $t) -> Value { Value(BigInt::from(v)) }
        }
    )*};
}
value_from_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl From<BigInt> for Value {
    fn from(v: BigInt) -> Value {
        Value(v)
    }
}
impl From<BigUint> for Value {
    fn from(v: BigUint) -> Value {
        Value(BigInt::from(v))
    }
}
impl From<&BigUint> for Value {
    fn from(v: &BigUint) -> Value {
        Value(BigInt::from(v.clone()))
    }
}

impl From<Expr> for Constraint {
    fn from(e: Expr) -> Constraint {
        Constraint(e)
    }
}
impl From<Var> for Constraint {
    fn from(v: Var) -> Constraint {
        Constraint(Expr::from(v))
    }
}

macro_rules! constraint_from_int {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for Constraint {
            fn from(v: $t) -> Constraint { Constraint(Expr::from(v)) }
        }
    )*};
}
constraint_from_int!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

// ─────────────────────────────────────────────────────────────────────────
// Operator overloading
// ─────────────────────────────────────────────────────────────────────────

macro_rules! impl_neg {
    ($t:ty, $conv:expr) => {
        impl std::ops::Neg for $t {
            type Output = Expr;
            fn neg(self) -> Expr {
                let e: Expr = $conv(self);
                e.neg_expr()
            }
        }
    };
}
impl_neg!(Expr, |e: Expr| e);
impl_neg!(&Expr, |e: &Expr| e.clone());
impl_neg!(Var, |v: Var| Expr::from(v));
impl_neg!(&Var, |v: &Var| Expr::from(v));

/// For each of `Add`/`Sub`/`Mul`, a generic `impl<R: Into<Expr>>` for each
/// owned/borrowed `Expr`/`Var` left-hand side.
macro_rules! impl_bin_owner {
    ($trait:ident, $method:ident, $call:ident) => {
        impl<R: Into<Expr>> std::ops::$trait<R> for Expr {
            type Output = Expr;
            fn $method(self, rhs: R) -> Expr {
                Expr::from(self).$call(rhs.into())
            }
        }
        impl<R: Into<Expr>> std::ops::$trait<R> for &Expr {
            type Output = Expr;
            fn $method(self, rhs: R) -> Expr {
                Expr::from(self).$call(rhs.into())
            }
        }
        impl<R: Into<Expr>> std::ops::$trait<R> for Var {
            type Output = Expr;
            fn $method(self, rhs: R) -> Expr {
                Expr::from(self).$call(rhs.into())
            }
        }
        impl<R: Into<Expr>> std::ops::$trait<R> for &Var {
            type Output = Expr;
            fn $method(self, rhs: R) -> Expr {
                Expr::from(self).$call(rhs.into())
            }
        }
    };
}
impl_bin_owner!(Add, add, add_expr);
impl_bin_owner!(Sub, sub, sub_expr);
impl_bin_owner!(Mul, mul, mul_expr);

/// Integer literals on the *left*: `2 * x`, `2 + x`, `2 - x`. Orphan-legal
/// because the right-hand side (`Var`/`&Var`/`Expr`/`&Expr`) is our local type.
macro_rules! impl_bin_int_lhs {
    ($trait:ident, $method:ident, $call:ident, $($int:ty),* $(,)?) => {$(
        impl std::ops::$trait<Var> for $int {
            type Output = Expr;
            fn $method(self, rhs: Var) -> Expr { Expr::from(self).$call(Expr::from(rhs)) }
        }
        impl std::ops::$trait<&Var> for $int {
            type Output = Expr;
            fn $method(self, rhs: &Var) -> Expr { Expr::from(self).$call(Expr::from(rhs)) }
        }
        impl std::ops::$trait<Expr> for $int {
            type Output = Expr;
            fn $method(self, rhs: Expr) -> Expr { Expr::from(self).$call(rhs) }
        }
        impl std::ops::$trait<&Expr> for $int {
            type Output = Expr;
            fn $method(self, rhs: &Expr) -> Expr { Expr::from(self).$call(Expr::from(rhs)) }
        }
    )*};
}
impl_bin_int_lhs!(Add, add, add_expr, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
impl_bin_int_lhs!(Sub, sub, sub_expr, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
impl_bin_int_lhs!(Mul, mul, mul_expr, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    fn sysid() -> SystemId {
        SystemId::fresh()
    }

    #[test]
    fn constant_normalizes_zero() {
        let e = Expr::from(0i32);
        assert!(e.terms.is_empty());
        assert!(e.is_constant());
    }

    #[test]
    fn like_terms_combine() {
        let id = sysid();
        let x = Var { sys: id, idx: 0 };
        // x + x == 2*x
        let e = x + x;
        assert_eq!(e.terms, vec![(vec![(0u32, 1u32)], BigInt::from(2))]);
        // x - x == 0
        let z = x - x;
        assert!(z.terms.is_empty());
    }

    #[test]
    fn mul_merges_exponents() {
        let id = sysid();
        let x = Var { sys: id, idx: 0 };
        let e = x.pow(2); // x*x
        assert_eq!(e.terms, vec![(vec![(0u32, 2u32)], BigInt::from(1))]);
    }

    #[test]
    fn bare_var_detection() {
        let id = sysid();
        let x = Var { sys: id, idx: 3 };
        assert_eq!(Expr::from(x).as_bare_var(), Some(3));
        assert_eq!((x + 1i32).as_bare_var(), None);
        assert_eq!((2i32 * x).as_bare_var(), None);
        assert_eq!(x.pow(2).as_bare_var(), None);
    }

    #[test]
    #[should_panic(expected = "different PolyIR")]
    fn cross_system_mul_panics() {
        let a = Var { sys: sysid(), idx: 0 };
        let b = Var { sys: sysid(), idx: 0 };
        let _ = a * b;
    }
}
