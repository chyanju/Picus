//! Ergonomic, ring-free API for building and solving a polynomial constraint
//! system over GF(p).
//!
//! Build a [`PolyIR`] for a prime, mint [`Var`]s, and assemble constraints with
//! natural Rust operators — `x*x - x`, `2*x + 3*y - 5`, `x.pow(3)` — then
//! [`assert`](PolyIR::assert) / [`eq`](PolyIR::eq) / [`ne`](PolyIR::ne) / … and
//! [`solve`](PolyIR::solve). The low-level `Arc`/ring/`Poly` machinery stays
//! hidden; the only bridge to it is [`PolyIR::lower`].
//!
//! ```
//! use picus::ir::PolyIR;
//! use num_bigint::BigUint;
//!
//! let mut s = PolyIR::new(7u32);
//! let [x, y] = s.vars(["x", "y"]);
//! s.eq(x * x - x, 0);   // x ∈ {0, 1}
//! s.eq(y, 1);
//! s.ne(x, y);           // x ≠ y ⇒ x = 0
//! s.field_polys(true);
//!
//! let sol = s.solve().unwrap();
//! let m = sol.model().unwrap();
//! assert_eq!(m[x], BigUint::from(0u32));
//! assert_eq!(m["y"], BigUint::from(1u32));
//! ```

mod expr;
mod lower;

pub use expr::{Constraint, Expr, Value, Var};
pub(crate) use expr::SystemId;

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;

use crate::{PicusConfig, SolverResult, UnknownReason};

// ─────────────────────────────────────────────────────────────────────────
// Errors
// ─────────────────────────────────────────────────────────────────────────

/// Errors surfaced by the [`crate::ir`] API.
#[derive(Debug, thiserror::Error)]
pub enum IrError {
    /// [`PolyIR::try_var`] was given a name that already exists.
    #[error("duplicate variable name: {0}")]
    DuplicateVar(String),
    /// A user tried to declare a variable with the reserved `"__"` prefix,
    /// which is kept for auxiliary variables.
    #[error("reserved variable name (\"__\" prefix): {0}")]
    ReservedName(String),
    /// [`PolyIR::from_prime_str`] could not parse its argument as a decimal.
    #[error("invalid prime string: {0}")]
    BadPrime(String),
    /// The underlying solver returned an error.
    #[error(transparent)]
    Solver(#[from] crate::SolveError),
}

// ─────────────────────────────────────────────────────────────────────────
// PolyIR
// ─────────────────────────────────────────────────────────────────────────

/// A polynomial constraint system over GF(p). Build it with [`Self::new`],
/// declare variables, add constraints, and [`solve`](Self::solve).
pub struct PolyIR {
    id: SystemId,
    prime: BigUint,
    names: Vec<String>,
    name_index: HashMap<String, u32>,
    eqs: Vec<Expr>,
    ors: Vec<Vec<Expr>>,
    diseq_vars: Vec<(u32, u32)>,
    assigns: Vec<(u32, Value)>,
    bitsums: Vec<Vec<u32>>,
    add_field_polys: bool,
    aux_ctr: u32,
}

impl PolyIR {
    /// A fresh, empty system over GF(`prime`). Accepts `7u32`, `7u64`, a
    /// [`BigUint`], etc. The prime is trusted, not verified.
    pub fn new(prime: impl Into<BigUint>) -> Self {
        PolyIR {
            id: SystemId::fresh(),
            prime: prime.into(),
            names: Vec::new(),
            name_index: HashMap::new(),
            eqs: Vec::new(),
            ors: Vec::new(),
            diseq_vars: Vec::new(),
            assigns: Vec::new(),
            bitsums: Vec::new(),
            add_field_polys: false,
            aux_ctr: 0,
        }
    }

    /// Like [`Self::new`] but parses the prime from a decimal string.
    pub fn from_prime_str(decimal: &str) -> Result<Self, IrError> {
        let prime: BigUint = decimal
            .parse()
            .map_err(|_| IrError::BadPrime(decimal.to_string()))?;
        Ok(Self::new(prime))
    }

    /// Declare (or look up) a variable by name. Idempotent: the same name
    /// always returns the same handle. Panics on a reserved `"__"`-prefixed
    /// name (use [`Self::try_var`] for a fallible variant).
    pub fn var(&mut self, name: impl Into<String>) -> Var {
        let name = name.into();
        if let Some(&idx) = self.name_index.get(&name) {
            return Var { sys: self.id, idx };
        }
        assert!(
            !name.starts_with("__"),
            "reserved variable name (\"__\" prefix): {name}"
        );
        self.intern(name)
    }

    /// Fallible [`Self::var`]: `Err` on a duplicate or reserved (`"__"`-prefix)
    /// name rather than reusing / panicking.
    pub fn try_var(&mut self, name: impl Into<String>) -> Result<Var, IrError> {
        let name = name.into();
        if name.starts_with("__") {
            return Err(IrError::ReservedName(name));
        }
        if self.name_index.contains_key(&name) {
            return Err(IrError::DuplicateVar(name));
        }
        Ok(self.intern(name))
    }

    /// Declare `N` variables at once: `let [x, y] = s.vars(["x", "y"]);`.
    pub fn vars<const N: usize>(&mut self, names: [&str; N]) -> [Var; N] {
        names.map(|n| self.var(n))
    }

    /// Mint a fresh auxiliary variable with a unique reserved name
    /// (`"__aux{n}"`). Internal: used for Rabinowitsch witnesses. Not part of
    /// the public builder surface (would otherwise let callers bypass the
    /// reserved-`__`-name guard that `var`/`try_var` enforce).
    pub(crate) fn fresh_var(&mut self) -> Var {
        let name = format!("__aux{}", self.aux_ctr);
        self.aux_ctr += 1;
        self.intern(name)
    }

    /// Append a name to the table and return its handle. Assumes the name is
    /// new (callers pre-check).
    fn intern(&mut self, name: String) -> Var {
        let idx = self.names.len() as u32;
        self.name_index.insert(name.clone(), idx);
        self.names.push(name);
        Var { sys: self.id, idx }
    }

    /// Panic if an expression belongs to a different system.
    fn check_sys(&self, sys: Option<SystemId>) {
        if let Some(s) = sys {
            assert!(
                s == self.id,
                "expression was built from a different PolyIR system"
            );
        }
    }

    /// Panic if a variable handle belongs to a different system.
    fn check_var(&self, var: Var) {
        assert!(
            var.sys == self.id,
            "variable handle was minted by a different PolyIR system"
        );
    }

    /// Assert a constraint (`c == 0`, or `l == r` via [`Var::equals`] /
    /// [`Expr::equals`]).
    pub fn assert(&mut self, c: impl Into<Constraint>) -> &mut Self {
        let e = c.into().0;
        self.check_sys(e.sys);
        self.eqs.push(e);
        self
    }

    /// Assert `lhs == rhs`.
    pub fn eq(&mut self, lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> &mut Self {
        let e = lhs.into() - rhs.into();
        self.check_sys(e.sys);
        self.eqs.push(e);
        self
    }

    /// Assert `lhs != rhs`. When both sides are bare variables this uses the
    /// native disequality primitive; otherwise it encodes a Rabinowitsch
    /// witness `(lhs - rhs) * w - 1 == 0`.
    pub fn ne(&mut self, lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> &mut Self {
        let le = lhs.into();
        let re = rhs.into();
        self.check_sys(le.sys);
        self.check_sys(re.sys);
        match (le.as_bare_var(), re.as_bare_var()) {
            (Some(a), Some(b)) => {
                self.diseq_vars.push((a, b));
            }
            _ => {
                let w = self.fresh_var();
                let poly = (le - re) * w - 1;
                self.check_sys(poly.sys);
                self.eqs.push(poly);
            }
        }
        self
    }

    /// Pin `var` to `value` (emits `var - value == 0`).
    pub fn assign(&mut self, var: Var, value: impl Into<Value>) -> &mut Self {
        self.check_var(var);
        self.assigns.push((var.idx, value.into()));
        self
    }

    /// Assert a disjunction: at least one clause must hold. Each clause is
    /// anything convertible to a [`Constraint`] (an `Expr`/`Var`/integer means
    /// `that == 0`).
    pub fn or<C: Into<Constraint>, I: IntoIterator<Item = C>>(&mut self, clauses: I) -> &mut Self {
        let mut clause = Vec::new();
        for c in clauses {
            let e = c.into().0;
            self.check_sys(e.sys);
            clause.push(e);
        }
        self.ors.push(clause);
        self
    }

    /// Declare a bitsum chain over `bits` (each an auxiliary
    /// `sum(2^i · bit_i)`).
    pub fn bitsum<I: IntoIterator<Item = Var>>(&mut self, bits: I) -> &mut Self {
        let idxs: Vec<u32> = bits
            .into_iter()
            .map(|v| {
                self.check_var(v);
                v.idx
            })
            .collect();
        self.bitsums.push(idxs);
        self
    }

    /// Opt into field polynomials `x^p - x = 0` for exact reasoning over small
    /// primes (the encoder still gates on `prime <= 1000`).
    pub fn field_polys(&mut self, on: bool) -> &mut Self {
        self.add_field_polys = on;
        self
    }

    /// Solve with the default configuration.
    pub fn solve(&self) -> Result<Solution, IrError> {
        self.solve_with(PicusConfig::default())
    }

    /// Solve with an explicit [`PicusConfig`].
    pub fn solve_with(&self, cfg: PicusConfig) -> Result<Solution, IrError> {
        let ps = lower::lower(self);
        Ok(match crate::solve_system(&ps, cfg)? {
            SolverResult::Unsat => Solution::Unsat,
            SolverResult::Sat(map) => Solution::Sat(Model {
                vals: map,
                names: self.names.clone().into(),
                sys: self.id,
            }),
            SolverResult::Unknown(reason) => Solution::Unknown(reason),
        })
    }

    /// Lower to a raw [`PolySystem`] — the bridge to the low-level machinery.
    pub fn lower(&self) -> picus_smt::poly_system::PolySystem {
        lower::lower(self)
    }

    /// Check whether `outputs` are uniquely determined by `inputs` under this
    /// system's constraints, using the full DPVL uniqueness analysis (two-copy
    /// lowering + propagation lemmas) rather than the bare solver
    /// [`Self::solve`] runs.
    ///
    /// `inputs` are shared across the two witnesses; `outputs` are the signals
    /// whose determinism is tested; `known` optionally seeds wires already
    /// believed unique (pass `&[]` if none). All handles must come from this
    /// system. Returns [`Safe`](crate::CheckResult::Safe) when every output is
    /// forced equal across both copies, [`Unsafe`](crate::CheckResult::Unsafe)
    /// with the two witnesses (keyed by variable name) when a counter-example
    /// exists, or [`Unknown`](crate::CheckResult::Unknown).
    pub fn check_uniqueness(
        &self,
        inputs: &[Var],
        outputs: &[Var],
        known: &[Var],
        cfg: PicusConfig,
    ) -> Result<crate::CheckResult, crate::PicusError> {
        crate::check_polyir_uniqueness(self, inputs, outputs, known, cfg)
    }

    /// Validate that `var` belongs to this system and return its ring index.
    pub(crate) fn var_index(&self, var: Var) -> usize {
        self.check_var(var);
        var.idx as usize
    }

    /// Rename a witness map keyed by the doubled ring's `x{i}` / `y{i}` names
    /// back to this system's user-facing names (both copies of wire `i` map to
    /// `names[i]`), dropping auxiliary `__`-prefixed variables.
    pub(crate) fn rename_witness(
        &self,
        m: HashMap<String, BigUint>,
    ) -> HashMap<String, BigUint> {
        let mut out = HashMap::new();
        for (k, v) in m {
            if let Some(i) = picus_r1cs::parse_var_index(&k) {
                if let Some(name) = self.names.get(i) {
                    if !name.starts_with("__") {
                        out.insert(name.clone(), v);
                    }
                }
            }
        }
        out
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Solution & Model
// ─────────────────────────────────────────────────────────────────────────

/// The verdict from [`PolyIR::solve`].
pub enum Solution {
    /// The system is unsatisfiable.
    Unsat,
    /// The system is satisfiable, with a witness [`Model`].
    Sat(Model),
    /// The solver could not decide the query.
    Unknown(UnknownReason),
}

impl Solution {
    /// True iff this is [`Solution::Sat`].
    pub fn is_sat(&self) -> bool {
        matches!(self, Solution::Sat(_))
    }

    /// Borrow the model, if satisfiable.
    pub fn model(&self) -> Option<&Model> {
        match self {
            Solution::Sat(m) => Some(m),
            _ => None,
        }
    }

    /// Take the model, if satisfiable.
    pub fn into_model(self) -> Option<Model> {
        match self {
            Solution::Sat(m) => Some(m),
            _ => None,
        }
    }
}

/// A satisfying assignment: variable name → field-element value.
pub struct Model {
    vals: HashMap<String, BigUint>,
    names: Arc<[String]>,
    sys: SystemId,
}

impl Model {
    /// Look up a variable's value by handle. Panics if `var` came from a
    /// different system.
    pub fn get(&self, var: Var) -> Option<&BigUint> {
        assert!(
            var.sys == self.sys,
            "variable handle was minted by a different PolyIR system"
        );
        let name = self.names[var.idx as usize].as_str();
        self.vals.get(name)
    }

    /// Look up a variable's value as a `u64`, if it fits.
    pub fn u64(&self, var: Var) -> Option<u64> {
        self.get(var).and_then(biguint_to_u64)
    }

    /// Look up a value by variable name.
    pub fn name(&self, name: &str) -> Option<&BigUint> {
        self.vals.get(name)
    }

    /// Iterate over user variables (those without the reserved `"__"` prefix).
    pub fn iter(&self) -> impl Iterator<Item = (&str, &BigUint)> {
        self.vals
            .iter()
            .filter(|(k, _)| !k.starts_with("__"))
            .map(|(k, v)| (k.as_str(), v))
    }

    /// Consume into the raw name → value map (including auxiliary variables).
    pub fn into_raw(self) -> HashMap<String, BigUint> {
        self.vals
    }
}

impl std::ops::Index<Var> for Model {
    type Output = BigUint;
    fn index(&self, var: Var) -> &BigUint {
        self.get(var).expect("variable not present in model")
    }
}

impl std::ops::Index<&str> for Model {
    type Output = BigUint;
    fn index(&self, name: &str) -> &BigUint {
        self.name(name)
            .unwrap_or_else(|| panic!("variable {name:?} not present in model"))
    }
}

/// `[] -> 0`, `[d] -> d`, wider -> `None`.
fn biguint_to_u64(b: &BigUint) -> Option<u64> {
    match b.to_u64_digits().as_slice() {
        [] => Some(0),
        [d] => Some(*d),
        _ => None,
    }
}
