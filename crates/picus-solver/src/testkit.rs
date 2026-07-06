//! Shared name-keyed fixture DSL for this crate's tests and benches
//! (feature `testkit`; never compiled into a production consumer).
//! Lets a dev target write systems in a readable name-keyed form that
//! wraps the index-keyed `ConstraintSystemBuilder` underneath.
//!
//! Threading a builder explicitly through each test would obscure
//! what's being checked; the helper below lets a test stay in the
//! "name-keyed fixture → encode → assert" shape.

use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::solve::{solve_encoded, SolveOutcome};
use crate::frontend::encoder::{
    encode, ConstraintSystem, ConstraintSystemBuilder, EncodedSystem, PolyTerm, VarIdx,
};

/// Name-keyed AST scratch term. Re-exported from
/// [`picus_solver::push_pop`] so the `pt(..)` helper here and
/// `RebuildOnCheckSolver::assert_equality` agree on one struct.
pub use crate::push_pop::NamedTerm;

fn intern_named_term(t: &NamedTerm, builder: &mut ConstraintSystemBuilder) -> PolyTerm {
    let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
    for v in &t.vars {
        let idx = builder.var(v);
        *counts.entry(idx).or_insert(0) += 1;
    }
    PolyTerm {
        coeff: t.coeff.clone(),
        vars: counts.into_iter().collect(),
    }
}

/// Constant term `c`.
pub fn ct(c: u64) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(c),
        vars: vec![],
    }
}

/// `1 * v`.
/// Constant term from a `BigUint`.
pub fn ctb(c: BigUint) -> NamedTerm {
    NamedTerm { coeff: c, vars: vec![] }
}

/// `1 * v`.
pub fn vt(v: &str) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(1u32),
        vars: vec![v.to_string()],
    }
}

/// `c * v`.
pub fn svt(c: u64, v: &str) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(c),
        vars: vec![v.to_string()],
    }
}

/// `c * prod(vars)`. Repeated names raise the exponent.
pub fn pt(c: u64, vars: &[&str]) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(c),
        vars: vars.iter().map(|s| s.to_string()).collect(),
    }
}

/// Name-keyed system fixture. Tests construct one of these, then
/// call [`Self::build`] to lower to a real `ConstraintSystem`.
#[derive(Default)]
pub struct NamedSystem {
    pub prime: BigUint,
    pub equalities: Vec<Vec<NamedTerm>>,
    pub disequalities: Vec<(String, String)>,
    pub assignments: Vec<(String, BigUint)>,
    pub add_field_polys: bool,
    pub bitsums: Vec<Vec<String>>,
}

impl NamedSystem {
        pub fn new(prime: BigUint) -> Self {
        NamedSystem {
            prime,
            ..Default::default()
        }
    }

        pub fn build(&self) -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(self.prime.clone());
        b.set_add_field_polys(self.add_field_polys);
        for eq in &self.equalities {
            let terms: Vec<PolyTerm> = eq.iter().map(|t| intern_named_term(t, &mut b)).collect();
            b.add_equality(terms);
        }
        for (a, val) in &self.assignments {
            let idx = b.var(a);
            b.add_assignment(idx, val.clone());
        }
        for (a, c) in &self.disequalities {
            let ai = b.var(a);
            let bi = b.var(c);
            b.add_disequality(ai, bi);
        }
        for bs in &self.bitsums {
            let idxs: Vec<VarIdx> = bs.iter().map(|n| b.var(n)).collect();
            b.add_bitsum(idxs);
        }
        b.build()
    }

        pub fn encode(&self) -> Result<EncodedSystem, String> {
        encode(&self.build()).map_err(|e| e.to_string())
    }

        pub fn solve(&self) -> SolveOutcome {
        let encoded = self.encode().expect("encode");
        solve_encoded(&encoded)
    }

        pub fn is_sat(&self) -> bool {
        matches!(self.solve(), SolveOutcome::Sat(_))
    }

        pub fn is_unsat(&self) -> bool {
        matches!(self.solve(), SolveOutcome::Unsat(_))
    }
}
