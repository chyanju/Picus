//! cvc5 backend using QF_NIA (nonlinear integer arithmetic mod p).

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{
    build_poly_cvc5, dump_smt_nia, preflight, resolve_disequalities, SolverBackend,
    SolverBackendDescriptor, SolverError, SolverResult, UnknownReason,
};
use crate::Theory;
use picus_core::timeout::CancelToken;
use crate::poly_system::PolySystem;

pub struct Cvc5NiaBackend;

impl Default for Cvc5NiaBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Cvc5NiaBackend {
    pub fn new() -> Self {
        Self
    }
}

impl SolverBackend for Cvc5NiaBackend {
    fn solve(
        &mut self,
        ir: &PolySystem,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        // NIA lowers only equalities + the target disequality, so it refuses
        // disjunctions (`allow_disjunctions = false`).
        if let Some(r) = preflight(ir, cancel, false) {
            return Ok(r);
        }
        let tm = cvc5_ff::TermManager::new();
        let mut solver = cvc5_ff::Solver::new(&tm);
        solver.set_logic("QF_NIA");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let int_sort = tm.integer_sort();
        let prime = ir.ring.field().prime();
        let p_term = tm.mk_integer_from_str(&prime.to_string());
        let zero_term = tm.mk_integer(0);

        // Declare every ring variable with a `[0, p)` range constraint.
        let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();
        for name in ir.ring.var_names() {
            let v = tm.mk_const(int_sort.clone(), name);
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Geq, &[v.clone(), zero_term.clone()]),
            );
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Lt, &[v.clone(), p_term.clone()]),
            );
            vars.insert(name.clone(), v);
        }

        // Theory-specific term constructors for `build_poly_cvc5` (NIA).
        let mk_coeff = |c: &BigUint| tm.mk_integer_from_str(&c.to_string());
        let mk_zero = || tm.mk_integer(0);
        let mk_var = |n: &str| tm.mk_const(tm.integer_sort(), n);

        // Equalities: `(mod poly p) = 0`.
        for poly in &ir.equalities {
            let lhs = build_poly_cvc5(
                &tm,
                &vars,
                ir,
                poly,
                cvc5_ff::Kind::Mult,
                cvc5_ff::Kind::Add,
                &mk_coeff,
                &mk_zero,
                &mk_var,
            );
            let modded = tm.mk_term(cvc5_ff::Kind::IntsModulus, &[lhs, p_term.clone()]);
            solver.assert_formula(
                tm.mk_term(cvc5_ff::Kind::Equal, &[modded, zero_term.clone()]),
            );
        }

        // Disequalities: each resolved `(a, b)` becomes `(not (= a b))`.
        for (na, nb) in resolve_disequalities(ir)? {
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[vars[&na].clone(), vars[&nb].clone()]);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Not, &[eq]));
        }

        let result = solver.check_sat();
        if result.is_unsat() {
            Ok(SolverResult::Unsat)
        } else if result.is_sat() {
            let mut model = HashMap::new();
            for (name, var) in &vars {
                let val = solver.get_value(var.clone());
                if let Ok(n) = val.to_string().parse::<BigUint>() {
                    model.insert(name.clone(), n);
                }
            }
            Ok(SolverResult::Sat(model))
        } else {
            Ok(SolverResult::Unknown(UnknownReason::IncompleteTheory))
        }
    }

    fn dump_smt(&self, ir: &PolySystem) -> String {
        dump_smt_nia(ir, "mod")
    }
}

inventory::submit! {
    SolverBackendDescriptor {
        name: "cvc5",
        theory: Theory::Nia,
        factory: || Box::new(Cvc5NiaBackend::new()),
    }
}
