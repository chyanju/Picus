//! cvc5 backend using QF_FF (native finite-field theory).
//!
//! Lowers each polynomial equality in the IR to a cvc5 `ff.add` of
//! `ff.mul` products, then asserts `(= 0 ...)`. The target wire's
//! disequality `(not (= x_t y_t))` closes the query.

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::backends::{
    build_poly_cvc5, poly_to_smtlib_ff, preflight, resolve_disequalities, SolverBackend,
    SolverBackendDescriptor, SolverError, SolverResult, UnknownReason,
};
use crate::Theory;
use picus_core::timeout::CancelToken;
use crate::poly_system::PolySystem;

pub struct Cvc5FfBackend;

impl Default for Cvc5FfBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Cvc5FfBackend {
    pub fn new() -> Self {
        Self
    }
}

impl SolverBackend for Cvc5FfBackend {
    fn solve(
        &mut self,
        ir: &PolySystem,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        // This backend allows disjunctions (its QF_FF DPLL(T) handles `or`).
        if let Some(r) = preflight(ir, cancel, true) {
            return Ok(r);
        }
        let tm = cvc5_ff::TermManager::new();
        let mut solver = cvc5_ff::Solver::new(&tm);
        solver.set_logic("QF_FF");
        solver.set_option("produce-models", "true");
        solver.set_option("tlimit", &timeout_ms.to_string());

        let prime = ir.ring.field().prime();
        let p_str = prime.to_string();
        let ff = tm.mk_ff_sort(&p_str, 10);

        // Declare every ring variable (both `x_i` and `y_i`). The IR's
        // input equalities will collapse `x_i = y_i` for inputs during
        // solving; we don't special-case them at declaration time.
        let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();
        for name in ir.ring.var_names() {
            let v = tm.mk_const(ff.clone(), name);
            vars.insert(name.clone(), v);
        }

        let zero = tm.mk_ff_elem("0", ff.clone(), 10);

        // Theory-specific term constructors for `build_poly_cvc5` (FF).
        let mk_coeff = |c: &BigUint| tm.mk_ff_elem(&c.to_string(), ff.clone(), 10);
        let mk_zero = || tm.mk_ff_elem("0", ff.clone(), 10);
        let mk_var = |n: &str| tm.mk_const(ff.clone(), n);
        let build = |poly: &picus_core::poly::Poly| {
            build_poly_cvc5(
                &tm,
                &vars,
                ir,
                poly,
                cvc5_ff::Kind::FiniteFieldMult,
                cvc5_ff::Kind::FiniteFieldAdd,
                &mk_coeff,
                &mk_zero,
                &mk_var,
            )
        };

        // Equalities.
        for poly in &ir.equalities {
            let lhs = build(poly);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs, zero.clone()]));
        }

        // Disequalities: each resolved `(a, b)` becomes `(not (= a b))`.
        for (na, nb) in resolve_disequalities(ir)? {
            let eq = tm.mk_term(cvc5_ff::Kind::Equal, &[vars[&na].clone(), vars[&nb].clone()]);
            solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Not, &[eq]));
        }

        // Disjunctions: clause `[p_1, ..., p_k]` ⇒ `(or (= p_1 0) ... (=
        // p_k 0))`. We hand cvc5 the `or` directly (no special-casing);
        // its QF_FF DPLL(T) does the case split. (cvc5's `or` soundness
        // is cvc5's own responsibility; picus adds no guard.)
        for clause in &ir.disjunctions {
            let mut alts: Vec<cvc5_ff::Term> = Vec::with_capacity(clause.len());
            for poly in clause {
                let lhs = build(poly);
                alts.push(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs, zero.clone()]));
            }
            match alts.len() {
                0 => {}
                1 => solver.assert_formula(alts.into_iter().next().unwrap()),
                _ => solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Or, &alts)),
            }
        }

        let result = solver.check_sat();
        if result.is_unsat() {
            Ok(SolverResult::Unsat)
        } else if result.is_sat() {
            let mut model = HashMap::new();
            for (name, var) in &vars {
                let val = solver.get_value(var.clone());
                let val_str = val.to_string();
                if let Some(n) = parse_ff_value(&val_str) {
                    model.insert(name.clone(), n);
                }
            }
            Ok(SolverResult::Sat(model))
        } else {
            // cvc5 returned `unknown` (or `timeout`). Without a way to
            // distinguish at this level we record it as `IncompleteTheory`
            // — the caller can still retry with more time.
            Ok(SolverResult::Unknown(UnknownReason::IncompleteTheory))
        }
    }

    fn dump_smt(&self, ir: &PolySystem) -> String {
        let p = ir.ring.field().prime();
        let mut lines = Vec::new();
        lines.push("(set-logic QF_FF)".to_string());
        lines.push(format!("(define-sort F () (_ FiniteField {}))", p));
        for name in ir.ring.var_names() {
            lines.push(format!("(declare-const {} F)", name));
        }
        for poly in &ir.equalities {
            lines.push(format!(
                "(assert (= #f0m{} {}))",
                p,
                poly_to_smtlib_ff(ir, poly)
            ));
        }
        {
            let names = ir.ring.var_names();
            for &(a, b) in &ir.disequalities {
                lines.push(format!("(assert (not (= {} {})))", names[a], names[b]));
            }
        }
        for clause in &ir.disjunctions {
            let parts: Vec<String> = clause
                .iter()
                .map(|poly| format!("(= #f0m{} {})", p, poly_to_smtlib_ff(ir, poly)))
                .collect();
            match parts.len() {
                0 => {}
                1 => lines.push(format!("(assert {})", parts[0])),
                _ => lines.push(format!("(assert (or {}))", parts.join(" "))),
            }
        }
        lines.push("(check-sat)".to_string());
        lines.push("(get-model)".to_string());
        lines.join("\n")
    }
}

fn parse_ff_value(s: &str) -> Option<BigUint> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("#f") {
        let m_pos = rest.find('m')?;
        rest[..m_pos].parse().ok()
    } else {
        s.parse().ok()
    }
}

inventory::submit! {
    SolverBackendDescriptor {
        name: "cvc5",
        theory: Theory::Ff,
        factory: || Box::new(Cvc5FfBackend::new()),
    }
}

#[cfg(test)]
#[path = "cvc5_ff_tests.rs"]
mod tests;
