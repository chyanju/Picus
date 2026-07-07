//! QF_UFFF differential harness: the native backend vs cvc5 (driven
//! through the cvc5-ff bindings) on randomized FF+UF goals.
//!
//! Only verdicts are compared, and only when both sides decide:
//! cvc5's FF+UF combination is Unknown-prone and the native Sat side
//! degrades on large primes, so unknown/timeout on either leg is "no
//! information", never a disagreement. The wired production backend's
//! `QF_FF` logic string rejects non-zero-arity `declare-fun`, so this
//! harness sets `QF_UFFF` explicitly.
//!
//! Builds only with `--features cvc5` (`[[test]]
//! required-features = ["cvc5"]`).

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_core::timeout::CancelToken;
use picus_smt::backends::{create_backend_by_name, SolverResult};
use picus_smt::poly_system::PolySystem;
use picus_smt::Theory;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Random FF+UF system: `n_vars` variables, one unary UF symbol with
/// 2-3 applications, 0-2 linear equalities (small coefficients), and
/// one result-pair disequality. Kept linear so the native Sat side
/// stays decidable on BN254 too.
fn random_ir(rng: &mut Lcg, prime: &BigUint) -> PolySystem {
    let n_vars = 4 + rng.below(2) as usize; // 4..=5
    let field = PrimeField::new(prime.clone());
    let names: Vec<String> = (0..n_vars).map(|i| format!("v{}", i)).collect();
    let ring = Arc::new(FfPolyRing::new(field, names));
    let mut ir = PolySystem::new(ring);

    let f = ir.uf_symbol("f");
    let n_apps = 2 + rng.below(2) as usize; // 2..=3
    let mut results: Vec<usize> = Vec::new();
    for _ in 0..n_apps {
        let arg = rng.below(n_vars as u64) as usize;
        let result = rng.below(n_vars as u64) as usize;
        ir.add_uf_app(f, vec![arg], result);
        results.push(result);
    }

    let n_eqs = rng.below(3) as usize; // 0..=2
    for _ in 0..n_eqs {
        let a = rng.below(n_vars as u64) as usize;
        let b = rng.below(n_vars as u64) as usize;
        if a == b {
            continue;
        }
        // a - c·b = 0 with c ∈ {1, 2}.
        let c = 1 + rng.below(2);
        let term = ir.ring.sub(
            ir.ring.var(a),
            ir.linear_term(&BigUint::from(c), b),
        );
        ir.push_equality(term);
    }

    // Target disequality between two application results (falls back
    // to the first two variables when the results coincide).
    let (r1, r2) = (results[0], results[1 % results.len()]);
    if r1 != r2 {
        ir.add_disequality(r1, r2);
    } else {
        ir.add_disequality(0, 1);
    }

    if prime <= &BigUint::from(1000u32) {
        ir.set_add_field_polys(true);
    }
    ir
}

fn native_verdict(ir: &PolySystem) -> Verdict {
    let mut backend = create_backend_by_name("native", Theory::Ff).expect("native backend");
    match backend.solve(ir, 5000, &CancelToken::none()) {
        Ok(SolverResult::Sat(_)) => Verdict::Sat,
        Ok(SolverResult::Unsat) => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

/// Drive cvc5 directly over QF_UFFF: FF sort + declared variables,
/// `declare_fun` for the symbol, `ApplyUf` terms for the applications.
fn cvc5_verdict(ir: &PolySystem) -> Verdict {
    let tm = cvc5_ff::TermManager::new();
    let mut solver = cvc5_ff::Solver::new(&tm);
    solver.set_logic("QF_UFFF");
    solver.set_option("tlimit", "5000");

    let prime = ir.ring.field().prime();
    let ff = tm.mk_ff_sort(&prime.to_string(), 10);
    let zero = tm.mk_ff_elem("0", ff.clone(), 10);

    let mut vars: HashMap<String, cvc5_ff::Term> = HashMap::new();
    for name in ir.ring.var_names() {
        vars.insert(name.clone(), tm.mk_const(ff.clone(), name));
    }

    let build_poly = |poly: &picus_core::poly::Poly| -> cvc5_ff::Term {
        let mut terms: Vec<cvc5_ff::Term> = Vec::new();
        for (coeff, atoms) in ir.poly_terms(poly) {
            let mut t = tm.mk_ff_elem(&coeff.to_string(), ff.clone(), 10);
            for name in atoms {
                t = tm.mk_term(
                    cvc5_ff::Kind::FiniteFieldMult,
                    &[t, vars[&name].clone()],
                );
            }
            terms.push(t);
        }
        match terms.len() {
            0 => zero.clone(),
            1 => terms.into_iter().next().unwrap(),
            _ => tm.mk_term(cvc5_ff::Kind::FiniteFieldAdd, &terms),
        }
    };

    for poly in &ir.equalities {
        let lhs = build_poly(poly);
        solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Equal, &[lhs, zero.clone()]));
    }

    // One cvc5 function constant per UF symbol (arity from the first
    // application — the harness generates consistent arities).
    let mut funs: HashMap<usize, cvc5_ff::Term> = HashMap::new();
    for app in &ir.uf_apps {
        funs.entry(app.symbol).or_insert_with(|| {
            let domain: Vec<cvc5_ff::Sort> = vec![ff.clone(); app.args.len()];
            solver.declare_fun(&ir.uf_symbols[app.symbol], &domain, ff.clone())
        });
    }
    let names = ir.ring.var_names();
    for app in &ir.uf_apps {
        let mut children: Vec<cvc5_ff::Term> = Vec::with_capacity(app.args.len() + 1);
        children.push(funs[&app.symbol].clone());
        for &a in &app.args {
            children.push(vars[&names[a]].clone());
        }
        let applied = tm.mk_term(cvc5_ff::Kind::ApplyUf, &children);
        solver.assert_formula(tm.mk_term(
            cvc5_ff::Kind::Equal,
            &[vars[&names[app.result]].clone(), applied],
        ));
    }

    for &(a, b) in &ir.disequalities {
        let eq = tm.mk_term(
            cvc5_ff::Kind::Equal,
            &[vars[&names[a]].clone(), vars[&names[b]].clone()],
        );
        solver.assert_formula(tm.mk_term(cvc5_ff::Kind::Not, &[eq]));
    }

    let result = solver.check_sat();
    if result.is_unsat() {
        Verdict::Unsat
    } else if result.is_sat() {
        Verdict::Sat
    } else {
        Verdict::Unknown
    }
}

fn run_leg(prime: &BigUint, n: usize, seed: u64) {
    let mut rng = Lcg(seed);
    let mut compared = 0usize;
    let mut sat_agree = 0usize;
    let mut unsat_agree = 0usize;
    for i in 0..n {
        let ir = random_ir(&mut rng, prime);
        let nv = native_verdict(&ir);
        let cv = cvc5_verdict(&ir);
        if nv == Verdict::Unknown || cv == Verdict::Unknown {
            continue; // no information, never a disagreement
        }
        assert_eq!(
            nv, cv,
            "native/cvc5 verdict contradiction on entry {} over GF({})",
            i, prime
        );
        compared += 1;
        match nv {
            Verdict::Sat => sat_agree += 1,
            Verdict::Unsat => unsat_agree += 1,
            Verdict::Unknown => unreachable!(),
        }
    }
    // Anti-vacuity: the comparison must actually exercise both verdicts.
    assert!(compared * 2 >= n, "too few comparable entries: {}/{}", compared, n);
    assert!(sat_agree > 0, "no SAT agreement observed");
    assert!(unsat_agree > 0, "no UNSAT agreement observed");
}

/// One sequential test for both legs: concurrent cvc5
/// TermManager/Solver instances in one process segfault (the bindings
/// are not thread-safe), so the legs must not run on parallel test
/// threads.
#[test]
fn differential_gf5_and_bn254() {
    run_leg(&BigUint::from(5u32), 40, 0xD1FF);
    let bn254: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap();
    run_leg(&bn254, 15, 0xB254);
}
