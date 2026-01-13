//! Property-based tests for the SAT solver.
//!
//! These tests verify logical laws and solver properties using
//! randomly generated formulas.

use proptest::prelude::*;
use cdcl_sat::{Expr, solve_formula};

/// Strategy to generate expression AST.
fn arb_expr(depth: u32, max_var: i32) -> impl Strategy<Value = Expr> {
    let leaf = (1..=max_var).prop_map(Expr::Var);

    if depth == 0 {
        leaf.boxed()
    } else {
        prop_oneof![
            // Variables (more weight)
            3 => (1..=max_var).prop_map(Expr::Var),
            // Unary
            1 => arb_expr(depth - 1, max_var).prop_map(|e| Expr::Not(Box::new(e))),
            // Binary ops
            1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                .prop_map(|(a, b)| Expr::And(Box::new(a), Box::new(b))),
            1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                .prop_map(|(a, b)| Expr::Or(Box::new(a), Box::new(b))),
            1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                .prop_map(|(a, b)| Expr::Impl(Box::new(a), Box::new(b))),
            1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                .prop_map(|(a, b)| Expr::Equiv(Box::new(a), Box::new(b))),
        ].boxed()
    }
}

proptest! {
    /// Any single variable is satisfiable.
    #[test]
    fn prop_single_var_sat(var in 1..100i32) {
        let formula = format!("x{}", var);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// x AND NOT x is always unsatisfiable.
    #[test]
    fn prop_contradiction_unsat(var in 1..100i32) {
        let formula = format!("(and x{} (not x{}))", var, var);
        prop_assert!(!solve_formula(&formula).unwrap());
    }

    /// x OR NOT x is always satisfiable (tautology).
    #[test]
    fn prop_tautology_sat(var in 1..100i32) {
        let formula = format!("(or x{} (not x{}))", var, var);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// x IMPL x is always satisfiable (reflexive implication).
    #[test]
    fn prop_reflexive_impl_sat(var in 1..100i32) {
        let formula = format!("(impl x{} x{})", var, var);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// x EQUIV x is always satisfiable (reflexive equivalence).
    #[test]
    fn prop_reflexive_equiv_sat(var in 1..100i32) {
        let formula = format!("(equiv x{} x{})", var, var);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// NOT NOT x should be satisfiable.
    #[test]
    fn prop_double_negation(var in 1..100i32) {
        let formula = format!("(not (not x{}))", var);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// (x AND y) OR (NOT x AND NOT y) is satisfiable.
    #[test]
    fn prop_xor_like_sat(x in 1..50i32, y in 51..100i32) {
        let formula = format!(
            "(or (and x{} x{}) (and (not x{}) (not x{})))",
            x, y, x, y
        );
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// Implication chain with antecedent true is satisfiable.
    #[test]
    fn prop_impl_chain_sat(n in 2..5usize) {
        let mut formula = "x1".to_string();
        for i in 1..n {
            formula = format!("(and {} (impl x{} x{}))", formula, i, i + 1);
        }
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// Implication chain with contradiction is unsatisfiable.
    #[test]
    fn prop_impl_chain_unsat(n in 2..5usize) {
        let mut formula = format!("(and x1 (not x{}))", n);
        for i in 1..n {
            formula = format!("(and {} (impl x{} x{}))", formula, i, i + 1);
        }
        prop_assert!(!solve_formula(&formula).unwrap());
    }

    /// Random expressions should terminate.
    #[test]
    fn prop_solver_terminates(expr in arb_expr(3, 5)) {
        let formula = expr.to_string();
        let _result = solve_formula(&formula).unwrap();
    }

    /// Parser round-trip works for generated expressions.
    #[test]
    fn prop_parser_roundtrip(expr in arb_expr(2, 5)) {
        use cdcl_sat::Parser;
        let formula = expr.to_string();
        let mut parser = Parser::new(&formula);
        let parsed = parser.parse().unwrap();
        let reparsed = parsed.to_string();
        prop_assert_eq!(formula, reparsed);
    }

    /// CNF formulas should solve.
    #[test]
    fn prop_cnf_formula_solves(
        num_clauses in 2..5usize,
        clause_size in 2..4usize,
        num_vars in 3..6i32
    ) {
        let mut clauses = Vec::new();
        for _ in 0..num_clauses {
            let mut clause = String::new();
            for j in 0..clause_size {
                let var = (j as i32 % num_vars) + 1;
                let lit = if j % 2 == 0 {
                    format!("x{}", var)
                } else {
                    format!("(not x{})", var)
                };
                if clause.is_empty() {
                    clause = lit;
                } else {
                    clause = format!("(or {} {})", clause, lit);
                }
            }
            clauses.push(clause);
        }
        let mut formula = clauses[0].clone();
        for clause in clauses.iter().skip(1) {
            formula = format!("(and {} {})", formula, clause);
        }
        let _result = solve_formula(&formula).unwrap();
    }

    /// De Morgan's laws - NOT (a AND b) = NOT a OR NOT b.
    #[test]
    fn prop_demorgan_and(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(not (and x{} x{}))", a, b);
        let formula2 = format!("(or (not x{}) (not x{}))", a, b);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// De Morgan's laws - NOT (a OR b) = NOT a AND NOT b.
    #[test]
    fn prop_demorgan_or(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(not (or x{} x{}))", a, b);
        let formula2 = format!("(and (not x{}) (not x{}))", a, b);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Implication equivalence - (a IMPL b) = (NOT a OR b).
    #[test]
    fn prop_impl_equiv(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(impl x{} x{})", a, b);
        let formula2 = format!("(or (not x{}) x{})", a, b);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Equivalence definition - (a EQUIV b) = (a IMPL b) AND (b IMPL a).
    #[test]
    fn prop_equiv_definition(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(equiv x{} x{})", a, b);
        let formula2 = format!("(and (impl x{} x{}) (impl x{} x{}))", a, b, b, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Commutative AND.
    #[test]
    fn prop_and_commutative(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(and x{} x{})", a, b);
        let formula2 = format!("(and x{} x{})", b, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Commutative OR.
    #[test]
    fn prop_or_commutative(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(or x{} x{})", a, b);
        let formula2 = format!("(or x{} x{})", b, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Commutative EQUIV.
    #[test]
    fn prop_equiv_commutative(a in 1..50i32, b in 51..100i32) {
        let formula1 = format!("(equiv x{} x{})", a, b);
        let formula2 = format!("(equiv x{} x{})", b, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Associative AND.
    #[test]
    fn prop_and_associative(a in 1..33i32, b in 34..66i32, c in 67..100i32) {
        let formula1 = format!("(and (and x{} x{}) x{})", a, b, c);
        let formula2 = format!("(and x{} (and x{} x{}))", a, b, c);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Associative OR.
    #[test]
    fn prop_or_associative(a in 1..33i32, b in 34..66i32, c in 67..100i32) {
        let formula1 = format!("(or (or x{} x{}) x{})", a, b, c);
        let formula2 = format!("(or x{} (or x{} x{}))", a, b, c);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Absorption - a AND (a OR b) is satisfiable.
    #[test]
    fn prop_absorption_and(a in 1..50i32, b in 51..100i32) {
        let formula = format!("(and x{} (or x{} x{}))", a, a, b);
        prop_assert!(solve_formula(&formula).unwrap());
    }

    /// Idempotent AND - a AND a = a.
    #[test]
    fn prop_idempotent_and(a in 1..100i32) {
        let formula1 = format!("x{}", a);
        let formula2 = format!("(and x{} x{})", a, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }

    /// Idempotent OR - a OR a = a.
    #[test]
    fn prop_idempotent_or(a in 1..100i32) {
        let formula1 = format!("x{}", a);
        let formula2 = format!("(or x{} x{})", a, a);
        prop_assert_eq!(
            solve_formula(&formula1).unwrap(),
            solve_formula(&formula2).unwrap()
        );
    }
}
