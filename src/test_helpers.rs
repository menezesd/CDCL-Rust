//! Shared test helper functions.
//!
//! This module provides common utilities used across test modules
//! to avoid code duplication.

use crate::{
    Parser, Expr, CDCLSolver, TseitinTransformer,
    is_cnf, extract_cnf_clauses, find_max_var,
};

/// Parses and solves a formula, returning whether it's satisfiable.
///
/// This is the canonical test helper that combines parsing, CNF conversion,
/// and solving. All test modules should use this function instead of
/// duplicating the logic.
///
/// # Arguments
///
/// * `input` - The formula in prefix notation
///
/// # Returns
///
/// `true` if the formula is satisfiable, `false` otherwise.
///
/// # Panics
///
/// Panics if the formula cannot be parsed or if a solver error occurs.
pub fn solve_formula(input: &str) -> bool {
    let mut parser = Parser::new(input);
    let expr = parser.parse().expect("Failed to parse formula");

    let clauses = if is_cnf(&expr) {
        let mut clauses = Vec::new();
        if extract_cnf_clauses(&expr, &mut clauses) {
            clauses
        } else {
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root_var = transformer.transform(&expr);
            transformer.into_clauses(root_var)
        }
    } else {
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root_var = transformer.transform(&expr);
        transformer.into_clauses(root_var)
    };

    let mut solver = CDCLSolver::new(clauses);
    solver.solve().expect("Solver error")
}

/// Converts an expression to its string representation.
///
/// This is useful for property-based testing where expressions
/// are generated programmatically.
pub fn expr_to_string(expr: &Expr) -> String {
    expr.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solve_formula_sat() {
        assert!(solve_formula("x1"));
        assert!(solve_formula("(or x1 x2)"));
        assert!(solve_formula("(and x1 x2)"));
    }

    #[test]
    fn test_solve_formula_unsat() {
        assert!(!solve_formula("(and x1 (not x1))"));
    }
}
