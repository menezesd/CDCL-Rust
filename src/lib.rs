//! A CDCL (Conflict-Driven Clause Learning) SAT solver implemented in Rust.
//!
//! This library provides a complete SAT solver that can determine the satisfiability
//! of boolean formulas. It supports formulas in prefix notation with the following
//! operators: `and`, `or`, `not`, `impl` (implication), and `equiv` (equivalence).
//!
//! # Features
//!
//! - **Flexible input**: Parse formulas in prefix notation or construct directly
//! - **CNF optimization**: Automatically detects CNF formulas and extracts directly
//! - **Tseitin transformation**: Converts arbitrary formulas to CNF in polynomial time
//! - **CDCL algorithm**: Modern SAT solving with:
//!   - Two-watched literals for efficient propagation
//!   - First-UIP conflict analysis
//!   - Non-chronological backtracking
//!   - VSIDS variable selection with binary heap
//!
//! # Example
//!
//! ```
//! use cdcl_sat::{Parser, solve_formula};
//!
//! // Parse and solve a formula
//! let result = solve_formula("(and x1 (or x2 (not x3)))");
//! assert!(result.is_ok());
//! assert!(result.unwrap()); // SAT
//!
//! // Contradiction is UNSAT
//! let result = solve_formula("(and x1 (not x1))");
//! assert!(!result.unwrap()); // UNSAT
//! ```
//!
//! # Formula Syntax
//!
//! Formulas use prefix (Polish) notation:
//!
//! - Variables: `x1`, `x2`, `x3`, ... (positive integers)
//! - Negation: `(not expr)`
//! - Conjunction: `(and expr1 expr2)`
//! - Disjunction: `(or expr1 expr2)`
//! - Implication: `(impl expr1 expr2)` (a → b)
//! - Equivalence: `(equiv expr1 expr2)` (a ↔ b)
//!
//! # Architecture
//!
//! The solver is organized into the following modules:
//!
//! - [`expr`]: Boolean expression AST
//! - [`parser`]: Prefix notation parser with error handling
//! - [`literal`]: Literal and clause types for CNF representation
//! - [`cnf`]: CNF detection and extraction
//! - [`tseitin`]: Tseitin transformation to CNF
//! - [`solver`]: CDCL SAT solver implementation

pub mod expr;
pub mod parser;
pub mod literal;
pub mod cnf;
pub mod tseitin;
pub mod solver;

#[cfg(test)]
pub mod test_helpers;

// Re-export main types for convenience
pub use expr::{Expr, find_max_var};
pub use parser::{Parser, ParseError};
pub use literal::{Literal, Clause};
pub use cnf::{is_clause, is_cnf, extract_clause_literals, extract_cnf_clauses};
pub use tseitin::TseitinTransformer;
pub use solver::{CDCLSolver, SolverError};

use std::fmt;

/// Combined error type for the solve_formula function.
///
/// This enum wraps both parsing errors and solver errors that can occur
/// when processing a formula from string input to solution.
#[derive(Debug, Clone)]
pub enum SolveError {
    /// An error occurred while parsing the formula.
    Parse(ParseError),
    /// An internal solver error occurred.
    Solver(SolverError),
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolveError::Parse(e) => write!(f, "Parse error: {}", e),
            SolveError::Solver(e) => write!(f, "Solver error: {}", e),
        }
    }
}

impl std::error::Error for SolveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SolveError::Parse(e) => Some(e),
            SolveError::Solver(e) => Some(e),
        }
    }
}

impl From<ParseError> for SolveError {
    fn from(err: ParseError) -> Self {
        SolveError::Parse(err)
    }
}

impl From<SolverError> for SolveError {
    fn from(err: SolverError) -> Self {
        SolveError::Solver(err)
    }
}

/// Parses and solves a formula given as a string.
///
/// This is a convenience function that combines parsing, CNF conversion,
/// and solving into a single call.
///
/// # Arguments
///
/// * `input` - The formula in prefix notation
///
/// # Returns
///
/// - `Ok(true)` if the formula is satisfiable
/// - `Ok(false)` if the formula is unsatisfiable
/// - `Err(SolveError::Parse(_))` if the formula could not be parsed
/// - `Err(SolveError::Solver(_))` if an internal solver error occurred
///
/// # Example
///
/// ```
/// use cdcl_sat::solve_formula;
///
/// // Satisfiable formula
/// assert!(solve_formula("(or x1 x2)").unwrap());
///
/// // Unsatisfiable formula
/// assert!(!solve_formula("(and x1 (not x1))").unwrap());
/// ```
pub fn solve_formula(input: &str) -> Result<bool, SolveError> {
    let mut parser = Parser::new(input);
    let expr = parser.parse()?;

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
    Ok(solver.solve()?)
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_ex1_single_var() {
        assert!(solve_formula("x1").unwrap());
    }

    #[test]
    fn test_ex2_contradiction() {
        assert!(!solve_formula("(and x1 (not x1))").unwrap());
    }

    #[test]
    fn test_ex3_nested_or() {
        assert!(solve_formula("(or x1 (not (and x2 x3)))").unwrap());
    }

    #[test]
    fn test_all_operators_combined() {
        let formula = "(and (impl x1 x2) (equiv x3 (or x1 (not x4))))";
        assert!(solve_formula(formula).unwrap());
    }

    #[test]
    fn test_cnf_direct_extraction() {
        let formula = "(and (or x1 x2) (or (not x1) x3))";
        assert!(solve_formula(formula).unwrap());
    }

    #[test]
    fn test_larger_cnf() {
        let formula = "(and (and (and (or x1 x2) (or (not x1) x3)) (or (not x2) x4)) (or x1 (not x4)))";
        assert!(solve_formula(formula).unwrap());
    }

    #[test]
    fn test_unsat_3_clauses() {
        let formula = "(and (and x1 (or (not x1) x2)) (not x2))";
        assert!(!solve_formula(formula).unwrap());
    }

    #[test]
    fn test_chain_implication_sat() {
        let formula = "(and (and (and (impl x1 x2) (impl x2 x3)) (impl x3 x4)) (and x1 x4))";
        assert!(solve_formula(formula).unwrap());
    }

    #[test]
    fn test_chain_implication_unsat() {
        let formula = "(and (and (and (impl x1 x2) (impl x2 x3)) x1) (not x3))";
        assert!(!solve_formula(formula).unwrap());
    }

    #[test]
    fn test_equiv_chain_sat() {
        let formula = "(and (and (equiv x1 x2) (equiv x2 x3)) (and x1 x3))";
        assert!(solve_formula(formula).unwrap());
    }

    #[test]
    fn test_equiv_chain_unsat() {
        let formula = "(and (and (equiv x1 x2) (equiv x2 x3)) (and x1 (not x3)))";
        assert!(!solve_formula(formula).unwrap());
    }

    #[test]
    fn test_tautology_sat() {
        assert!(solve_formula("(or x1 (not x1))").unwrap());
    }

    #[test]
    fn test_impl_sat() {
        assert!(solve_formula("(impl x1 x2)").unwrap());
    }

    #[test]
    fn test_equiv_sat() {
        assert!(solve_formula("(equiv x1 x2)").unwrap());
    }

    #[test]
    fn test_parse_error_handling() {
        let result = solve_formula("(foo x1 x2)");
        assert!(result.is_err());
        assert!(matches!(result, Err(SolveError::Parse(_))));
    }

    #[test]
    fn test_solve_error_display() {
        let parse_err = SolveError::Parse(ParseError::UnknownOperator("test".to_string()));
        let msg = format!("{}", parse_err);
        assert!(msg.contains("Parse error"));

        let solver_err = SolveError::Solver(SolverError::InternalError("test".to_string()));
        let msg2 = format!("{}", solver_err);
        assert!(msg2.contains("Solver error"));
    }

    #[test]
    fn test_solve_error_source() {
        use std::error::Error;

        let parse_err = SolveError::Parse(ParseError::UnknownOperator("test".to_string()));
        assert!(parse_err.source().is_some());

        let solver_err = SolveError::Solver(SolverError::InternalError("test".to_string()));
        assert!(solver_err.source().is_some());
    }

    #[test]
    fn test_solve_error_from_parse_error() {
        let parse_err = ParseError::UnknownOperator("test".to_string());
        let solve_err: SolveError = parse_err.into();
        assert!(matches!(solve_err, SolveError::Parse(_)));
    }

    #[test]
    fn test_solve_error_from_solver_error() {
        let solver_err = SolverError::InternalError("test".to_string());
        let solve_err: SolveError = solver_err.into();
        assert!(matches!(solve_err, SolveError::Solver(_)));
    }
}
