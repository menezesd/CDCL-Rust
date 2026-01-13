//! CNF detection and extraction for boolean expressions.
//!
//! This module provides functions to check if an expression is already in
//! Conjunctive Normal Form (CNF) and to extract clauses from CNF expressions.
//! This optimization avoids the overhead of Tseitin transformation when the
//! input is already in CNF.
//!
//! # CNF Definition
//!
//! A formula is in CNF if it is a conjunction (AND) of clauses, where each
//! clause is a disjunction (OR) of literals, and each literal is either a
//! variable or its negation.

use crate::{Clause, Expr, Literal};

/// Checks if an expression is a valid clause.
///
/// A clause is a disjunction of literals, which can be:
/// - A single variable: `x1`
/// - A negated variable: `(not x1)`
/// - An OR of literals: `(or x1 (not x2))`
/// - Nested ORs of literals: `(or (or x1 x2) x3)`
///
/// # Arguments
///
/// * `expr` - The expression to check
///
/// # Returns
///
/// `true` if the expression is a valid clause, `false` otherwise.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Expr, is_clause};
///
/// let clause = Expr::Or(
///     Box::new(Expr::Var(1)),
///     Box::new(Expr::Not(Box::new(Expr::Var(2)))),
/// );
/// assert!(is_clause(&clause));
///
/// // AND is not a clause
/// let not_clause = Expr::And(
///     Box::new(Expr::Var(1)),
///     Box::new(Expr::Var(2)),
/// );
/// assert!(!is_clause(&not_clause));
/// ```
pub fn is_clause(expr: &Expr) -> bool {
    match expr {
        Expr::Var(_) => true,
        Expr::Not(e) => matches!(e.as_ref(), Expr::Var(_)),
        Expr::Or(e1, e2) => is_clause(e1) && is_clause(e2),
        _ => false,
    }
}

/// Extracts literals from a clause expression.
///
/// This function traverses a clause expression and collects all literals
/// into the provided vector.
///
/// # Arguments
///
/// * `expr` - The clause expression to extract from
/// * `lits` - Vector to collect the extracted literals
///
/// # Returns
///
/// `true` if extraction succeeded, `false` if the expression is not a valid clause.
pub fn extract_clause_literals(expr: &Expr, lits: &mut Vec<Literal>) -> bool {
    match expr {
        Expr::Var(v) => {
            lits.push(Literal::positive(*v));
            true
        }
        Expr::Not(e) => {
            if let Expr::Var(v) = e.as_ref() {
                lits.push(Literal::negative(*v));
                true
            } else {
                false
            }
        }
        Expr::Or(e1, e2) => {
            extract_clause_literals(e1, lits) && extract_clause_literals(e2, lits)
        }
        _ => false,
    }
}

/// Checks if an expression is in Conjunctive Normal Form (CNF).
///
/// A formula is in CNF if it's a conjunction (AND) of clauses.
/// Single clauses are also considered to be in CNF.
///
/// # Arguments
///
/// * `expr` - The expression to check
///
/// # Returns
///
/// `true` if the expression is in CNF, `false` otherwise.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Expr, is_cnf};
///
/// // (x1 OR x2) AND (x3 OR NOT x4) is CNF
/// let cnf = Expr::And(
///     Box::new(Expr::Or(
///         Box::new(Expr::Var(1)),
///         Box::new(Expr::Var(2)),
///     )),
///     Box::new(Expr::Or(
///         Box::new(Expr::Var(3)),
///         Box::new(Expr::Not(Box::new(Expr::Var(4)))),
///     )),
/// );
/// assert!(is_cnf(&cnf));
///
/// // (x1 IMPL x2) is NOT CNF
/// let not_cnf = Expr::Impl(
///     Box::new(Expr::Var(1)),
///     Box::new(Expr::Var(2)),
/// );
/// assert!(!is_cnf(&not_cnf));
/// ```
pub fn is_cnf(expr: &Expr) -> bool {
    match expr {
        Expr::And(e1, e2) => {
            (is_cnf(e1) || is_clause(e1)) && (is_cnf(e2) || is_clause(e2))
        }
        _ => is_clause(expr),
    }
}

/// Extracts clauses from a CNF expression.
///
/// This function traverses a CNF expression and extracts all clauses,
/// converting them into the `Clause` representation used by the solver.
///
/// # Arguments
///
/// * `expr` - The CNF expression to extract from
/// * `clauses` - Vector to collect the extracted clauses
///
/// # Returns
///
/// `true` if extraction succeeded, `false` if the expression is not valid CNF.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Expr, Clause, extract_cnf_clauses};
///
/// let cnf = Expr::And(
///     Box::new(Expr::Or(
///         Box::new(Expr::Var(1)),
///         Box::new(Expr::Var(2)),
///     )),
///     Box::new(Expr::Var(3)),
/// );
///
/// let mut clauses = Vec::new();
/// assert!(extract_cnf_clauses(&cnf, &mut clauses));
/// assert_eq!(clauses.len(), 2);
/// ```
pub fn extract_cnf_clauses(expr: &Expr, clauses: &mut Vec<Clause>) -> bool {
    match expr {
        Expr::And(e1, e2) => {
            extract_cnf_clauses(e1, clauses) && extract_cnf_clauses(e2, clauses)
        }
        _ => {
            let mut lits = Vec::new();
            if extract_clause_literals(expr, &mut lits) {
                clauses.push(Clause::new(lits));
                true
            } else {
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_clause_single_var() {
        let expr = Expr::Var(1);
        assert!(is_clause(&expr));
    }

    #[test]
    fn test_is_clause_negated_var() {
        let expr = Expr::Not(Box::new(Expr::Var(1)));
        assert!(is_clause(&expr));
    }

    #[test]
    fn test_is_clause_or_of_literals() {
        let expr = Expr::Or(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Not(Box::new(Expr::Var(2)))),
        );
        assert!(is_clause(&expr));
    }

    #[test]
    fn test_is_clause_nested_or() {
        let expr = Expr::Or(
            Box::new(Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            )),
            Box::new(Expr::Var(3)),
        );
        assert!(is_clause(&expr));
    }

    #[test]
    fn test_is_clause_and_not_clause() {
        let expr = Expr::And(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        assert!(!is_clause(&expr));
    }

    #[test]
    fn test_is_clause_double_negation_not_clause() {
        let expr = Expr::Not(Box::new(Expr::Not(Box::new(Expr::Var(1)))));
        assert!(!is_clause(&expr));
    }

    #[test]
    fn test_is_cnf_single_clause() {
        let expr = Expr::Or(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        assert!(is_cnf(&expr));
    }

    #[test]
    fn test_is_cnf_and_of_clauses() {
        let expr = Expr::And(
            Box::new(Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            )),
            Box::new(Expr::Or(
                Box::new(Expr::Var(3)),
                Box::new(Expr::Not(Box::new(Expr::Var(4)))),
            )),
        );
        assert!(is_cnf(&expr));
    }

    #[test]
    fn test_is_cnf_nested_and() {
        let expr = Expr::And(
            Box::new(Expr::And(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            )),
            Box::new(Expr::Var(3)),
        );
        assert!(is_cnf(&expr));
    }

    #[test]
    fn test_is_cnf_impl_not_cnf() {
        let expr = Expr::Impl(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        assert!(!is_cnf(&expr));
    }

    #[test]
    fn test_extract_clause_literals() {
        let expr = Expr::Or(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Not(Box::new(Expr::Var(2)))),
        );
        let mut lits = Vec::new();
        assert!(extract_clause_literals(&expr, &mut lits));
        assert_eq!(lits.len(), 2);
        assert_eq!(lits[0].var, 1);
        assert!(!lits[0].negated);
        assert_eq!(lits[1].var, 2);
        assert!(lits[1].negated);
    }

    #[test]
    fn test_extract_cnf_clauses() {
        let expr = Expr::And(
            Box::new(Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            )),
            Box::new(Expr::Or(
                Box::new(Expr::Var(3)),
                Box::new(Expr::Var(4)),
            )),
        );
        let mut clauses = Vec::new();
        assert!(extract_cnf_clauses(&expr, &mut clauses));
        assert_eq!(clauses.len(), 2);
    }
}
