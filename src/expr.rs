//! Boolean expression AST representation.
//!
//! This module defines the abstract syntax tree (AST) for boolean expressions
//! that can be parsed and solved by the SAT solver.

/// Represents a boolean expression in abstract syntax tree form.
///
/// Supports the following operations:
/// - Variables (`Var`): Named boolean variables with integer identifiers
/// - Negation (`Not`): Logical NOT
/// - Conjunction (`And`): Logical AND
/// - Disjunction (`Or`): Logical OR
/// - Implication (`Impl`): Logical implication (a → b)
/// - Equivalence (`Equiv`): Logical biconditional (a ↔ b)
///
/// # Example
///
/// ```
/// use cdcl_sat::Expr;
///
/// // Represents the formula: (x1 AND x2) OR (NOT x3)
/// let expr = Expr::Or(
///     Box::new(Expr::And(
///         Box::new(Expr::Var(1)),
///         Box::new(Expr::Var(2)),
///     )),
///     Box::new(Expr::Not(Box::new(Expr::Var(3)))),
/// );
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A boolean variable identified by a positive integer.
    /// Variable numbers should be >= 1.
    Var(i32),

    /// Logical negation: NOT a
    Not(Box<Expr>),

    /// Logical conjunction: a AND b
    And(Box<Expr>, Box<Expr>),

    /// Logical disjunction: a OR b
    Or(Box<Expr>, Box<Expr>),

    /// Logical implication: a → b (equivalent to NOT a OR b)
    Impl(Box<Expr>, Box<Expr>),

    /// Logical equivalence: a ↔ b (a if and only if b)
    Equiv(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Converts the expression to its string representation in prefix notation.
    ///
    /// This produces a string that can be parsed back by the `Parser`.
    ///
    /// # Example
    ///
    /// ```
    /// use cdcl_sat::Expr;
    ///
    /// let expr = Expr::And(
    ///     Box::new(Expr::Var(1)),
    ///     Box::new(Expr::Var(2)),
    /// );
    /// assert_eq!(expr.to_string(), "(and x1 x2)");
    /// ```
    pub fn to_string(&self) -> String {
        match self {
            Expr::Var(v) => format!("x{}", v),
            Expr::Not(e) => format!("(not {})", e.to_string()),
            Expr::And(a, b) => format!("(and {} {})", a.to_string(), b.to_string()),
            Expr::Or(a, b) => format!("(or {} {})", a.to_string(), b.to_string()),
            Expr::Impl(a, b) => format!("(impl {} {})", a.to_string(), b.to_string()),
            Expr::Equiv(a, b) => format!("(equiv {} {})", a.to_string(), b.to_string()),
        }
    }
}

/// Finds the maximum variable number used in an expression.
///
/// This is useful for determining how many variables need to be tracked
/// and for allocating auxiliary variables during Tseitin transformation.
///
/// # Arguments
///
/// * `expr` - The expression to scan for variable numbers
///
/// # Returns
///
/// The highest variable number found in the expression.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Expr, find_max_var};
///
/// let expr = Expr::And(
///     Box::new(Expr::Var(5)),
///     Box::new(Expr::Var(3)),
/// );
/// assert_eq!(find_max_var(&expr), 5);
/// ```
pub fn find_max_var(expr: &Expr) -> i32 {
    match expr {
        Expr::Var(v) => *v,
        Expr::Not(e) => find_max_var(e),
        Expr::And(e1, e2) | Expr::Or(e1, e2) | Expr::Impl(e1, e2) | Expr::Equiv(e1, e2) => {
            find_max_var(e1).max(find_max_var(e2))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_max_var() {
        let expr = Expr::And(
            Box::new(Expr::Var(5)),
            Box::new(Expr::Or(
                Box::new(Expr::Var(3)),
                Box::new(Expr::Var(10)),
            )),
        );
        assert_eq!(find_max_var(&expr), 10);
    }

    #[test]
    fn test_expr_to_string() {
        let expr = Expr::And(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Not(Box::new(Expr::Var(2)))),
        );
        assert_eq!(expr.to_string(), "(and x1 (not x2))");
    }
}
