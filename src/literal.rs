//! Literal and Clause types for CNF representation.
//!
//! This module defines the basic building blocks of CNF (Conjunctive Normal Form)
//! formulas: literals (possibly negated variables) and clauses (disjunctions of literals).

/// A literal is a variable or its negation.
///
/// In SAT solving, literals are the atomic units that appear in clauses.
/// Each literal references a variable by its positive integer ID and tracks
/// whether the literal is negated.
///
/// # Example
///
/// ```
/// use cdcl_sat::Literal;
///
/// let pos = Literal::positive(1);  // x1
/// let neg = Literal::negative(1);  // ¬x1
///
/// assert_eq!(pos.as_signed(), 1);
/// assert_eq!(neg.as_signed(), -1);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    /// The variable number (always positive).
    pub var: i32,
    /// Whether this literal is negated.
    pub negated: bool,
}

impl Literal {
    /// Creates a positive (non-negated) literal for the given variable.
    ///
    /// # Arguments
    ///
    /// * `var` - The variable number (should be >= 1)
    #[inline]
    pub fn positive(var: i32) -> Self {
        Literal { var, negated: false }
    }

    /// Creates a negative (negated) literal for the given variable.
    ///
    /// # Arguments
    ///
    /// * `var` - The variable number (should be >= 1)
    #[inline]
    pub fn negative(var: i32) -> Self {
        Literal { var, negated: true }
    }

    /// Converts the literal to its signed integer representation.
    ///
    /// This is the standard DIMACS format where positive integers represent
    /// positive literals and negative integers represent negated literals.
    ///
    /// # Returns
    ///
    /// - `var` if the literal is positive
    /// - `-var` if the literal is negated
    #[inline]
    pub fn as_signed(self) -> i32 {
        if self.negated { -self.var } else { self.var }
    }
}

/// A clause is a disjunction (OR) of literals.
///
/// In CNF, a formula is a conjunction (AND) of clauses, where each clause
/// is satisfied if at least one of its literals is true.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Clause, Literal};
///
/// // Create the clause (x1 OR ¬x2 OR x3)
/// let clause = Clause::new(vec![
///     Literal::positive(1),
///     Literal::negative(2),
///     Literal::positive(3),
/// ]);
/// ```
#[derive(Debug, Clone)]
pub struct Clause {
    /// The literals in this clause.
    pub literals: Vec<Literal>,
}

impl Clause {
    /// Creates a new clause with the given literals.
    ///
    /// # Arguments
    ///
    /// * `literals` - The literals that form this disjunction
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    /// Creates a unit clause containing a single literal.
    ///
    /// Unit clauses are important in SAT solving because they force
    /// a specific assignment for their variable.
    ///
    /// # Arguments
    ///
    /// * `lit` - The single literal in this clause
    pub fn unit(lit: Literal) -> Self {
        Clause { literals: vec![lit] }
    }

    /// Returns true if this is a unit clause (contains exactly one literal).
    #[inline]
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Returns the number of literals in this clause.
    #[inline]
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Returns true if this clause is empty (always false).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_positive_literal() {
        let lit = Literal::positive(5);
        assert_eq!(lit.var, 5);
        assert!(!lit.negated);
        assert_eq!(lit.as_signed(), 5);
    }

    #[test]
    fn test_negative_literal() {
        let lit = Literal::negative(5);
        assert_eq!(lit.var, 5);
        assert!(lit.negated);
        assert_eq!(lit.as_signed(), -5);
    }

    #[test]
    fn test_literal_equality() {
        let lit1 = Literal::positive(3);
        let lit2 = Literal::positive(3);
        let lit3 = Literal::negative(3);
        assert_eq!(lit1, lit2);
        assert_ne!(lit1, lit3);
    }

    #[test]
    fn test_clause_creation() {
        let clause = Clause::new(vec![
            Literal::positive(1),
            Literal::negative(2),
        ]);
        assert_eq!(clause.len(), 2);
        assert!(!clause.is_unit());
        assert!(!clause.is_empty());
    }

    #[test]
    fn test_unit_clause() {
        let clause = Clause::unit(Literal::positive(7));
        assert_eq!(clause.len(), 1);
        assert!(clause.is_unit());
        assert_eq!(clause.literals[0].var, 7);
    }
}
