//! Tseitin transformation for converting arbitrary boolean formulas to CNF.
//!
//! The Tseitin transformation converts any boolean formula to an equisatisfiable
//! CNF formula in polynomial time and space. It works by introducing auxiliary
//! variables that represent the result of each subformula.
//!
//! # Algorithm
//!
//! For each subformula, a fresh variable is introduced that is equivalent to
//! that subformula. The equivalence is encoded as CNF clauses:
//!
//! - **NOT**: r ↔ ¬a becomes (r ∨ a) ∧ (¬r ∨ ¬a)
//! - **AND**: r ↔ a ∧ b becomes (¬r ∨ a) ∧ (¬r ∨ b) ∧ (r ∨ ¬a ∨ ¬b)
//! - **OR**: r ↔ a ∨ b becomes (¬r ∨ a ∨ b) ∧ (r ∨ ¬a) ∧ (r ∨ ¬b)
//! - **IMPL**: r ↔ (a → b) becomes (¬r ∨ ¬a ∨ b) ∧ (r ∨ a) ∧ (r ∨ ¬b)
//! - **EQUIV**: r ↔ (a ↔ b) becomes 4 clauses encoding both directions
//!
//! Finally, a unit clause is added asserting that the root variable is true.

use crate::{Clause, Expr, Literal};

/// Transforms boolean expressions to CNF using Tseitin transformation.
///
/// This struct maintains state during the transformation, including the
/// next available variable number and the accumulated clauses.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Expr, TseitinTransformer, find_max_var};
///
/// let expr = Expr::And(
///     Box::new(Expr::Var(1)),
///     Box::new(Expr::Not(Box::new(Expr::Var(2)))),
/// );
///
/// let max_var = find_max_var(&expr);
/// let mut transformer = TseitinTransformer::new(max_var);
/// let root = transformer.transform(&expr);
/// let clauses = transformer.into_clauses(root);
/// ```
pub struct TseitinTransformer {
    /// The next variable number to allocate for auxiliary variables.
    next_var: i32,
    /// The accumulated CNF clauses.
    clauses: Vec<Clause>,
}

impl TseitinTransformer {
    /// Creates a new transformer.
    ///
    /// Auxiliary variables will be numbered starting from `max_var + 1`.
    ///
    /// # Arguments
    ///
    /// * `max_var` - The maximum variable number used in the original formula
    pub fn new(max_var: i32) -> Self {
        TseitinTransformer {
            next_var: max_var + 1,
            clauses: Vec::new(),
        }
    }

    /// Allocates a fresh auxiliary variable.
    ///
    /// Each call returns a new, unique variable number.
    fn fresh_var(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    /// Transforms an expression, returning the variable representing its result.
    ///
    /// This recursively transforms subexpressions and generates clauses
    /// that encode the equivalence between each result variable and its
    /// corresponding subformula.
    ///
    /// # Arguments
    ///
    /// * `expr` - The expression to transform
    ///
    /// # Returns
    ///
    /// The variable number representing this expression's result.
    pub fn transform(&mut self, expr: &Expr) -> i32 {
        enum Task<'a> {
            Visit(&'a Expr),
            BuildNot,
            BuildAnd,
            BuildOr,
            BuildImpl,
            BuildEquiv,
        }

        let mut stack: Vec<Task> = vec![Task::Visit(expr)];
        let mut results: Vec<i32> = Vec::new();

        while let Some(task) = stack.pop() {
            match task {
                Task::Visit(e) => match e {
                    Expr::Var(v) => results.push(*v),
                    Expr::Not(inner) => {
                        stack.push(Task::BuildNot);
                        stack.push(Task::Visit(inner));
                    }
                    Expr::And(a, b) => {
                        stack.push(Task::BuildAnd);
                        stack.push(Task::Visit(b));
                        stack.push(Task::Visit(a));
                    }
                    Expr::Or(a, b) => {
                        stack.push(Task::BuildOr);
                        stack.push(Task::Visit(b));
                        stack.push(Task::Visit(a));
                    }
                    Expr::Impl(a, b) => {
                        stack.push(Task::BuildImpl);
                        stack.push(Task::Visit(b));
                        stack.push(Task::Visit(a));
                    }
                    Expr::Equiv(a, b) => {
                        stack.push(Task::BuildEquiv);
                        stack.push(Task::Visit(b));
                        stack.push(Task::Visit(a));
                    }
                },
                Task::BuildNot => {
                    let sub = results.pop().unwrap();
                    let result = self.fresh_var();
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::positive(sub),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::negative(sub),
                    ]));
                    results.push(result);
                }
                Task::BuildAnd => {
                    let sub2 = results.pop().unwrap();
                    let sub1 = results.pop().unwrap();
                    let result = self.fresh_var();
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::positive(sub1),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::positive(sub2),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::negative(sub1),
                        Literal::negative(sub2),
                    ]));
                    results.push(result);
                }
                Task::BuildOr => {
                    let sub2 = results.pop().unwrap();
                    let sub1 = results.pop().unwrap();
                    let result = self.fresh_var();
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::positive(sub1),
                        Literal::positive(sub2),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::negative(sub1),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::negative(sub2),
                    ]));
                    results.push(result);
                }
                Task::BuildImpl => {
                    let sub2 = results.pop().unwrap();
                    let sub1 = results.pop().unwrap();
                    let result = self.fresh_var();
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::negative(sub1),
                        Literal::positive(sub2),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::positive(sub1),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::negative(sub2),
                    ]));
                    results.push(result);
                }
                Task::BuildEquiv => {
                    let sub2 = results.pop().unwrap();
                    let sub1 = results.pop().unwrap();
                    let result = self.fresh_var();
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::negative(sub1),
                        Literal::positive(sub2),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::negative(result),
                        Literal::negative(sub2),
                        Literal::positive(sub1),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::positive(sub1),
                        Literal::positive(sub2),
                    ]));
                    self.clauses.push(Clause::new(vec![
                        Literal::positive(result),
                        Literal::negative(sub1),
                        Literal::negative(sub2),
                    ]));
                    results.push(result);
                }
            }
        }

        results.pop().unwrap()
    }

    /// Finalizes the transformation and returns the CNF clauses.
    ///
    /// This adds a unit clause asserting that the root variable is true,
    /// then returns all accumulated clauses.
    ///
    /// # Arguments
    ///
    /// * `root_var` - The variable representing the entire formula
    ///
    /// # Returns
    ///
    /// A vector of clauses that together are equisatisfiable with the
    /// original formula.
    pub fn into_clauses(mut self, root_var: i32) -> Vec<Clause> {
        self.clauses.push(Clause::unit(Literal::positive(root_var)));
        self.clauses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::find_max_var;

    #[test]
    fn test_tseitin_single_var() {
        let expr = Expr::Var(1);
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        assert_eq!(root, 1);
        assert!(transformer.clauses.is_empty());
    }

    #[test]
    fn test_tseitin_not() {
        let expr = Expr::Not(Box::new(Expr::Var(1)));
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        // root should be a fresh variable (2)
        assert_eq!(root, 2);
        // NOT creates 2 clauses
        assert_eq!(transformer.clauses.len(), 2);
    }

    #[test]
    fn test_tseitin_and() {
        let expr = Expr::And(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        // AND creates 3 clauses
        assert_eq!(transformer.clauses.len(), 3);
        assert_eq!(root, 3);
    }

    #[test]
    fn test_tseitin_or() {
        let expr = Expr::Or(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        // OR creates 3 clauses
        assert_eq!(transformer.clauses.len(), 3);
        assert_eq!(root, 3);
    }

    #[test]
    fn test_tseitin_impl() {
        let expr = Expr::Impl(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        // IMPL creates 3 clauses
        assert_eq!(transformer.clauses.len(), 3);
        assert_eq!(root, 3);
    }

    #[test]
    fn test_tseitin_equiv() {
        let expr = Expr::Equiv(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        // EQUIV creates 4 clauses
        assert_eq!(transformer.clauses.len(), 4);
        assert_eq!(root, 3);
    }

    #[test]
    fn test_tseitin_into_clauses_adds_unit() {
        let expr = Expr::And(
            Box::new(Expr::Var(1)),
            Box::new(Expr::Var(2)),
        );
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root = transformer.transform(&expr);
        let clauses = transformer.into_clauses(root);
        // AND creates 3 clauses + 1 unit clause for root
        assert_eq!(clauses.len(), 4);
        // Last clause should be unit clause asserting root
        let last = &clauses[clauses.len() - 1];
        assert_eq!(last.literals.len(), 1);
        assert_eq!(last.literals[0].var, root);
        assert!(!last.literals[0].negated);
    }
}
