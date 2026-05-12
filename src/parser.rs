//! Parser for boolean expressions in prefix notation.
//!
//! This module provides a parser that converts string representations of
//! boolean formulas into an AST (`Expr`).
//!
//! # Syntax
//!
//! The parser accepts formulas in prefix (Polish) notation:
//! - Variables: `x1`, `x2`, `x3`, etc. (optionally parenthesized: `(x1)`)
//! - Negation: `(not expr)`
//! - Conjunction: `(and expr1 expr2)`
//! - Disjunction: `(or expr1 expr2)`
//! - Implication: `(impl expr1 expr2)`
//! - Equivalence: `(equiv expr1 expr2)`
//!
//! # Example
//!
//! ```
//! use cdcl_sat::{Parser, Expr};
//!
//! let mut parser = Parser::new("(and x1 (not x2))");
//! let expr = parser.parse().unwrap();
//! ```

use std::collections::VecDeque;
use std::fmt;

use crate::Expr;

/// Errors that can occur during parsing.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// An unknown operator was encountered.
    /// Contains the unrecognized operator string.
    UnknownOperator(String),

    /// A variable number could not be parsed.
    /// Contains the invalid variable string.
    InvalidVariable(String),

    /// An unexpected token was encountered.
    /// Contains a description of what was found.
    UnexpectedToken(String),

    /// Expected a specific token but found something else.
    /// Contains the expected token and what was actually found.
    ExpectedToken {
        expected: String,
        found: String,
    },

    /// The input ended unexpectedly.
    UnexpectedEndOfInput,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnknownOperator(op) => write!(f, "Unknown operator: '{op}'"),
            ParseError::InvalidVariable(var) => write!(f, "Invalid variable: '{var}'"),
            ParseError::UnexpectedToken(tok) => write!(f, "Unexpected token: {tok}"),
            ParseError::ExpectedToken { expected, found } => {
                write!(f, "Expected '{expected}', found '{found}'")
            }
            ParseError::UnexpectedEndOfInput => write!(f, "Unexpected end of input"),
        }
    }
}

impl std::error::Error for ParseError {}

/// A parser for boolean expressions in prefix notation.
///
/// The parser tokenizes the input and then recursively builds an AST.
///
/// # Example
///
/// ```
/// use cdcl_sat::{Parser, Expr};
///
/// let mut parser = Parser::new("(or x1 x2)");
/// match parser.parse() {
///     Ok(expr) => println!("Parsed: {:?}", expr),
///     Err(e) => eprintln!("Parse error: {}", e),
/// }
/// ```
pub struct Parser {
    tokens: VecDeque<String>,
}

impl Parser {
    /// Creates a new parser for the given input string.
    ///
    /// The input is immediately tokenized during construction.
    ///
    /// # Arguments
    ///
    /// * `input` - The string to parse
    pub fn new(input: &str) -> Self {
        let mut tokens = VecDeque::new();
        let mut current = String::new();

        for c in input.chars() {
            match c {
                '(' | ')' => {
                    if !current.is_empty() {
                        tokens.push_back(std::mem::take(&mut current));
                    }
                    tokens.push_back(c.to_string());
                }
                c if c.is_whitespace() => {
                    if !current.is_empty() {
                        tokens.push_back(std::mem::take(&mut current));
                    }
                }
                _ => current.push(c),
            }
        }
        if !current.is_empty() {
            tokens.push_back(current);
        }

        Parser { tokens }
    }

    /// Returns a reference to the next token without consuming it.
    fn peek(&self) -> Option<&str> {
        self.tokens.front().map(std::string::String::as_str)
    }

    /// Consumes and returns the next token.
    fn consume(&mut self) -> Option<String> {
        self.tokens.pop_front()
    }

    /// Parses the input and returns the resulting expression.
    ///
    /// # Returns
    ///
    /// - `Ok(Expr)` if parsing succeeds
    /// - `Err(ParseError)` if there's a syntax error
    ///
    /// # Example
    ///
    /// ```
    /// use cdcl_sat::Parser;
    ///
    /// let mut parser = Parser::new("(and x1 x2)");
    /// let expr = parser.parse().expect("Failed to parse");
    /// ```
    pub fn parse(&mut self) -> Result<Expr, ParseError> {
        // Iterative parser using an explicit task stack to avoid stack overflow
        // on deeply nested inputs.
        enum Task {
            Parse,
            BuildNot,
            BuildAnd,
            BuildOr,
            BuildImpl,
            BuildEquiv,
            ExpectClose,
        }

        let mut task_stack: Vec<Task> = vec![Task::Parse];
        let mut results: Vec<Expr> = Vec::new();

        while let Some(task) = task_stack.pop() {
            match task {
                Task::Parse => {
                    match self.peek() {
                        Some("(") => {
                            self.consume();
                            let op = self.consume().ok_or(ParseError::UnexpectedEndOfInput)?;
                            match op.as_str() {
                                "not" => {
                                    task_stack.push(Task::ExpectClose);
                                    task_stack.push(Task::BuildNot);
                                    task_stack.push(Task::Parse);
                                }
                                "and" => {
                                    task_stack.push(Task::ExpectClose);
                                    task_stack.push(Task::BuildAnd);
                                    task_stack.push(Task::Parse);
                                    task_stack.push(Task::Parse);
                                }
                                "or" => {
                                    task_stack.push(Task::ExpectClose);
                                    task_stack.push(Task::BuildOr);
                                    task_stack.push(Task::Parse);
                                    task_stack.push(Task::Parse);
                                }
                                "impl" => {
                                    task_stack.push(Task::ExpectClose);
                                    task_stack.push(Task::BuildImpl);
                                    task_stack.push(Task::Parse);
                                    task_stack.push(Task::Parse);
                                }
                                "equiv" => {
                                    task_stack.push(Task::ExpectClose);
                                    task_stack.push(Task::BuildEquiv);
                                    task_stack.push(Task::Parse);
                                    task_stack.push(Task::Parse);
                                }
                                _ => {
                                    if let Some(num_str) = op.strip_prefix('x') {
                                        let var_num: i32 = num_str
                                            .parse()
                                            .map_err(|_| ParseError::InvalidVariable(op.clone()))?;
                                        self.expect(")")?;
                                        results.push(Expr::Var(var_num));
                                    } else {
                                        return Err(ParseError::UnknownOperator(op));
                                    }
                                }
                            }
                        }
                        Some(s) if s.starts_with('x') => {
                            let var = self.consume().unwrap();
                            let num_str = var.strip_prefix('x').unwrap();
                            let var_num: i32 = num_str
                                .parse()
                                .map_err(|_| ParseError::InvalidVariable(var.clone()))?;
                            results.push(Expr::Var(var_num));
                        }
                        Some(other) => return Err(ParseError::UnexpectedToken(other.to_string())),
                        None => return Err(ParseError::UnexpectedEndOfInput),
                    }
                }
                Task::BuildNot => {
                    let inner = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    results.push(Expr::Not(Box::new(inner)));
                }
                Task::BuildAnd => {
                    let right = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    let left = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    results.push(Expr::And(Box::new(left), Box::new(right)));
                }
                Task::BuildOr => {
                    let right = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    let left = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    results.push(Expr::Or(Box::new(left), Box::new(right)));
                }
                Task::BuildImpl => {
                    let right = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    let left = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    results.push(Expr::Impl(Box::new(left), Box::new(right)));
                }
                Task::BuildEquiv => {
                    let right = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    let left = results.pop().ok_or(ParseError::UnexpectedEndOfInput)?;
                    results.push(Expr::Equiv(Box::new(left), Box::new(right)));
                }
                Task::ExpectClose => {
                    self.expect(")")?;
                }
            }
        }

        results.pop().ok_or(ParseError::UnexpectedEndOfInput)
    }

    /// Expects and consumes a specific token.
    ///
    /// # Arguments
    ///
    /// * `expected` - The token string that should appear next
    ///
    /// # Returns
    ///
    /// - `Ok(())` if the expected token was found and consumed
    /// - `Err(ParseError::ExpectedToken)` if a different token was found
    fn expect(&mut self, expected: &str) -> Result<(), ParseError> {
        let token = self.consume();
        if token.as_deref() != Some(expected) {
            return Err(ParseError::ExpectedToken {
                expected: expected.to_string(),
                found: token.unwrap_or_else(|| "end of input".to_string()),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_single_variable() {
        let mut parser = Parser::new("x1");
        let expr = parser.parse().unwrap();
        assert!(matches!(expr, Expr::Var(1)));
    }

    #[test]
    fn test_parse_variable_with_parens() {
        let mut parser = Parser::new("(x42)");
        let expr = parser.parse().unwrap();
        assert!(matches!(expr, Expr::Var(42)));
    }

    #[test]
    fn test_parse_not() {
        let mut parser = Parser::new("(not x1)");
        let expr = parser.parse().unwrap();
        if let Expr::Not(inner) = expr {
            assert!(matches!(*inner, Expr::Var(1)));
        } else {
            panic!("Expected Not expression");
        }
    }

    #[test]
    fn test_parse_and() {
        let mut parser = Parser::new("(and x1 x2)");
        let expr = parser.parse().unwrap();
        if let Expr::And(left, right) = expr {
            assert!(matches!(*left, Expr::Var(1)));
            assert!(matches!(*right, Expr::Var(2)));
        } else {
            panic!("Expected And expression");
        }
    }

    #[test]
    fn test_parse_or() {
        let mut parser = Parser::new("(or x3 x4)");
        let expr = parser.parse().unwrap();
        if let Expr::Or(left, right) = expr {
            assert!(matches!(*left, Expr::Var(3)));
            assert!(matches!(*right, Expr::Var(4)));
        } else {
            panic!("Expected Or expression");
        }
    }

    #[test]
    fn test_parse_impl() {
        let mut parser = Parser::new("(impl x1 x2)");
        let expr = parser.parse().unwrap();
        if let Expr::Impl(left, right) = expr {
            assert!(matches!(*left, Expr::Var(1)));
            assert!(matches!(*right, Expr::Var(2)));
        } else {
            panic!("Expected Impl expression");
        }
    }

    #[test]
    fn test_parse_equiv() {
        let mut parser = Parser::new("(equiv x1 x2)");
        let expr = parser.parse().unwrap();
        if let Expr::Equiv(left, right) = expr {
            assert!(matches!(*left, Expr::Var(1)));
            assert!(matches!(*right, Expr::Var(2)));
        } else {
            panic!("Expected Equiv expression");
        }
    }

    #[test]
    fn test_parse_nested() {
        let mut parser = Parser::new("(and (or x1 x2) (not x3))");
        let expr = parser.parse().unwrap();
        if let Expr::And(left, right) = expr {
            assert!(matches!(*left, Expr::Or(_, _)));
            assert!(matches!(*right, Expr::Not(_)));
        } else {
            panic!("Expected nested And expression");
        }
    }

    #[test]
    fn test_parse_deeply_nested() {
        let mut parser = Parser::new("(and (or (not x1) x2) (impl x3 (equiv x4 x5)))");
        let expr = parser.parse().unwrap();
        assert!(matches!(expr, Expr::And(_, _)));
    }

    #[test]
    fn test_parse_whitespace_handling() {
        let mut parser = Parser::new("  (  and   x1    x2  )  ");
        let expr = parser.parse().unwrap();
        assert!(matches!(expr, Expr::And(_, _)));
    }

    #[test]
    fn test_parse_large_variable_number() {
        let mut parser = Parser::new("x999");
        let expr = parser.parse().unwrap();
        assert!(matches!(expr, Expr::Var(999)));
    }

    #[test]
    fn test_parse_error_unknown_operator() {
        let mut parser = Parser::new("(foo x1 x2)");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::UnknownOperator(_))));
    }

    #[test]
    fn test_parse_error_invalid_variable() {
        let mut parser = Parser::new("xabc");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::InvalidVariable(_))));
    }

    #[test]
    fn test_parse_error_unexpected_token() {
        let mut parser = Parser::new("123");
        let result = parser.parse();
        assert!(matches!(result, Err(ParseError::UnexpectedToken(_))));
    }
}
