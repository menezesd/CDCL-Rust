//! DIMACS CNF SAT Solver
//!
//! Reads a SAT problem in DIMACS CNF format and solves it.
//! This is the standard format used in SAT competitions.
//!
//! DIMACS format:
//! - Lines starting with 'c' are comments
//! - 'p cnf <variables> <clauses>' declares the problem
//! - Each subsequent line is a clause: space-separated literals ending with 0
//! - Positive literal = variable is true, negative = false
//!
//! Example:
//! ```
//! c Example SAT problem
//! p cnf 3 2
//! 1 -2 3 0
//! -1 2 0
//! ```

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

fn parse_dimacs() -> Result<(usize, Vec<Clause>), String> {
    let stdin = io::stdin();
    let mut num_vars = 0;
    let mut num_clauses_expected = 0;
    let mut clauses = Vec::new();
    let mut header_seen = false;

    for line in stdin.lock().lines() {
        let line = line.map_err(|e| e.to_string())?;
        let trimmed = line.trim();

        if trimmed.is_empty() {
            continue;
        }

        // Comment line
        if trimmed.starts_with('c') {
            continue;
        }

        // Problem line
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err("Invalid problem line, expected 'p cnf <vars> <clauses>'".to_string());
            }
            num_vars = parts[2].parse().map_err(|_| "Invalid variable count")?;
            num_clauses_expected = parts[3].parse().map_err(|_| "Invalid clause count")?;
            header_seen = true;
            continue;
        }

        if !header_seen {
            return Err("Clause before problem line".to_string());
        }

        // Clause line
        let literals: Result<Vec<i32>, _> = trimmed
            .split_whitespace()
            .map(|s| s.parse::<i32>())
            .collect();

        let literals = literals.map_err(|_| "Invalid literal")?;

        // Clause ends with 0
        let clause_lits: Vec<Literal> = literals.iter()
            .take_while(|&&l| l != 0)
            .map(|&l| {
                if l > 0 {
                    Literal::positive(l)
                } else {
                    Literal::negative(-l)
                }
            })
            .collect();

        if !clause_lits.is_empty() || literals.contains(&0) {
            clauses.push(Clause::new(clause_lits));
        }
    }

    if !header_seen {
        return Err("No problem line found".to_string());
    }

    if clauses.len() != num_clauses_expected {
        eprintln!("Warning: Expected {} clauses, got {}", num_clauses_expected, clauses.len());
    }

    Ok((num_vars, clauses))
}

fn print_solution(solver: &CDCLSolver, num_vars: usize) {
    print!("v");
    for v in 1..=num_vars {
        match solver.get_value(v as i32) {
            Some(true) => print!(" {}", v),
            Some(false) => print!(" -{}", v),
            None => print!(" {}", v), // Default to positive if unassigned
        }
    }
    println!(" 0");
}

fn main() {
    let (num_vars, clauses) = match parse_dimacs() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    };

    eprintln!("c Parsed {} variables and {} clauses", num_vars, clauses.len());

    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            println!("s SATISFIABLE");
            print_solution(&solver, num_vars);
        }
        Ok(false) => {
            println!("s UNSATISFIABLE");
        }
        Err(e) => {
            eprintln!("c Solver error: {}", e);
            println!("s UNKNOWN");
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&l| {
            if l > 0 {
                Literal::positive(l)
            } else {
                Literal::negative(-l)
            }
        }).collect())
    }

    #[test]
    fn test_simple_sat() {
        // (x1 OR x2) AND (NOT x1 OR x2)
        let clauses = vec![
            make_clause(&[1, 2]),
            make_clause(&[-1, 2]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        // x2 must be true
        assert_eq!(solver.get_value(2), Some(true));
    }

    #[test]
    fn test_simple_unsat() {
        // (x1) AND (NOT x1)
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_3sat_instance() {
        // A satisfiable 3-SAT instance
        // (x1 OR x2 OR x3) AND (NOT x1 OR x2 OR x3) AND (x1 OR NOT x2 OR x3)
        let clauses = vec![
            make_clause(&[1, 2, 3]),
            make_clause(&[-1, 2, 3]),
            make_clause(&[1, -2, 3]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_contradictory_unit_clauses() {
        // Two contradictory unit clauses are unsatisfiable
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_unit_propagation() {
        // (x1) AND (NOT x1 OR x2) AND (NOT x2 OR x3)
        // Unit propagation: x1=T -> x2=T -> x3=T
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1, 2]),
            make_clause(&[-2, 3]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(true));
        assert_eq!(solver.get_value(3), Some(true));
    }
}
