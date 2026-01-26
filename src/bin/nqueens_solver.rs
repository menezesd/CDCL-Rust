//! N-Queens Solver using CDCL SAT Solver
//!
//! Places N queens on an NxN chessboard such that no two queens attack each other.
//!
//! Usage: nqueens_solver <N>
//! Output: Board with Q for queens, . for empty cells

use std::env;
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Convert (row, col) to variable number for an NxN board.
/// row, col are 1-indexed.
fn var(n: usize, row: usize, col: usize) -> i32 {
    debug_assert!(row >= 1 && row <= n);
    debug_assert!(col >= 1 && col <= n);
    ((row - 1) * n + col) as i32
}

/// Generate all N-Queens constraints as CNF clauses.
fn generate_nqueens_clauses(n: usize) -> Vec<Clause> {
    let mut clauses = Vec::new();

    // 1. Each row has at least one queen
    for r in 1..=n {
        let clause: Vec<Literal> = (1..=n)
            .map(|c| Literal::positive(var(n, r, c)))
            .collect();
        clauses.push(Clause::new(clause));
    }

    // 2. Each row has at most one queen
    for r in 1..=n {
        for c1 in 1..=n {
            for c2 in (c1 + 1)..=n {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(n, r, c1)),
                    Literal::negative(var(n, r, c2)),
                ]));
            }
        }
    }

    // 3. Each column has at least one queen
    for c in 1..=n {
        let clause: Vec<Literal> = (1..=n)
            .map(|r| Literal::positive(var(n, r, c)))
            .collect();
        clauses.push(Clause::new(clause));
    }

    // 4. Each column has at most one queen
    for c in 1..=n {
        for r1 in 1..=n {
            for r2 in (r1 + 1)..=n {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(n, r1, c)),
                    Literal::negative(var(n, r2, c)),
                ]));
            }
        }
    }

    // 5. No two queens on same diagonal (top-left to bottom-right)
    // For each pair of cells on the same diagonal
    for r1 in 1..=n {
        for c1 in 1..=n {
            for r2 in (r1 + 1)..=n {
                let c2 = c1 as i32 + (r2 as i32 - r1 as i32);
                if c2 >= 1 && c2 <= n as i32 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(n, r1, c1)),
                        Literal::negative(var(n, r2, c2 as usize)),
                    ]));
                }
            }
        }
    }

    // 6. No two queens on same anti-diagonal (top-right to bottom-left)
    for r1 in 1..=n {
        for c1 in 1..=n {
            for r2 in (r1 + 1)..=n {
                let c2 = c1 as i32 - (r2 as i32 - r1 as i32);
                if c2 >= 1 && c2 <= n as i32 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(n, r1, c1)),
                        Literal::negative(var(n, r2, c2 as usize)),
                    ]));
                }
            }
        }
    }

    clauses
}

/// Extract and print the solution.
fn print_solution(solver: &CDCLSolver, n: usize) {
    for r in 1..=n {
        for c in 1..=n {
            if solver.get_value(var(n, r, c)) == Some(true) {
                print!("Q ");
            } else {
                print!(". ");
            }
        }
        println!();
    }
}

/// Count total solutions (for small N).
fn count_solutions(n: usize) -> usize {
    let base_clauses = generate_nqueens_clauses(n);
    let mut count = 0;
    let mut blocking_clauses: Vec<Clause> = Vec::new();

    loop {
        let mut all_clauses = base_clauses.clone();
        all_clauses.extend(blocking_clauses.clone());

        let mut solver = CDCLSolver::new(all_clauses);
        match solver.solve() {
            Ok(true) => {
                count += 1;
                // Add blocking clause to exclude this solution
                let mut blocking: Vec<Literal> = Vec::new();
                for r in 1..=n {
                    for c in 1..=n {
                        let v = var(n, r, c);
                        if solver.get_value(v) == Some(true) {
                            blocking.push(Literal::negative(v));
                        }
                    }
                }
                blocking_clauses.push(Clause::new(blocking));
            }
            Ok(false) => break,
            Err(_) => break,
        }
    }

    count
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <N> [--count]", args[0]);
        eprintln!("  N: board size (e.g., 8 for 8-queens)");
        eprintln!("  --count: count all solutions instead of printing one");
        process::exit(1);
    }

    let n: usize = match args[1].parse() {
        Ok(n) if n >= 1 => n,
        _ => {
            eprintln!("Error: N must be a positive integer");
            process::exit(1);
        }
    };

    let count_mode = args.len() > 2 && args[2] == "--count";

    if count_mode {
        let count = count_solutions(n);
        println!("{}-Queens has {} solutions", n, count);
    } else {
        let clauses = generate_nqueens_clauses(n);
        let mut solver = CDCLSolver::new(clauses);

        match solver.solve() {
            Ok(true) => {
                println!("{}-Queens solution:", n);
                print_solution(&solver, n);
            }
            Ok(false) => {
                println!("No solution exists for {}-Queens", n);
            }
            Err(e) => {
                eprintln!("Solver error: {}", e);
                process::exit(1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_encoding() {
        assert_eq!(var(8, 1, 1), 1);
        assert_eq!(var(8, 1, 8), 8);
        assert_eq!(var(8, 2, 1), 9);
        assert_eq!(var(8, 8, 8), 64);
    }

    #[test]
    fn test_4_queens_solvable() {
        let clauses = generate_nqueens_clauses(4);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_3_queens_unsolvable() {
        let clauses = generate_nqueens_clauses(3);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_2_queens_unsolvable() {
        let clauses = generate_nqueens_clauses(2);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_1_queen_solvable() {
        let clauses = generate_nqueens_clauses(1);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_8_queens_solvable() {
        let clauses = generate_nqueens_clauses(8);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_count_4_queens() {
        assert_eq!(count_solutions(4), 2);
    }

    #[test]
    fn test_count_5_queens() {
        assert_eq!(count_solutions(5), 10);
    }
}
