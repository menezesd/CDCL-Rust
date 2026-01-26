//! Minesweeper Solver using CDCL SAT Solver
//!
//! Given a partially revealed Minesweeper board, determines which cells
//! must be mines, which must be safe, and which are uncertain.
//!
//! Input format (stdin):
//! ```
//! <rows> <cols>
//! <board>
//! ```
//! Where: 0-8 = revealed number, * = revealed mine, ? = unknown cell
//!
//! Example:
//! ```
//! 5 5
//! 1????
//! 2????
//! ?????
//! ?????
//! ?????
//! ```

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: cell (r,c) is a mine
fn var(cols: usize, row: usize, col: usize) -> i32 {
    (row * cols + col + 1) as i32
}

/// Get neighbors of a cell.
fn neighbors(rows: usize, cols: usize, r: usize, c: usize) -> Vec<(usize, usize)> {
    let mut result = Vec::new();
    for dr in -1..=1i32 {
        for dc in -1..=1i32 {
            if dr == 0 && dc == 0 {
                continue;
            }
            let nr = r as i32 + dr;
            let nc = c as i32 + dc;
            if nr >= 0 && nr < rows as i32 && nc >= 0 && nc < cols as i32 {
                result.push((nr as usize, nc as usize));
            }
        }
    }
    result
}

/// Encode "exactly k of these variables are true" constraint.
fn encode_exactly_k(vars: &[i32], k: usize) -> Vec<Clause> {
    let mut clauses = Vec::new();
    let n = vars.len();

    if k > n {
        // Impossible - add empty clause
        clauses.push(Clause::new(vec![]));
        return clauses;
    }

    // At least k: every combination of (n-k+1) variables must have at least one true
    // Encode: NOT all of any (n-k+1) variables can be false
    if k > 0 {
        for combo in combinations(n, n - k + 1) {
            let clause: Vec<Literal> = combo.iter()
                .map(|&i| Literal::positive(vars[i]))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    // At most k: every combination of (k+1) variables must have at least one false
    if k < n {
        for combo in combinations(n, k + 1) {
            let clause: Vec<Literal> = combo.iter()
                .map(|&i| Literal::negative(vars[i]))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    clauses
}

/// Generate all combinations of k elements from 0..n.
fn combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut combo = Vec::new();
    generate_combinations(n, k, 0, &mut combo, &mut result);
    result
}

fn generate_combinations(
    n: usize,
    k: usize,
    start: usize,
    current: &mut Vec<usize>,
    result: &mut Vec<Vec<usize>>,
) {
    if current.len() == k {
        result.push(current.clone());
        return;
    }
    for i in start..n {
        current.push(i);
        generate_combinations(n, k, i + 1, current, result);
        current.pop();
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Cell {
    Unknown,
    Number(u8),
    Mine,
}

fn parse_input() -> Result<(usize, usize, Vec<Vec<Cell>>), String> {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();

    let first_line = lines.next()
        .ok_or("Missing first line")?
        .map_err(|e| e.to_string())?;

    let dims: Vec<usize> = first_line
        .split_whitespace()
        .map(|s| s.parse().map_err(|_| "Invalid dimension"))
        .collect::<Result<_, _>>()?;

    if dims.len() != 2 {
        return Err("Expected 'rows cols' on first line".to_string());
    }

    let (rows, cols) = (dims[0], dims[1]);
    let mut board = Vec::new();

    for _ in 0..rows {
        let line = lines.next()
            .ok_or("Missing board row")?
            .map_err(|e| e.to_string())?;

        let row: Vec<Cell> = line.chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| match c {
                '?' | '.' => Cell::Unknown,
                '*' | 'X' => Cell::Mine,
                '0'..='8' => Cell::Number(c.to_digit(10).unwrap() as u8),
                _ => Cell::Unknown,
            })
            .collect();

        if row.len() != cols {
            return Err(format!("Expected {} columns, got {}", cols, row.len()));
        }

        board.push(row);
    }

    Ok((rows, cols, board))
}

fn generate_minesweeper_clauses(
    rows: usize,
    cols: usize,
    board: &[Vec<Cell>],
) -> Vec<Clause> {
    let mut clauses = Vec::new();

    for r in 0..rows {
        for c in 0..cols {
            match board[r][c] {
                Cell::Number(count) => {
                    // This cell is not a mine
                    clauses.push(Clause::new(vec![Literal::negative(var(cols, r, c))]));

                    // Exactly 'count' of the neighbors are mines
                    let neighs = neighbors(rows, cols, r, c);
                    let unknown_neighs: Vec<i32> = neighs.iter()
                        .filter(|&&(nr, nc)| board[nr][nc] == Cell::Unknown)
                        .map(|&(nr, nc)| var(cols, nr, nc))
                        .collect();

                    // Count already-known mines
                    let known_mines: usize = neighs.iter()
                        .filter(|&&(nr, nc)| board[nr][nc] == Cell::Mine)
                        .count();

                    if known_mines > count as usize {
                        // Contradiction
                        clauses.push(Clause::new(vec![]));
                    } else {
                        let remaining = count as usize - known_mines;
                        clauses.extend(encode_exactly_k(&unknown_neighs, remaining));
                    }
                }
                Cell::Mine => {
                    // This cell is definitely a mine
                    clauses.push(Clause::new(vec![Literal::positive(var(cols, r, c))]));
                }
                Cell::Unknown => {
                    // No constraint yet
                }
            }
        }
    }

    clauses
}

fn main() {
    let (rows, cols, board) = match parse_input() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    };

    let base_clauses = generate_minesweeper_clauses(rows, cols, &board);

    println!("Minesweeper Analysis:");
    println!("=====================");

    // For each unknown cell, check if it must be a mine or must be safe
    for r in 0..rows {
        for c in 0..cols {
            if board[r][c] != Cell::Unknown {
                continue;
            }

            let cell_var = var(cols, r, c);

            // Check if cell must be a mine (assuming it's safe leads to UNSAT)
            let mut clauses_safe = base_clauses.clone();
            clauses_safe.push(Clause::new(vec![Literal::negative(cell_var)]));
            let must_be_mine = !CDCLSolver::new(clauses_safe).solve().unwrap_or(true);

            // Check if cell must be safe (assuming it's a mine leads to UNSAT)
            let mut clauses_mine = base_clauses.clone();
            clauses_mine.push(Clause::new(vec![Literal::positive(cell_var)]));
            let must_be_safe = !CDCLSolver::new(clauses_mine).solve().unwrap_or(true);

            if must_be_mine {
                println!("Cell ({}, {}): DEFINITELY A MINE", r + 1, c + 1);
            } else if must_be_safe {
                println!("Cell ({}, {}): DEFINITELY SAFE", r + 1, c + 1);
            }
        }
    }

    // Print the board with analysis
    println!("\nBoard (M=mine, S=safe, ?=unknown):");
    for r in 0..rows {
        for c in 0..cols {
            match board[r][c] {
                Cell::Number(n) => print!("{} ", n),
                Cell::Mine => print!("* "),
                Cell::Unknown => {
                    let cell_var = var(cols, r, c);

                    let mut clauses_safe = base_clauses.clone();
                    clauses_safe.push(Clause::new(vec![Literal::negative(cell_var)]));
                    let must_be_mine = !CDCLSolver::new(clauses_safe).solve().unwrap_or(true);

                    let mut clauses_mine = base_clauses.clone();
                    clauses_mine.push(Clause::new(vec![Literal::positive(cell_var)]));
                    let must_be_safe = !CDCLSolver::new(clauses_mine).solve().unwrap_or(true);

                    if must_be_mine {
                        print!("M ");
                    } else if must_be_safe {
                        print!("S ");
                    } else {
                        print!("? ");
                    }
                }
            }
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_exactly_1_of_3() {
        let vars = vec![1, 2, 3];
        let clauses = encode_exactly_k(&vars, 1);

        // Test with exactly one true
        let mut test_clauses = clauses.clone();
        test_clauses.push(Clause::new(vec![Literal::positive(1)]));
        test_clauses.push(Clause::new(vec![Literal::negative(2)]));
        test_clauses.push(Clause::new(vec![Literal::negative(3)]));

        let mut solver = CDCLSolver::new(test_clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_simple_minesweeper() {
        // 1 ?
        // ? ?
        // The '1' means exactly one of the 3 neighbors is a mine
        let board = vec![
            vec![Cell::Number(1), Cell::Unknown],
            vec![Cell::Unknown, Cell::Unknown],
        ];
        let clauses = generate_minesweeper_clauses(2, 2, &board);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_corner_with_1() {
        // 1 ?
        // A corner '1' with one unknown neighbor - that neighbor must be a mine
        let board = vec![
            vec![Cell::Number(1), Cell::Unknown],
        ];
        let clauses = generate_minesweeper_clauses(1, 2, &board);

        // The unknown cell must be a mine
        let cell_var = var(2, 0, 1);
        let mut clauses_safe = clauses.clone();
        clauses_safe.push(Clause::new(vec![Literal::negative(cell_var)]));
        assert!(!CDCLSolver::new(clauses_safe).solve().unwrap());
    }
}
