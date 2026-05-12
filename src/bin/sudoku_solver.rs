//! Sudoku Solver using CDCL SAT Solver
//!
//! Encodes a Sudoku puzzle as a boolean satisfiability problem and solves it.
//!
//! Usage: echo "530070000600195000..." | sudoku_solver
//! Input: 81-character string (0 = empty cell, 1-9 = given digits)
//! Output: Solved 9x9 grid or "UNSOLVABLE"

use std::io::{self, Read};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Convert (row, col, digit) to variable number.
/// row, col, digit are 1-indexed (1-9).
/// Returns a variable number from 1 to 729.
fn var(row: usize, col: usize, digit: usize) -> i32 {
    debug_assert!((1..=9).contains(&row));
    debug_assert!((1..=9).contains(&col));
    debug_assert!((1..=9).contains(&digit));
    (81 * (row - 1) + 9 * (col - 1) + digit) as i32
}

/// Decode variable number back to (row, col, digit).
fn decode_var(v: i32) -> (usize, usize, usize) {
    let v = v as usize - 1;
    let row = v / 81 + 1;
    let col = (v % 81) / 9 + 1;
    let digit = v % 9 + 1;
    (row, col, digit)
}

/// Generate all Sudoku constraints as CNF clauses.
fn generate_sudoku_clauses(clues: &[(usize, usize, usize)]) -> Vec<Clause> {
    let mut clauses = Vec::new();

    // 1. Each cell contains at least one digit
    for r in 1..=9 {
        for c in 1..=9 {
            let clause: Vec<Literal> = (1..=9)
                .map(|d| Literal::positive(var(r, c, d)))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    // 2. Each cell contains at most one digit (no two digits in same cell)
    for r in 1..=9 {
        for c in 1..=9 {
            for d1 in 1..=9 {
                for d2 in (d1 + 1)..=9 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(r, c, d1)),
                        Literal::negative(var(r, c, d2)),
                    ]));
                }
            }
        }
    }

    // 3. Each row contains each digit at least once
    for r in 1..=9 {
        for d in 1..=9 {
            let clause: Vec<Literal> = (1..=9)
                .map(|c| Literal::positive(var(r, c, d)))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    // 4. Each row contains each digit at most once
    for r in 1..=9 {
        for d in 1..=9 {
            for c1 in 1..=9 {
                for c2 in (c1 + 1)..=9 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(r, c1, d)),
                        Literal::negative(var(r, c2, d)),
                    ]));
                }
            }
        }
    }

    // 5. Each column contains each digit at least once
    for c in 1..=9 {
        for d in 1..=9 {
            let clause: Vec<Literal> = (1..=9)
                .map(|r| Literal::positive(var(r, c, d)))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    // 6. Each column contains each digit at most once
    for c in 1..=9 {
        for d in 1..=9 {
            for r1 in 1..=9 {
                for r2 in (r1 + 1)..=9 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(r1, c, d)),
                        Literal::negative(var(r2, c, d)),
                    ]));
                }
            }
        }
    }

    // 7. Each 3x3 box contains each digit at least once
    for box_r in 0..3 {
        for box_c in 0..3 {
            for d in 1..=9 {
                let mut clause = Vec::new();
                for dr in 0..3 {
                    for dc in 0..3 {
                        let r = box_r * 3 + dr + 1;
                        let c = box_c * 3 + dc + 1;
                        clause.push(Literal::positive(var(r, c, d)));
                    }
                }
                clauses.push(Clause::new(clause));
            }
        }
    }

    // 8. Each 3x3 box contains each digit at most once
    for box_r in 0..3 {
        for box_c in 0..3 {
            for d in 1..=9 {
                let cells: Vec<(usize, usize)> = (0..3)
                    .flat_map(|dr| (0..3).map(move |dc| (box_r * 3 + dr + 1, box_c * 3 + dc + 1)))
                    .collect();
                for i in 0..cells.len() {
                    for j in (i + 1)..cells.len() {
                        let (r1, c1) = cells[i];
                        let (r2, c2) = cells[j];
                        clauses.push(Clause::new(vec![
                            Literal::negative(var(r1, c1, d)),
                            Literal::negative(var(r2, c2, d)),
                        ]));
                    }
                }
            }
        }
    }

    // 9. Add clues as unit clauses
    for &(r, c, d) in clues {
        clauses.push(Clause::new(vec![Literal::positive(var(r, c, d))]));
    }

    clauses
}

/// Parse a Sudoku puzzle string into clues.
/// Input: 81-character string where '0' or '.' = empty, '1'-'9' = given digit.
fn parse_puzzle(input: &str) -> Result<Vec<(usize, usize, usize)>, String> {
    let chars: Vec<char> = input.chars().filter(|c| !c.is_whitespace()).collect();

    if chars.len() != 81 {
        return Err(format!(
            "Expected 81 characters, got {}",
            chars.len()
        ));
    }

    let mut clues = Vec::new();
    for (i, ch) in chars.iter().enumerate() {
        let row = i / 9 + 1;
        let col = i % 9 + 1;
        match ch {
            '1'..='9' => {
                let digit = ch.to_digit(10).unwrap() as usize;
                clues.push((row, col, digit));
            }
            '0' | '.' => {}
            _ => return Err(format!("Invalid character '{ch}' at position {i}")),
        }
    }

    Ok(clues)
}

/// Extract solution from solver's assignment.
fn extract_solution(solver: &CDCLSolver) -> Option<[[u8; 9]; 9]> {
    let mut grid = [[0u8; 9]; 9];

    for v in 1i32..=729 {
        if solver.get_value(v) == Some(true) {
            let (row, col, digit) = decode_var(v);
            if grid[row - 1][col - 1] != 0 {
                return None; // Multiple digits in same cell
            }
            grid[row - 1][col - 1] = digit as u8;
        }
    }

    // Verify all cells are filled
    for row in &grid {
        for &cell in row {
            if cell == 0 {
                return None;
            }
        }
    }

    Some(grid)
}

/// Print the Sudoku grid.
fn print_grid(grid: &[[u8; 9]; 9]) {
    for (i, row) in grid.iter().enumerate() {
        if i > 0 && i % 3 == 0 {
            println!("------+-------+------");
        }
        for (j, &digit) in row.iter().enumerate() {
            if j > 0 && j % 3 == 0 {
                print!("| ");
            }
            print!("{digit} ");
        }
        println!();
    }
}

fn main() {
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("Error reading input: {e}");
        process::exit(1);
    }

    let clues = match parse_puzzle(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(1);
        }
    };

    let clauses = generate_sudoku_clauses(&clues);
    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            if let Some(grid) = extract_solution(&solver) {
                print_grid(&grid);
            } else {
                eprintln!("Error: Could not extract valid solution from SAT result");
                process::exit(1);
            }
        }
        Ok(false) => {
            println!("UNSOLVABLE");
        }
        Err(e) => {
            eprintln!("Solver error: {e}");
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_encoding() {
        assert_eq!(var(1, 1, 1), 1i32);
        assert_eq!(var(1, 1, 9), 9i32);
        assert_eq!(var(1, 2, 1), 10i32);
        assert_eq!(var(2, 1, 1), 82i32);
        assert_eq!(var(9, 9, 9), 729i32);
    }

    #[test]
    fn test_var_decode_roundtrip() {
        for r in 1..=9 {
            for c in 1..=9 {
                for d in 1..=9 {
                    let v = var(r, c, d);
                    let (r2, c2, d2) = decode_var(v);
                    assert_eq!((r, c, d), (r2, c2, d2));
                }
            }
        }
    }

    #[test]
    fn test_parse_puzzle() {
        let puzzle = "530070000600195000098000060800060003400803001700020006060000280000419005000080079";
        let clues = parse_puzzle(puzzle).unwrap();
        assert!(clues.contains(&(1, 1, 5)));
        assert!(clues.contains(&(1, 2, 3)));
        assert!(!clues.iter().any(|&(r, c, _)| r == 1 && c == 4)); // 0 = empty
    }

    #[test]
    fn test_parse_puzzle_with_dots() {
        let puzzle = "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79";
        let clues = parse_puzzle(puzzle).unwrap();
        assert!(clues.contains(&(1, 1, 5)));
    }

    #[test]
    fn test_clause_count() {
        let clauses = generate_sudoku_clauses(&[]);
        // Cell constraints: 81 (at least one) + 81*36 (at most one) = 81 + 2916 = 2997
        // Row constraints: 81 (at least one) + 81*36 (at most one) = 2997
        // Col constraints: 81 (at least one) + 81*36 (at most one) = 2997
        // Box constraints: 81 (at least one) + 81*36 (at most one) = 2997
        // Total: 4 * 2997 = 11988 clauses for empty puzzle
        assert!(clauses.len() > 10000);
    }
}
