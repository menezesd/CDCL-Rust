//! Nonogram (Picross) Solver using CDCL SAT Solver
//!
//! Solves grid puzzles where row/column clues indicate runs of filled cells.
//!
//! Input format (stdin):
//! ```
//! <rows> <cols>
//! <row_1_clues>
//! <row_2_clues>
//! ...
//! <col_1_clues>
//! <col_2_clues>
//! ...
//! ```
//!
//! Example (5x5 heart):
//! ```
//! 5 5
//! 1 1
//! 5
//! 5
//! 3
//! 1
//! 1 1
//! 3
//! 3
//! 3
//! 1 1
//! ```

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Convert (row, col) to variable number.
/// row, col are 0-indexed.
fn var(cols: usize, row: usize, col: usize) -> i32 {
    (row * cols + col + 1) as i32
}

/// Generate all valid patterns for a line with given clues.
/// Returns vectors of positions that should be filled.
fn generate_valid_patterns(line_len: usize, clues: &[usize]) -> Vec<Vec<bool>> {
    if clues.is_empty() || (clues.len() == 1 && clues[0] == 0) {
        // No clues means all cells empty
        return vec![vec![false; line_len]];
    }

    let min_len: usize = clues.iter().sum::<usize>() + clues.len() - 1;
    if min_len > line_len {
        return vec![]; // Impossible
    }

    let mut patterns = Vec::new();
    generate_patterns_recursive(line_len, clues, 0, &mut vec![false; line_len], &mut patterns);
    patterns
}

fn generate_patterns_recursive(
    line_len: usize,
    clues: &[usize],
    start_pos: usize,
    current: &mut Vec<bool>,
    patterns: &mut Vec<Vec<bool>>,
) {
    if clues.is_empty() {
        patterns.push(current.clone());
        return;
    }

    let clue = clues[0];
    let remaining_clues = &clues[1..];
    let remaining_min: usize = remaining_clues.iter().sum::<usize>()
        + if remaining_clues.is_empty() { 0 } else { remaining_clues.len() };

    let max_start = line_len - clue - remaining_min;

    for pos in start_pos..=max_start {
        // Place this run starting at pos
        for cell in current.iter_mut().skip(pos).take(clue) {
            *cell = true;
        }

        let next_start = pos + clue + 1; // +1 for mandatory gap
        generate_patterns_recursive(line_len, remaining_clues, next_start, current, patterns);

        // Undo
        for cell in current.iter_mut().skip(pos).take(clue) {
            *cell = false;
        }
    }
}

/// Encode that exactly one of the patterns must be true for a row.
fn encode_row_patterns(
    row: usize,
    cols: usize,
    patterns: &[Vec<bool>],
    next_aux: &mut i32,
) -> Vec<Clause> {
    if patterns.is_empty() {
        // No valid patterns - add empty clause to make UNSAT
        return vec![Clause::new(vec![])];
    }

    if patterns.len() == 1 {
        // Only one pattern - directly constrain cells
        let mut clauses = Vec::new();
        for (c, &filled) in patterns[0].iter().enumerate() {
            let lit = if filled {
                Literal::positive(var(cols, row, c))
            } else {
                Literal::negative(var(cols, row, c))
            };
            clauses.push(Clause::new(vec![lit]));
        }
        return clauses;
    }

    // Multiple patterns: use auxiliary variables
    // aux_i means "pattern i is selected"
    let mut clauses = Vec::new();
    let aux_vars: Vec<i32> = (0..patterns.len()).map(|_| { let v = *next_aux; *next_aux += 1; v }).collect();

    // At least one pattern must be selected
    clauses.push(Clause::new(aux_vars.iter().map(|&v| Literal::positive(v)).collect()));

    // At most one pattern (optional but helps propagation)
    for i in 0..aux_vars.len() {
        for j in (i + 1)..aux_vars.len() {
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                Literal::negative(aux_vars[j]),
            ]));
        }
    }

    // If pattern i is selected, cells must match
    for (i, pattern) in patterns.iter().enumerate() {
        for (c, &filled) in pattern.iter().enumerate() {
            // aux_i -> (cell matches pattern)
            // equiv: NOT aux_i OR (cell matches)
            let cell_lit = if filled {
                Literal::positive(var(cols, row, c))
            } else {
                Literal::negative(var(cols, row, c))
            };
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                cell_lit,
            ]));
        }
    }

    clauses
}

/// Encode that exactly one of the patterns must be true for a column.
fn encode_col_patterns(
    col: usize,
    _rows: usize,
    cols: usize,
    patterns: &[Vec<bool>],
    next_aux: &mut i32,
) -> Vec<Clause> {
    if patterns.is_empty() {
        return vec![Clause::new(vec![])];
    }

    if patterns.len() == 1 {
        let mut clauses = Vec::new();
        for (r, &filled) in patterns[0].iter().enumerate() {
            let lit = if filled {
                Literal::positive(var(cols, r, col))
            } else {
                Literal::negative(var(cols, r, col))
            };
            clauses.push(Clause::new(vec![lit]));
        }
        return clauses;
    }

    let mut clauses = Vec::new();
    let aux_vars: Vec<i32> = (0..patterns.len()).map(|_| { let v = *next_aux; *next_aux += 1; v }).collect();

    clauses.push(Clause::new(aux_vars.iter().map(|&v| Literal::positive(v)).collect()));

    for i in 0..aux_vars.len() {
        for j in (i + 1)..aux_vars.len() {
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                Literal::negative(aux_vars[j]),
            ]));
        }
    }

    for (i, pattern) in patterns.iter().enumerate() {
        for (r, &filled) in pattern.iter().enumerate() {
            let cell_lit = if filled {
                Literal::positive(var(cols, r, col))
            } else {
                Literal::negative(var(cols, r, col))
            };
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                cell_lit,
            ]));
        }
    }

    clauses
}

/// Parse input and return (rows, cols, row_clues, col_clues).
type NonogramInput = (usize, usize, Vec<Vec<usize>>, Vec<Vec<usize>>);

fn parse_input() -> Result<NonogramInput, String> {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();

    // First line: rows cols
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

    // Next 'rows' lines: row clues
    let mut row_clues = Vec::new();
    for _ in 0..rows {
        let line = lines.next()
            .ok_or("Missing row clue")?
            .map_err(|e| e.to_string())?;
        let clues: Vec<usize> = if line.trim().is_empty() || line.trim() == "0" {
            vec![0]
        } else {
            line.split_whitespace()
                .map(|s| s.parse().map_err(|_| "Invalid clue"))
                .collect::<Result<_, _>>()?
        };
        row_clues.push(clues);
    }

    // Next 'cols' lines: column clues
    let mut col_clues = Vec::new();
    for _ in 0..cols {
        let line = lines.next()
            .ok_or("Missing column clue")?
            .map_err(|e| e.to_string())?;
        let clues: Vec<usize> = if line.trim().is_empty() || line.trim() == "0" {
            vec![0]
        } else {
            line.split_whitespace()
                .map(|s| s.parse().map_err(|_| "Invalid clue"))
                .collect::<Result<_, _>>()?
        };
        col_clues.push(clues);
    }

    Ok((rows, cols, row_clues, col_clues))
}

/// Print the solution grid.
fn print_solution(solver: &CDCLSolver, rows: usize, cols: usize) {
    for r in 0..rows {
        for c in 0..cols {
            if solver.get_value(var(cols, r, c)) == Some(true) {
                print!("# ");
            } else {
                print!(". ");
            }
        }
        println!();
    }
}

fn main() {
    let (rows, cols, row_clues, col_clues) = match parse_input() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(1);
        }
    };

    // Generate all clauses
    let mut clauses = Vec::new();
    let mut next_aux = (rows * cols + 1) as i32; // Auxiliary vars start after grid vars

    // Row constraints
    for (r, clues) in row_clues.iter().enumerate() {
        let patterns = generate_valid_patterns(cols, clues);
        if patterns.is_empty() {
            eprintln!("No valid patterns for row {} with clues {:?}", r + 1, clues);
            process::exit(1);
        }
        clauses.extend(encode_row_patterns(r, cols, &patterns, &mut next_aux));
    }

    // Column constraints
    for (c, clues) in col_clues.iter().enumerate() {
        let patterns = generate_valid_patterns(rows, clues);
        if patterns.is_empty() {
            eprintln!("No valid patterns for column {} with clues {:?}", c + 1, clues);
            process::exit(1);
        }
        clauses.extend(encode_col_patterns(c, rows, cols, &patterns, &mut next_aux));
    }

    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            print_solution(&solver, rows, cols);
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
    fn test_generate_patterns_simple() {
        let patterns = generate_valid_patterns(5, &[2]);
        assert_eq!(patterns.len(), 4); // positions 0,1,2,3
        assert_eq!(patterns[0], vec![true, true, false, false, false]);
        assert_eq!(patterns[3], vec![false, false, false, true, true]);
    }

    #[test]
    fn test_generate_patterns_two_runs() {
        let patterns = generate_valid_patterns(5, &[1, 1]);
        // 1.1.. 1..1. 1...1 .1.1. .1..1 ..1.1
        assert_eq!(patterns.len(), 6);
    }

    #[test]
    fn test_generate_patterns_empty() {
        let patterns = generate_valid_patterns(5, &[0]);
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0], vec![false; 5]);
    }

    #[test]
    fn test_generate_patterns_full() {
        let patterns = generate_valid_patterns(5, &[5]);
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0], vec![true; 5]);
    }

    #[test]
    fn test_generate_patterns_impossible() {
        let patterns = generate_valid_patterns(5, &[3, 3]);
        assert_eq!(patterns.len(), 0);
    }

    #[test]
    fn test_simple_nonogram() {
        // 3x3 with diagonal
        // Clues: rows [1], [1], [1], cols [1], [1], [1]
        let rows = 3;
        let cols = 3;
        let row_clues = [vec![1], vec![1], vec![1]];
        let col_clues = [vec![1], vec![1], vec![1]];

        let mut clauses = Vec::new();
        let mut next_aux = (rows * cols + 1) as i32;

        for (r, clues) in row_clues.iter().enumerate() {
            let patterns = generate_valid_patterns(cols, clues);
            clauses.extend(encode_row_patterns(r, cols, &patterns, &mut next_aux));
        }

        for (c, clues) in col_clues.iter().enumerate() {
            let patterns = generate_valid_patterns(rows, clues);
            clauses.extend(encode_col_patterns(c, rows, cols, &patterns, &mut next_aux));
        }

        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }
}
