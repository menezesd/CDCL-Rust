//! Lights Out Solver using CDCL SAT Solver
//!
//! Finds the solution to a Lights Out puzzle. Pressing a light toggles it
//! and all orthogonally adjacent lights.
//!
//! Input format (stdin):
//! ```
//! <rows> <cols>
//! <board>
//! ```
//! Where: 1 = light on, 0 = light off
//!
//! Output: Which buttons to press to turn all lights off.

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: button at (r,c) is pressed
fn var(cols: usize, row: usize, col: usize) -> i32 {
    (row * cols + col + 1) as i32
}

/// Get cells affected by pressing button at (r,c) - the cell itself and orthogonal neighbors.
fn affected_cells(rows: usize, cols: usize, r: usize, c: usize) -> Vec<(usize, usize)> {
    let mut result = vec![(r, c)];

    if r > 0 {
        result.push((r - 1, c));
    }
    if r + 1 < rows {
        result.push((r + 1, c));
    }
    if c > 0 {
        result.push((r, c - 1));
    }
    if c + 1 < cols {
        result.push((r, c + 1));
    }

    result
}

/// Encode the Lights Out puzzle.
/// For each cell, the XOR of initial state and all affecting button presses must be 0 (off).
fn generate_lights_out_clauses(
    rows: usize,
    cols: usize,
    initial: &[Vec<bool>],
) -> Vec<Clause> {
    let mut clauses = Vec::new();

    // For each light, we need: initial XOR (toggles) = 0
    // i.e., if initial is ON, odd number of toggles needed
    //       if initial is OFF, even number of toggles needed

    // For XOR constraints, we use the property that:
    // XOR(x1, x2, ..., xn) = 1 iff odd number of xi are true

    // We'll use auxiliary variables for partial XORs
    let num_cells = rows * cols;
    let mut next_aux = (num_cells + 1) as i32;

    for (r, initial_row) in initial.iter().enumerate().take(rows) {
        for (c, &target) in initial_row.iter().enumerate().take(cols) {
            // Find all buttons that affect this cell
            let affecting: Vec<i32> = (0..rows)
                .flat_map(|br| (0..cols).map(move |bc| (br, bc)))
                .filter(|&(br, bc)| affected_cells(rows, cols, br, bc).contains(&(r, c)))
                .map(|(br, bc)| var(cols, br, bc))
                .collect();

            // The XOR of all affecting buttons must equal initial[r][c]
            // (if initial is 1, we need odd toggles; if 0, we need even toggles)

            // Encode XOR constraint using auxiliary variables
            clauses.extend(encode_xor_equals(&affecting, target, &mut next_aux));
        }
    }

    clauses
}

/// Encode XOR of variables equals target value.
fn encode_xor_equals(vars: &[i32], target: bool, next_aux: &mut i32) -> Vec<Clause> {
    if vars.is_empty() {
        if target {
            // XOR of nothing should be true - impossible
            return vec![Clause::new(vec![])];
        } else {
            return vec![];
        }
    }

    if vars.len() == 1 {
        let lit = if target {
            Literal::positive(vars[0])
        } else {
            Literal::negative(vars[0])
        };
        return vec![Clause::new(vec![lit])];
    }

    // For multiple variables, build XOR chain
    // result_1 = vars[0] XOR vars[1]
    // result_2 = result_1 XOR vars[2]
    // ...
    // result_n-1 = target

    let mut clauses = Vec::new();
    let mut prev_result = vars[0];

    for &v in &vars[1..vars.len() - 1] {
        let result = *next_aux;
        *next_aux += 1;

        // result = prev_result XOR v
        // Equivalent to:
        // (prev AND v) -> NOT result
        // (prev AND NOT v) -> result
        // (NOT prev AND v) -> result
        // (NOT prev AND NOT v) -> NOT result

        // CNF encoding of XOR:
        // (NOT prev OR NOT v OR NOT result) AND
        // (NOT prev OR v OR result) AND
        // (prev OR NOT v OR result) AND
        // (prev OR v OR NOT result)

        clauses.push(Clause::new(vec![
            Literal::negative(prev_result),
            Literal::negative(v),
            Literal::negative(result),
        ]));
        clauses.push(Clause::new(vec![
            Literal::negative(prev_result),
            Literal::positive(v),
            Literal::positive(result),
        ]));
        clauses.push(Clause::new(vec![
            Literal::positive(prev_result),
            Literal::negative(v),
            Literal::positive(result),
        ]));
        clauses.push(Clause::new(vec![
            Literal::positive(prev_result),
            Literal::positive(v),
            Literal::negative(result),
        ]));

        prev_result = result;
    }

    // Final XOR with last variable equals target
    let last_var = *vars.last().unwrap();

    if target {
        // prev_result XOR last_var = 1
        // Means they must be different
        clauses.push(Clause::new(vec![
            Literal::negative(prev_result),
            Literal::negative(last_var),
        ]));
        clauses.push(Clause::new(vec![
            Literal::positive(prev_result),
            Literal::positive(last_var),
        ]));
    } else {
        // prev_result XOR last_var = 0
        // Means they must be the same
        clauses.push(Clause::new(vec![
            Literal::negative(prev_result),
            Literal::positive(last_var),
        ]));
        clauses.push(Clause::new(vec![
            Literal::positive(prev_result),
            Literal::negative(last_var),
        ]));
    }

    clauses
}

fn parse_input() -> Result<(usize, usize, Vec<Vec<bool>>), String> {
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

        let row: Vec<bool> = line.chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| c == '1')
            .collect();

        if row.len() != cols {
            return Err(format!("Expected {} columns, got {}", cols, row.len()));
        }

        board.push(row);
    }

    Ok((rows, cols, board))
}

fn print_solution(solver: &CDCLSolver, rows: usize, cols: usize) {
    println!("Press these buttons (marked with X):");
    let mut count = 0;

    for r in 0..rows {
        for c in 0..cols {
            if solver.get_value(var(cols, r, c)) == Some(true) {
                print!("X ");
                count += 1;
            } else {
                print!(". ");
            }
        }
        println!();
    }

    println!("\nTotal button presses: {count}");
}

fn main() {
    let (rows, cols, initial) = match parse_input() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {e}");
            process::exit(1);
        }
    };

    println!("Initial board:");
    for row in &initial {
        for &cell in row {
            print!("{} ", if cell { "1" } else { "0" });
        }
        println!();
    }
    println!();

    let clauses = generate_lights_out_clauses(rows, cols, &initial);
    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            print_solution(&solver, rows, cols);
        }
        Ok(false) => {
            println!("No solution exists (puzzle is unsolvable)");
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
    fn test_single_light() {
        // Single light on - just press it
        let initial = vec![vec![true]];
        let clauses = generate_lights_out_clauses(1, 1, &initial);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
    }

    #[test]
    fn test_all_off() {
        // All lights off - don't press anything
        let initial = vec![vec![false, false], vec![false, false]];
        let clauses = generate_lights_out_clauses(2, 2, &initial);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_2x2_center_pattern() {
        // 2x2 with all lights on
        let initial = vec![vec![true, true], vec![true, true]];
        let clauses = generate_lights_out_clauses(2, 2, &initial);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_xor_encoding() {
        // Test that XOR encoding works correctly
        let mut next_aux = 100;

        // XOR(1,2) = true means exactly one of var 1,2 is true
        let clauses = encode_xor_equals(&[1, 2], true, &mut next_aux);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        let v1 = solver.get_value(1) == Some(true);
        let v2 = solver.get_value(2) == Some(true);
        assert!(v1 ^ v2); // Exactly one should be true
    }
}
