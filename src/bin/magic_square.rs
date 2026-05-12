//! Magic Square Solver using CDCL SAT Solver
//!
//! Finds an NxN magic square where all rows, columns, and diagonals sum to
//! the same magic constant: N(N²+1)/2
//!
//! Uses order encoding for the sum constraints.
//!
//! Usage: magic_square <N>

use std::env;
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: cell (r,c) contains value v
/// r, c are 0-indexed, v is 1 to N²
fn var(n: usize, row: usize, col: usize, value: usize) -> i32 {
    (row * n * n * n + col * n * n + value) as i32
}

/// Generate all permutation constraints (each cell has one value, each value appears once).
fn generate_permutation_clauses(n: usize) -> Vec<Clause> {
    let mut clauses = Vec::new();
    let n2 = n * n;

    // Each cell has at least one value
    for r in 0..n {
        for c in 0..n {
            let clause: Vec<Literal> = (1..=n2)
                .map(|v| Literal::positive(var(n, r, c, v)))
                .collect();
            clauses.push(Clause::new(clause));
        }
    }

    // Each cell has at most one value
    for r in 0..n {
        for c in 0..n {
            for v1 in 1..=n2 {
                for v2 in (v1 + 1)..=n2 {
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(n, r, c, v1)),
                        Literal::negative(var(n, r, c, v2)),
                    ]));
                }
            }
        }
    }

    // Each value appears at least once
    for v in 1..=n2 {
        let mut clause = Vec::new();
        for r in 0..n {
            for c in 0..n {
                clause.push(Literal::positive(var(n, r, c, v)));
            }
        }
        clauses.push(Clause::new(clause));
    }

    // Each value appears at most once
    for v in 1..=n2 {
        let cells: Vec<(usize, usize)> = (0..n)
            .flat_map(|r| (0..n).map(move |c| (r, c)))
            .collect();
        for i in 0..cells.len() {
            for j in (i + 1)..cells.len() {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(n, cells[i].0, cells[i].1, v)),
                    Literal::negative(var(n, cells[j].0, cells[j].1, v)),
                ]));
            }
        }
    }

    clauses
}

/// Encode that the sum of values in given cells equals target.
/// Uses a simpler direct enumeration for small N.
fn encode_sum_constraint(
    n: usize,
    cells: &[(usize, usize)],
    target: usize,
    next_aux: &mut i32,
) -> Vec<Clause> {
    let n2 = n * n;

    // Find all valid value combinations that sum to target
    let valid_combos = find_valid_combinations(n2, cells.len(), target);

    if valid_combos.is_empty() {
        return vec![Clause::new(vec![])]; // UNSAT
    }

    let mut clauses = Vec::new();

    // Create auxiliary variable for each valid combination
    let aux_vars: Vec<i32> = (0..valid_combos.len())
        .map(|_| {
            let v = *next_aux;
            *next_aux += 1;
            v
        })
        .collect();

    // At least one combination must be true
    clauses.push(Clause::new(
        aux_vars.iter().map(|&v| Literal::positive(v)).collect(),
    ));

    // At most one combination (helps solver)
    for i in 0..aux_vars.len() {
        for j in (i + 1)..aux_vars.len() {
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                Literal::negative(aux_vars[j]),
            ]));
        }
    }

    // If combination i is selected, cells must have those values
    for (i, combo) in valid_combos.iter().enumerate() {
        for (cell_idx, &value) in combo.iter().enumerate() {
            let (r, c) = cells[cell_idx];
            // aux_i -> cell(r,c) = value
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                Literal::positive(var(n, r, c, value)),
            ]));
        }
    }

    clauses
}

/// Find all combinations of `count` distinct values from 1..=max_val that sum to target.
fn find_valid_combinations(max_val: usize, count: usize, target: usize) -> Vec<Vec<usize>> {
    let mut results = Vec::new();
    let mut current = Vec::new();
    find_combinations_recursive(max_val, count, target, 1, &mut current, &mut results);

    // Generate all permutations of each combination
    let mut all_perms = Vec::new();
    for combo in results {
        generate_permutations(&combo, &mut all_perms);
    }
    all_perms
}

fn find_combinations_recursive(
    max_val: usize,
    remaining: usize,
    target: usize,
    start: usize,
    current: &mut Vec<usize>,
    results: &mut Vec<Vec<usize>>,
) {
    if remaining == 0 {
        if target == 0 {
            results.push(current.clone());
        }
        return;
    }

    for v in start..=max_val {
        if v > target {
            break;
        }
        current.push(v);
        find_combinations_recursive(max_val, remaining - 1, target - v, v + 1, current, results);
        current.pop();
    }
}

fn generate_permutations(combo: &[usize], results: &mut Vec<Vec<usize>>) {
    let mut perm = combo.to_vec();
    loop {
        results.push(perm.clone());
        if !next_permutation(&mut perm) {
            break;
        }
    }
}

fn next_permutation(arr: &mut [usize]) -> bool {
    let n = arr.len();
    if n < 2 {
        return false;
    }

    let mut i = n - 1;
    while i > 0 && arr[i - 1] >= arr[i] {
        i -= 1;
    }

    if i == 0 {
        return false;
    }

    let mut j = n - 1;
    while arr[j] <= arr[i - 1] {
        j -= 1;
    }

    arr.swap(i - 1, j);
    arr[i..].reverse();
    true
}

fn generate_magic_square_clauses(n: usize) -> Vec<Clause> {
    let n2 = n * n;
    let magic_sum = n * (n2 + 1) / 2;

    let mut clauses = generate_permutation_clauses(n);
    let mut next_aux = (n * n * n * n * n + 1) as i32;

    // Row sums
    for r in 0..n {
        let cells: Vec<(usize, usize)> = (0..n).map(|c| (r, c)).collect();
        clauses.extend(encode_sum_constraint(n, &cells, magic_sum, &mut next_aux));
    }

    // Column sums
    for c in 0..n {
        let cells: Vec<(usize, usize)> = (0..n).map(|r| (r, c)).collect();
        clauses.extend(encode_sum_constraint(n, &cells, magic_sum, &mut next_aux));
    }

    // Main diagonal
    let main_diag: Vec<(usize, usize)> = (0..n).map(|i| (i, i)).collect();
    clauses.extend(encode_sum_constraint(n, &main_diag, magic_sum, &mut next_aux));

    // Anti-diagonal
    let anti_diag: Vec<(usize, usize)> = (0..n).map(|i| (i, n - 1 - i)).collect();
    clauses.extend(encode_sum_constraint(n, &anti_diag, magic_sum, &mut next_aux));

    clauses
}

fn extract_solution(solver: &CDCLSolver, n: usize) -> Option<Vec<Vec<usize>>> {
    let n2 = n * n;
    let mut grid = vec![vec![0usize; n]; n];

    for (r, grid_row) in grid.iter_mut().enumerate().take(n) {
        for (c, cell) in grid_row.iter_mut().enumerate().take(n) {
            for v in 1..=n2 {
                if solver.get_value(var(n, r, c, v)) == Some(true) {
                    *cell = v;
                    break;
                }
            }
            if *cell == 0 {
                return None;
            }
        }
    }

    Some(grid)
}

fn print_magic_square(grid: &[Vec<usize>]) {
    let n = grid.len();
    let max_val = n * n;
    let width = format!("{max_val}").len();

    for row in grid {
        for (i, &val) in row.iter().enumerate() {
            if i > 0 {
                print!(" ");
            }
            print!("{val:>width$}");
        }
        println!();
    }

    let magic_sum: usize = grid[0].iter().sum();
    println!("\nMagic constant: {magic_sum}");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <N>", args[0]);
        eprintln!("  N: size of the magic square (3 recommended)");
        process::exit(1);
    }

    let n: usize = match args[1].parse() {
        Ok(n) if n >= 1 => n,
        _ => {
            eprintln!("Error: N must be a positive integer");
            process::exit(1);
        }
    };

    if n > 3 {
        eprintln!("Warning: N > 3 will generate many clauses and may be slow");
    }

    let clauses = generate_magic_square_clauses(n);
    eprintln!("Generated {} clauses for {}x{} magic square", clauses.len(), n, n);

    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            if let Some(grid) = extract_solution(&solver, n) {
                println!("{n}x{n} Magic Square:");
                print_magic_square(&grid);
            } else {
                eprintln!("Error: Could not extract solution");
                process::exit(1);
            }
        }
        Ok(false) => {
            println!("No {n}x{n} magic square exists");
        }
        Err(e) => {
            eprintln!("Solver error: {e}");
            process::exit(1);
        }
    }
}
