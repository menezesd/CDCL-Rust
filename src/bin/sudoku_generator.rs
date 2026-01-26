//! Sudoku Generator using CDCL SAT Solver
//!
//! Generates Sudoku puzzles with a unique solution.
//!
//! Usage: sudoku_generator [difficulty]
//! Difficulty: easy (35+ clues), medium (28-34), hard (22-27), expert (17-21)

use std::env;

use cdcl_sat::{CDCLSolver, Clause, Literal};
use rand::seq::SliceRandom;
use rand::Rng;

/// Convert (row, col, digit) to variable number.
fn var(row: usize, col: usize, digit: usize) -> i32 {
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
fn generate_sudoku_clauses() -> Vec<Clause> {
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

    // 2. Each cell contains at most one digit
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

    clauses
}

/// Add clue constraints.
fn add_clues(clauses: &mut Vec<Clause>, clues: &[(usize, usize, usize)]) {
    for &(r, c, d) in clues {
        clauses.push(Clause::new(vec![Literal::positive(var(r, c, d))]));
    }
}

/// Extract solution from solver.
fn extract_solution(solver: &CDCLSolver) -> [[u8; 9]; 9] {
    let mut grid = [[0u8; 9]; 9];

    for v in 1i32..=729 {
        if solver.get_value(v) == Some(true) {
            let (row, col, digit) = decode_var(v);
            grid[row - 1][col - 1] = digit as u8;
        }
    }

    grid
}

/// Check if puzzle has a unique solution.
fn has_unique_solution(clues: &[(usize, usize, usize)]) -> bool {
    let mut clauses = generate_sudoku_clauses();
    add_clues(&mut clauses, clues);

    let mut solver = CDCLSolver::new(clauses.clone());
    if !solver.solve().unwrap_or(false) {
        return false; // No solution
    }

    // Get the first solution
    let solution = extract_solution(&solver);

    // Add blocking clause to exclude this solution
    let mut blocking = Vec::new();
    for r in 0..9 {
        for c in 0..9 {
            let d = solution[r][c] as usize;
            blocking.push(Literal::negative(var(r + 1, c + 1, d)));
        }
    }
    clauses.push(Clause::new(blocking));

    // Check if there's another solution
    let mut solver2 = CDCLSolver::new(clauses);
    !solver2.solve().unwrap_or(false)
}

/// Generate a complete, valid Sudoku grid.
fn generate_complete_grid() -> [[u8; 9]; 9] {
    let clauses = generate_sudoku_clauses();
    let mut solver = CDCLSolver::new(clauses);
    solver.solve().unwrap();
    extract_solution(&solver)
}

/// Generate a Sudoku puzzle with the specified number of clues.
fn generate_puzzle(target_clues: usize) -> (Vec<(usize, usize, usize)>, [[u8; 9]; 9]) {
    let mut rng = rand::thread_rng();

    // Start with a complete grid
    let solution = generate_complete_grid();

    // Create list of all cells
    let mut cells: Vec<(usize, usize)> = (0..9)
        .flat_map(|r| (0..9).map(move |c| (r, c)))
        .collect();
    cells.shuffle(&mut rng);

    // Start with all cells as clues
    let mut clues: Vec<(usize, usize, usize)> = cells.iter()
        .map(|&(r, c)| (r + 1, c + 1, solution[r][c] as usize))
        .collect();

    // Remove clues one by one while maintaining unique solution
    for &(r, c) in &cells {
        if clues.len() <= target_clues {
            break;
        }

        // Try removing this clue
        let clue_to_remove = (r + 1, c + 1, solution[r][c] as usize);
        let new_clues: Vec<_> = clues.iter()
            .filter(|&&clue| clue != clue_to_remove)
            .copied()
            .collect();

        if has_unique_solution(&new_clues) {
            clues = new_clues;
        }
    }

    (clues, solution)
}

/// Print puzzle grid.
fn print_puzzle(clues: &[(usize, usize, usize)]) {
    let mut grid = [[0u8; 9]; 9];
    for &(r, c, d) in clues {
        grid[r - 1][c - 1] = d as u8;
    }

    for (i, row) in grid.iter().enumerate() {
        if i > 0 && i % 3 == 0 {
            println!("------+-------+------");
        }
        for (j, &digit) in row.iter().enumerate() {
            if j > 0 && j % 3 == 0 {
                print!("| ");
            }
            if digit == 0 {
                print!(". ");
            } else {
                print!("{} ", digit);
            }
        }
        println!();
    }
}

/// Print solution grid.
fn print_solution(grid: &[[u8; 9]; 9]) {
    for (i, row) in grid.iter().enumerate() {
        if i > 0 && i % 3 == 0 {
            println!("------+-------+------");
        }
        for (j, &digit) in row.iter().enumerate() {
            if j > 0 && j % 3 == 0 {
                print!("| ");
            }
            print!("{} ", digit);
        }
        println!();
    }
}

/// Convert puzzle to string format.
fn puzzle_to_string(clues: &[(usize, usize, usize)]) -> String {
    let mut grid = [[0u8; 9]; 9];
    for &(r, c, d) in clues {
        grid[r - 1][c - 1] = d as u8;
    }

    grid.iter()
        .flat_map(|row| row.iter())
        .map(|&d| char::from_digit(d as u32, 10).unwrap_or('0'))
        .collect()
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let difficulty = if args.len() > 1 {
        args[1].to_lowercase()
    } else {
        "medium".to_string()
    };

    let target_clues = match difficulty.as_str() {
        "easy" => rand::thread_rng().gen_range(35..=45),
        "medium" => rand::thread_rng().gen_range(28..=34),
        "hard" => rand::thread_rng().gen_range(22..=27),
        "expert" => rand::thread_rng().gen_range(17..=21),
        _ => {
            eprintln!("Unknown difficulty: {}. Using medium.", difficulty);
            rand::thread_rng().gen_range(28..=34)
        }
    };

    eprintln!("Generating {} puzzle with ~{} clues...", difficulty, target_clues);

    let (clues, solution) = generate_puzzle(target_clues);

    println!("Puzzle ({} clues):", clues.len());
    println!();
    print_puzzle(&clues);

    println!();
    println!("String format: {}", puzzle_to_string(&clues));

    println!();
    println!("Solution:");
    println!();
    print_solution(&solution);
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_generate_complete_grid() {
        let grid = generate_complete_grid();

        // Check all cells are filled
        for r in 0..9 {
            for c in 0..9 {
                assert!(grid[r][c] >= 1 && grid[r][c] <= 9);
            }
        }

        // Check rows
        for r in 0..9 {
            let mut seen = [false; 10];
            for c in 0..9 {
                let d = grid[r][c] as usize;
                assert!(!seen[d], "Duplicate in row");
                seen[d] = true;
            }
        }

        // Check columns
        for c in 0..9 {
            let mut seen = [false; 10];
            for r in 0..9 {
                let d = grid[r][c] as usize;
                assert!(!seen[d], "Duplicate in column");
                seen[d] = true;
            }
        }
    }

    #[test]
    fn test_unique_solution_check() {
        // A puzzle with many clues should have unique solution
        let grid = generate_complete_grid();
        let clues: Vec<_> = (0..9)
            .flat_map(|r| (0..9).map(move |c| (r + 1, c + 1, grid[r][c] as usize)))
            .collect();

        assert!(has_unique_solution(&clues));
    }
}
