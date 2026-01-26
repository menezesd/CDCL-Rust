//! Graph Coloring Solver using CDCL SAT Solver
//!
//! Determines if a graph can be colored with k colors such that no two
//! adjacent vertices have the same color.
//!
//! Input format (stdin):
//! ```
//! <vertices> <edges> <colors>
//! <v1> <v2>
//! <v1> <v2>
//! ...
//! ```
//!
//! Example (triangle with 3 colors):
//! ```
//! 3 3 3
//! 1 2
//! 2 3
//! 1 3
//! ```

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: vertex v has color c
/// v and c are 1-indexed
fn var(num_colors: usize, vertex: usize, color: usize) -> i32 {
    ((vertex - 1) * num_colors + color) as i32
}

/// Generate graph coloring constraints.
fn generate_coloring_clauses(
    num_vertices: usize,
    num_colors: usize,
    edges: &[(usize, usize)],
) -> Vec<Clause> {
    let mut clauses = Vec::new();

    // 1. Each vertex has at least one color
    for v in 1..=num_vertices {
        let clause: Vec<Literal> = (1..=num_colors)
            .map(|c| Literal::positive(var(num_colors, v, c)))
            .collect();
        clauses.push(Clause::new(clause));
    }

    // 2. Each vertex has at most one color
    for v in 1..=num_vertices {
        for c1 in 1..=num_colors {
            for c2 in (c1 + 1)..=num_colors {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(num_colors, v, c1)),
                    Literal::negative(var(num_colors, v, c2)),
                ]));
            }
        }
    }

    // 3. Adjacent vertices have different colors
    for &(v1, v2) in edges {
        for c in 1..=num_colors {
            clauses.push(Clause::new(vec![
                Literal::negative(var(num_colors, v1, c)),
                Literal::negative(var(num_colors, v2, c)),
            ]));
        }
    }

    clauses
}

fn parse_input() -> Result<(usize, usize, Vec<(usize, usize)>), String> {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();

    let first_line = lines.next()
        .ok_or("Missing first line")?
        .map_err(|e| e.to_string())?;

    let parts: Vec<usize> = first_line
        .split_whitespace()
        .map(|s| s.parse().map_err(|_| "Invalid number"))
        .collect::<Result<_, _>>()?;

    if parts.len() != 3 {
        return Err("Expected 'vertices edges colors' on first line".to_string());
    }

    let (num_vertices, num_edges, num_colors) = (parts[0], parts[1], parts[2]);

    let mut edges = Vec::new();
    for _ in 0..num_edges {
        let line = lines.next()
            .ok_or("Missing edge")?
            .map_err(|e| e.to_string())?;

        let parts: Vec<usize> = line
            .split_whitespace()
            .map(|s| s.parse().map_err(|_| "Invalid vertex"))
            .collect::<Result<_, _>>()?;

        if parts.len() != 2 {
            return Err("Expected 'v1 v2' for each edge".to_string());
        }

        edges.push((parts[0], parts[1]));
    }

    Ok((num_vertices, num_colors, edges))
}

fn print_coloring(solver: &CDCLSolver, num_vertices: usize, num_colors: usize) {
    let colors = ["Red", "Green", "Blue", "Yellow", "Purple", "Orange", "Cyan", "Magenta"];

    for v in 1..=num_vertices {
        for c in 1..=num_colors {
            if solver.get_value(var(num_colors, v, c)) == Some(true) {
                let color_name = if c <= colors.len() {
                    colors[c - 1]
                } else {
                    "Color"
                };
                println!("Vertex {}: {} ({})", v, color_name, c);
                break;
            }
        }
    }
}

fn main() {
    let (num_vertices, num_colors, edges) = match parse_input() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    };

    let clauses = generate_coloring_clauses(num_vertices, num_colors, &edges);
    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            println!("Graph is {}-colorable:", num_colors);
            print_coloring(&solver, num_vertices, num_colors);
        }
        Ok(false) => {
            println!("Graph is NOT {}-colorable", num_colors);
        }
        Err(e) => {
            eprintln!("Solver error: {}", e);
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_triangle_3_colors() {
        let edges = vec![(1, 2), (2, 3), (1, 3)];
        let clauses = generate_coloring_clauses(3, 3, &edges);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_triangle_2_colors() {
        let edges = vec![(1, 2), (2, 3), (1, 3)];
        let clauses = generate_coloring_clauses(3, 2, &edges);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_bipartite_2_colors() {
        // K2,2: complete bipartite graph
        let edges = vec![(1, 3), (1, 4), (2, 3), (2, 4)];
        let clauses = generate_coloring_clauses(4, 2, &edges);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_k4_needs_4_colors() {
        // Complete graph K4
        let edges = vec![(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)];

        let clauses = generate_coloring_clauses(4, 3, &edges);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());

        let clauses = generate_coloring_clauses(4, 4, &edges);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }
}
