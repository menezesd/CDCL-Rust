//! Hamiltonian Path/Cycle Solver using CDCL SAT Solver
//!
//! Finds a Hamiltonian path (visits every vertex exactly once) or cycle
//! in a graph.
//!
//! Input format (stdin):
//! ```
//! <vertices> <edges> [cycle]
//! <v1> <v2>
//! ...
//! ```
//!
//! Add "cycle" to find a Hamiltonian cycle instead of path.

use std::io::{self, BufRead};
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: vertex v is at position p in the path
/// v and p are 1-indexed
fn var(num_vertices: usize, vertex: usize, position: usize) -> i32 {
    ((vertex - 1) * num_vertices + position) as i32
}

/// Generate Hamiltonian path/cycle constraints.
fn generate_hamiltonian_clauses(
    num_vertices: usize,
    edges: &[(usize, usize)],
    find_cycle: bool,
) -> Vec<Clause> {
    let mut clauses = Vec::new();
    let n = num_vertices;

    // Build adjacency set for quick lookup
    let mut adjacent: Vec<Vec<bool>> = vec![vec![false; n + 1]; n + 1];
    for &(v1, v2) in edges {
        adjacent[v1][v2] = true;
        adjacent[v2][v1] = true;
    }

    // 1. Each vertex appears at exactly one position

    // At least one position for each vertex
    for v in 1..=n {
        let clause: Vec<Literal> = (1..=n)
            .map(|p| Literal::positive(var(n, v, p)))
            .collect();
        clauses.push(Clause::new(clause));
    }

    // At most one position for each vertex
    for v in 1..=n {
        for p1 in 1..=n {
            for p2 in (p1 + 1)..=n {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(n, v, p1)),
                    Literal::negative(var(n, v, p2)),
                ]));
            }
        }
    }

    // 2. Each position has exactly one vertex

    // At least one vertex at each position
    for p in 1..=n {
        let clause: Vec<Literal> = (1..=n)
            .map(|v| Literal::positive(var(n, v, p)))
            .collect();
        clauses.push(Clause::new(clause));
    }

    // At most one vertex at each position
    for p in 1..=n {
        for v1 in 1..=n {
            for v2 in (v1 + 1)..=n {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(n, v1, p)),
                    Literal::negative(var(n, v2, p)),
                ]));
            }
        }
    }

    // 3. Adjacent positions in path must be connected by edges
    for p in 1..n {
        for v1 in 1..=n {
            for v2 in 1..=n {
                if v1 != v2 && !adjacent[v1][v2] {
                    // If v1 is at position p, v2 cannot be at position p+1
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(n, v1, p)),
                        Literal::negative(var(n, v2, p + 1)),
                    ]));
                }
            }
        }
    }

    // 4. For Hamiltonian cycle: last position must connect back to first
    if find_cycle {
        for v1 in 1..=n {
            for v2 in 1..=n {
                if v1 != v2 && !adjacent[v1][v2] {
                    // If v1 is at position n, v2 cannot be at position 1
                    clauses.push(Clause::new(vec![
                        Literal::negative(var(n, v1, n)),
                        Literal::negative(var(n, v2, 1)),
                    ]));
                }
            }
        }
    }

    clauses
}

fn parse_input() -> Result<(usize, Vec<(usize, usize)>, bool), String> {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();

    let first_line = lines.next()
        .ok_or("Missing first line")?
        .map_err(|e| e.to_string())?;

    let parts: Vec<&str> = first_line.split_whitespace().collect();
    if parts.len() < 2 {
        return Err("Expected 'vertices edges [cycle]' on first line".to_string());
    }

    let num_vertices: usize = parts[0].parse().map_err(|_| "Invalid vertex count")?;
    let num_edges: usize = parts[1].parse().map_err(|_| "Invalid edge count")?;
    let find_cycle = parts.len() > 2 && parts[2].to_lowercase() == "cycle";

    let mut edges = Vec::new();
    for _ in 0..num_edges {
        let line = lines.next()
            .ok_or("Missing edge")?
            .map_err(|e| e.to_string())?;

        let edge_parts: Vec<usize> = line
            .split_whitespace()
            .map(|s| s.parse().map_err(|_| "Invalid vertex"))
            .collect::<Result<_, _>>()?;

        if edge_parts.len() != 2 {
            return Err("Expected 'v1 v2' for each edge".to_string());
        }

        edges.push((edge_parts[0], edge_parts[1]));
    }

    Ok((num_vertices, edges, find_cycle))
}

fn extract_path(solver: &CDCLSolver, num_vertices: usize) -> Vec<usize> {
    let mut path = vec![0; num_vertices];

    for v in 1..=num_vertices {
        for p in 1..=num_vertices {
            if solver.get_value(var(num_vertices, v, p)) == Some(true) {
                path[p - 1] = v;
                break;
            }
        }
    }

    path
}

fn main() {
    let (num_vertices, edges, find_cycle) = match parse_input() {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    };

    let path_type = if find_cycle { "cycle" } else { "path" };
    println!("Finding Hamiltonian {} for graph with {} vertices and {} edges",
             path_type, num_vertices, edges.len());

    let clauses = generate_hamiltonian_clauses(num_vertices, &edges, find_cycle);
    let mut solver = CDCLSolver::new(clauses);

    match solver.solve() {
        Ok(true) => {
            let path = extract_path(&solver, num_vertices);
            println!("\nHamiltonian {}:", path_type);
            print!("{}", path[0]);
            for &v in &path[1..] {
                print!(" -> {}", v);
            }
            if find_cycle {
                print!(" -> {}", path[0]);
            }
            println!();
        }
        Ok(false) => {
            println!("No Hamiltonian {} exists", path_type);
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
    fn test_triangle_cycle() {
        // Triangle K3 has a Hamiltonian cycle
        let edges = vec![(1, 2), (2, 3), (1, 3)];
        let clauses = generate_hamiltonian_clauses(3, &edges, true);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_path_graph() {
        // Path 1-2-3-4 has a Hamiltonian path
        let edges = vec![(1, 2), (2, 3), (3, 4)];
        let clauses = generate_hamiltonian_clauses(4, &edges, false);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());

        // But no Hamiltonian cycle
        let clauses = generate_hamiltonian_clauses(4, &edges, true);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_disconnected() {
        // Two disconnected edges: no Hamiltonian path
        let edges = vec![(1, 2), (3, 4)];
        let clauses = generate_hamiltonian_clauses(4, &edges, false);
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_complete_k4() {
        // Complete graph K4 has Hamiltonian cycle
        let edges = vec![(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)];
        let clauses = generate_hamiltonian_clauses(4, &edges, true);
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }
}
