//! SATLIB-style benchmark integration tests.
//!
//! Tests the solver on standard combinatorial instances:
//! pigeonhole, random 3-SAT, Latin squares, graph coloring.

use cdcl_sat::{CDCLSolver, Clause, Literal};

fn make_clause(lits: &[i32]) -> Clause {
    Clause::new(
        lits.iter()
            .map(|&l| {
                if l > 0 { Literal::positive(l) } else { Literal::negative(-l) }
            })
            .collect(),
    )
}

/// Verifies that the solver's assignment satisfies all clauses.
fn verify_assignment(clauses: &[Clause], solver: &CDCLSolver) {
    for (i, clause) in clauses.iter().enumerate() {
        let satisfied = clause.literals.iter().any(|lit| {
            let val = solver.get_value(lit.var);
            match val {
                Some(true) => !lit.negated,
                Some(false) => lit.negated,
                None => false,
            }
        });
        assert!(satisfied, "Clause {} not satisfied: {:?}",
            i, clause.literals.iter().map(|l| l.as_signed()).collect::<Vec<_>>());
    }
}

/// Pigeonhole PHP(n+1, n): n+1 pigeons into n holes. Always UNSAT.
fn pigeonhole_clauses(pigeons: usize, holes: usize) -> Vec<Clause> {
    // Variable p_i_j (1-indexed): pigeon i in hole j
    let var = |i: usize, j: usize| -> i32 { (i * holes + j + 1) as i32 };
    let mut clauses = Vec::new();

    // Each pigeon in at least one hole
    for i in 0..pigeons {
        let lits: Vec<i32> = (0..holes).map(|j| var(i, j)).collect();
        clauses.push(make_clause(&lits));
    }

    // At most one pigeon per hole
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(make_clause(&[-var(i1, j), -var(i2, j)]));
            }
        }
    }

    clauses
}

#[test]
fn test_php_4_3_unsat() {
    let clauses = pigeonhole_clauses(4, 3);
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap(), "PHP(4,3) should be UNSAT");
}

#[test]
fn test_php_3_2_unsat() {
    let clauses = pigeonhole_clauses(3, 2);
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap(), "PHP(3,2) should be UNSAT");
}

#[test]
fn test_php_3_3_sat() {
    let clauses = pigeonhole_clauses(3, 3);
    let mut solver = CDCLSolver::new(clauses.clone());
    assert!(solver.solve().unwrap(), "PHP(3,3) should be SAT");
    verify_assignment(&clauses, &solver);
}

#[test]
fn test_php_5_4_unsat() {
    let clauses = pigeonhole_clauses(5, 4);
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap(), "PHP(5,4) should be UNSAT");
}

/// 3x3 Latin square: each cell has value 1-3, each value once per row/col.
#[test]
fn test_latin_square_3x3_sat() {
    let n = 3;
    // Variable: cell (r,c) has value v => var = r*n*n + c*n + v + 1
    let var = |r: usize, c: usize, v: usize| -> i32 { (r * n * n + c * n + v + 1) as i32 };
    let mut clauses = Vec::new();

    for r in 0..n {
        for c in 0..n {
            // Each cell has at least one value
            let lits: Vec<i32> = (0..n).map(|v| var(r, c, v)).collect();
            clauses.push(make_clause(&lits));
            // At most one value per cell
            for v1 in 0..n {
                for v2 in (v1 + 1)..n {
                    clauses.push(make_clause(&[-var(r, c, v1), -var(r, c, v2)]));
                }
            }
        }
    }

    // Each value once per row
    for r in 0..n {
        for v in 0..n {
            for c1 in 0..n {
                for c2 in (c1 + 1)..n {
                    clauses.push(make_clause(&[-var(r, c1, v), -var(r, c2, v)]));
                }
            }
        }
    }

    // Each value once per column
    for c in 0..n {
        for v in 0..n {
            for r1 in 0..n {
                for r2 in (r1 + 1)..n {
                    clauses.push(make_clause(&[-var(r1, c, v), -var(r2, c, v)]));
                }
            }
        }
    }

    let mut solver = CDCLSolver::new(clauses.clone());
    assert!(solver.solve().unwrap(), "3x3 Latin square should be SAT");
    verify_assignment(&clauses, &solver);
}

/// Petersen graph 3-coloring (SAT — chromatic number is 3).
#[test]
fn test_petersen_3_coloring_sat() {
    let edges = [
        (0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),
        (3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9),
    ];
    let n_verts = 10;
    let n_colors = 3;
    let var = |v: usize, c: usize| -> i32 { (v * n_colors + c + 1) as i32 };

    let mut clauses = Vec::new();

    // Each vertex has at least one color
    for v in 0..n_verts {
        let lits: Vec<i32> = (0..n_colors).map(|c| var(v, c)).collect();
        clauses.push(make_clause(&lits));
    }

    // Adjacent vertices have different colors
    for &(u, v) in &edges {
        for c in 0..n_colors {
            clauses.push(make_clause(&[-var(u, c), -var(v, c)]));
        }
    }

    let mut solver = CDCLSolver::new(clauses.clone());
    assert!(solver.solve().unwrap(), "Petersen 3-coloring should be SAT");
    verify_assignment(&clauses, &solver);
}

/// Petersen graph 2-coloring (UNSAT — it has odd cycles).
#[test]
fn test_petersen_2_coloring_unsat() {
    let edges = [
        (0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),
        (3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9),
    ];
    let n_verts = 10;
    let n_colors = 2;
    let var = |v: usize, c: usize| -> i32 { (v * n_colors + c + 1) as i32 };

    let mut clauses = Vec::new();
    for v in 0..n_verts {
        let lits: Vec<i32> = (0..n_colors).map(|c| var(v, c)).collect();
        clauses.push(make_clause(&lits));
    }
    for &(u, v) in &edges {
        for c in 0..n_colors {
            clauses.push(make_clause(&[-var(u, c), -var(v, c)]));
        }
    }

    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap(), "Petersen 2-coloring should be UNSAT");
}
