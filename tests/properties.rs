//! Property-based tests for the CDCL SAT solver.

use proptest::prelude::*;
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

/// Generates a random 3-SAT instance.
#[allow(dead_code)]
fn random_3sat(num_vars: usize, num_clauses: usize) -> impl Strategy<Value = Vec<Vec<i32>>> {
    proptest::collection::vec(
        proptest::collection::vec(1..=(num_vars as i32), 3).prop_map(|vars| {
            vars.into_iter()
                .map(|v| if rand::random::<bool>() { v } else { -v })
                .collect::<Vec<i32>>()
        }),
        num_clauses,
    )
}

/// Verify assignment satisfies all clauses.
fn check_assignment(raw_clauses: &[Vec<i32>], solver: &CDCLSolver) -> bool {
    for clause in raw_clauses {
        let satisfied = clause.iter().any(|&lit| {
            let var = lit.unsigned_abs() as i32;
            match solver.get_value(var) {
                Some(true) => lit > 0,
                Some(false) => lit < 0,
                None => false,
            }
        });
        if !satisfied { return false; }
    }
    true
}

proptest! {
    #[test]
    fn test_random_3sat_consistency(
        num_vars in 5..12usize,
        ratio_x10 in 30..45u32,  // ratio * 10 (3.0 to 4.5)
    ) {
        let num_clauses = (num_vars as u32 * ratio_x10 / 10) as usize;
        // Generate random clauses
        let mut rng_state = num_vars as u32 * 1000 + ratio_x10;
        let mut clauses_raw: Vec<Vec<i32>> = Vec::new();
        for _ in 0..num_clauses {
            let mut lits = Vec::new();
            for _ in 0..3 {
                rng_state ^= rng_state << 13;
                rng_state ^= rng_state >> 17;
                rng_state ^= rng_state << 5;
                let var = (rng_state % num_vars as u32) as i32 + 1;
                rng_state ^= rng_state << 13;
                rng_state ^= rng_state >> 17;
                rng_state ^= rng_state << 5;
                let lit = if rng_state.is_multiple_of(2) { var } else { -var };
                lits.push(lit);
            }
            clauses_raw.push(lits);
        }

        let clauses: Vec<Clause> = clauses_raw.iter()
            .map(|c| make_clause(c))
            .collect();
        let mut solver = CDCLSolver::new(clauses);
        let result = solver.solve().unwrap();

        // If SAT, verify the assignment
        if result {
            prop_assert!(check_assignment(&clauses_raw, &solver),
                "SAT result but assignment doesn't satisfy all clauses");
        }
        // If UNSAT, that's also valid — we just can't easily verify
    }

    #[test]
    fn test_empty_formula_is_sat(num_vars in 1..20i32) {
        let mut solver = CDCLSolver::new_incremental(num_vars);
        prop_assert!(solver.solve().unwrap(), "Empty formula should be SAT");
    }

    #[test]
    fn test_contradiction_is_unsat(var in 1..100i32) {
        let clauses = vec![
            make_clause(&[var]),
            make_clause(&[-var]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        prop_assert!(!solver.solve().unwrap(), "x AND !x should be UNSAT");
    }

    #[test]
    fn test_single_unit_always_sat(var in 1..100i32, positive in proptest::bool::ANY) {
        let lit = if positive { var } else { -var };
        let clauses = vec![make_clause(&[lit])];
        let mut solver = CDCLSolver::new(clauses);
        prop_assert!(solver.solve().unwrap(), "Single unit clause should be SAT");
        let expected = if positive { Some(true) } else { Some(false) };
        prop_assert_eq!(solver.get_value(var), expected);
    }

    #[test]
    fn test_tautology_always_sat(var in 1..100i32) {
        // (x OR !x) is always SAT
        let clauses = vec![make_clause(&[var, -var])];
        let mut solver = CDCLSolver::new(clauses);
        prop_assert!(solver.solve().unwrap(), "Tautological clause should be SAT");
    }
}
