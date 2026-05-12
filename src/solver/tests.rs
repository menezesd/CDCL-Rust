use super::*;
use crate::Literal;

fn make_clause(lits: &[(i32, bool)]) -> Clause {
    Clause::new(
        lits.iter()
            .map(|&(var, neg)| {
                if neg {
                    Literal::negative(var)
                } else {
                    Literal::positive(var)
                }
            })
            .collect()
    )
}

#[test]
fn test_single_variable_sat() {
    let clauses = vec![make_clause(&[(1, false)])];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_contradiction_unsat() {
    // x1 AND NOT x1
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(1, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_simple_sat() {
    // (x1 OR x2) AND (NOT x1 OR x2)
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, true), (2, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_unit_propagation() {
    // x1 AND (NOT x1 OR x2) AND (NOT x2 OR x3)
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(1, true), (2, false)]),
        make_clause(&[(2, true), (3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(true));
    assert_eq!(solver.get_value(2), Some(true));
    assert_eq!(solver.get_value(3), Some(true));
}

#[test]
fn test_conflict_learning() {
    // A formula that requires conflict learning to solve efficiently
    // (x1 OR x2) AND (x1 OR NOT x2) AND (NOT x1 OR x2) AND (NOT x1 OR NOT x2)
    // This is UNSAT
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, false), (2, true)]),
        make_clause(&[(1, true), (2, false)]),
        make_clause(&[(1, true), (2, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_get_model() {
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(2, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    let model = solver.get_model();
    assert!(model[1]);
    assert!(model[2]);
}

// ========================================================================
// Edge Case Tests
// ========================================================================

#[test]
fn test_empty_clause_set() {
    // Empty clause set is trivially SAT
    let clauses: Vec<Clause> = vec![];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_single_unit_clause() {
    // Just x1
    let clauses = vec![make_clause(&[(1, false)])];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(true));
}

#[test]
fn test_single_negative_unit_clause() {
    // Just NOT x1
    let clauses = vec![make_clause(&[(1, true)])];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(false));
}

#[test]
fn test_multiple_unit_clauses_consistent() {
    // x1 AND x2 AND x3
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(2, false)]),
        make_clause(&[(3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(true));
    assert_eq!(solver.get_value(2), Some(true));
    assert_eq!(solver.get_value(3), Some(true));
}

#[test]
fn test_multiple_unit_clauses_conflict() {
    // x1 AND NOT x1 - immediate conflict
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(1, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_large_variable_numbers() {
    // Use variables with large gaps: x100 AND x200 AND (NOT x100 OR x300)
    let clauses = vec![
        Clause::new(vec![Literal::positive(100)]),
        Clause::new(vec![Literal::positive(200)]),
        Clause::new(vec![Literal::negative(100), Literal::positive(300)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(100), Some(true));
    assert_eq!(solver.get_value(200), Some(true));
    assert_eq!(solver.get_value(300), Some(true));
}

#[test]
fn test_binary_clauses_sat() {
    // (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR x3)
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, true), (3, false)]),
        make_clause(&[(2, true), (3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_binary_clauses_unsat() {
    // (x1 OR x2) AND (NOT x1 OR NOT x2) AND (x1 OR NOT x2) AND (NOT x1 OR x2)
    // This forces x1 = x2 and x1 != x2 simultaneously
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),   // x1 OR x2
        make_clause(&[(1, true), (2, true)]),     // NOT x1 OR NOT x2
        make_clause(&[(1, false), (2, true)]),    // x1 OR NOT x2
        make_clause(&[(1, true), (2, false)]),    // NOT x1 OR x2
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_long_implication_chain() {
    // x1 AND (NOT x1 OR x2) AND (NOT x2 OR x3) AND ... AND (NOT x9 OR x10)
    let mut clauses = vec![make_clause(&[(1, false)])];
    for i in 1..10 {
        clauses.push(make_clause(&[(i, true), (i + 1, false)]));
    }
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    // All variables should be true due to unit propagation
    for i in 1..=10 {
        assert_eq!(solver.get_value(i), Some(true));
    }
}

#[test]
fn test_long_implication_chain_unsat() {
    // x1 AND (NOT x1 OR x2) AND ... AND (NOT x9 OR x10) AND NOT x10
    let mut clauses = vec![make_clause(&[(1, false)])];
    for i in 1..10 {
        clauses.push(make_clause(&[(i, true), (i + 1, false)]));
    }
    clauses.push(make_clause(&[(10, true)])); // NOT x10
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_three_literal_clauses() {
    // (x1 OR x2 OR x3) AND (NOT x1 OR NOT x2 OR NOT x3)
    let clauses = vec![
        make_clause(&[(1, false), (2, false), (3, false)]),
        make_clause(&[(1, true), (2, true), (3, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_pigeonhole_2_1() {
    // 2 pigeons, 1 hole - UNSAT
    // p1 must be in hole 1: x1
    // p2 must be in hole 1: x2
    // At most one pigeon per hole: NOT x1 OR NOT x2
    let clauses = vec![
        make_clause(&[(1, false)]),              // pigeon 1 in hole 1
        make_clause(&[(2, false)]),              // pigeon 2 in hole 1
        make_clause(&[(1, true), (2, true)]),    // at most one per hole
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_pigeonhole_3_2() {
    // 3 pigeons, 2 holes - UNSAT
    // Pigeon 1: x1 (hole 1) OR x2 (hole 2)
    // Pigeon 2: x3 (hole 1) OR x4 (hole 2)
    // Pigeon 3: x5 (hole 1) OR x6 (hole 2)
    // Hole 1 at most one: pairs of NOT xi OR NOT xj for x1,x3,x5
    // Hole 2 at most one: pairs of NOT xi OR NOT xj for x2,x4,x6
    let clauses = vec![
        // Each pigeon in some hole
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(3, false), (4, false)]),
        make_clause(&[(5, false), (6, false)]),
        // Hole 1: at most one
        make_clause(&[(1, true), (3, true)]),
        make_clause(&[(1, true), (5, true)]),
        make_clause(&[(3, true), (5, true)]),
        // Hole 2: at most one
        make_clause(&[(2, true), (4, true)]),
        make_clause(&[(2, true), (6, true)]),
        make_clause(&[(4, true), (6, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_horn_clauses_sat() {
    // Horn clauses: at most one positive literal per clause
    // (NOT x1 OR NOT x2 OR x3) AND (NOT x3 OR x4) AND x1 AND x2
    let clauses = vec![
        make_clause(&[(1, true), (2, true), (3, false)]),
        make_clause(&[(3, true), (4, false)]),
        make_clause(&[(1, false)]),
        make_clause(&[(2, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(true));
    assert_eq!(solver.get_value(2), Some(true));
    assert_eq!(solver.get_value(3), Some(true));
    assert_eq!(solver.get_value(4), Some(true));
}

#[test]
fn test_get_value_unassigned() {
    // Create solver but don't solve - all variables unassigned
    let clauses = vec![make_clause(&[(1, false), (2, false)])];
    let solver = CDCLSolver::new(clauses);
    // Before solving, variables may be unassigned
    // After solving, let's check
    let mut solver = solver;
    solver.solve().unwrap();
    // At least one should be assigned
    let v1 = solver.get_value(1);
    let v2 = solver.get_value(2);
    assert!(v1.is_some() || v2.is_some());
}

#[test]
fn test_get_value_out_of_bounds() {
    let clauses = vec![make_clause(&[(1, false)])];
    let mut solver = CDCLSolver::new(clauses);
    solver.solve().unwrap();
    // Variable 1000 doesn't exist
    assert_eq!(solver.get_value(1000), None);
}

#[test]
fn test_duplicate_clauses() {
    // Same clause twice shouldn't break anything
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, false), (2, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_all_negative_clause() {
    // (NOT x1 OR NOT x2 OR NOT x3) - SAT (set any to false)
    let clauses = vec![
        make_clause(&[(1, true), (2, true), (3, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

#[test]
fn test_mixed_polarity_unit_propagation() {
    // x1 AND NOT x2 AND (NOT x1 OR x2 OR x3)
    // x1=T, x2=F makes (NOT x1 OR x2 OR x3) = (F OR F OR x3) = x3
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(2, true)]),
        make_clause(&[(1, true), (2, false), (3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(true));
    assert_eq!(solver.get_value(2), Some(false));
    assert_eq!(solver.get_value(3), Some(true));
}

#[test]
fn test_multiple_backtrack_levels() {
    // Formula requiring backtracking through multiple levels
    // This creates a more complex search tree
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, false), (2, true)]),
        make_clause(&[(1, true), (3, false)]),
        make_clause(&[(1, true), (3, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_solver_error_display() {
    let err = SolverError::InvalidConflictAnalysis {
        variable: 5,
        message: "test error".to_string(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("variable 5"));
    assert!(msg.contains("test error"));

    let err2 = SolverError::InternalError("internal test".to_string());
    let msg2 = format!("{err2}");
    assert!(msg2.contains("internal test"));
}

#[test]
fn test_activity_decay() {
    // Create a formula that will cause multiple conflicts
    // to test the activity decay mechanism
    let clauses = vec![
        make_clause(&[(1, false), (2, false)]),
        make_clause(&[(1, false), (2, true)]),
        make_clause(&[(1, true), (2, false)]),
        make_clause(&[(1, true), (2, true)]),
        make_clause(&[(3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    // Should be UNSAT due to clauses 1-4
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_watched_literal_maintenance() {
    // Test that watches are properly maintained
    // by creating clauses that force watch updates
    let clauses = vec![
        make_clause(&[(1, false), (2, false), (3, false)]),
        make_clause(&[(1, true)]),  // Forces x1=F
        make_clause(&[(2, true)]),  // Forces x2=F
        // Now first clause only has x3 as non-false
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
    assert_eq!(solver.get_value(1), Some(false));
    assert_eq!(solver.get_value(2), Some(false));
    assert_eq!(solver.get_value(3), Some(true));
}

#[test]
fn test_initial_conflict_detection() {
    // Conflicting unit clauses detected at initialization
    let clauses = vec![
        make_clause(&[(1, false)]),
        make_clause(&[(1, true)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.solve().unwrap());
}

#[test]
fn test_many_variables_sparse() {
    // Many variables but sparse usage
    let clauses = vec![
        Clause::new(vec![Literal::positive(1), Literal::positive(50)]),
        Clause::new(vec![Literal::negative(1), Literal::positive(100)]),
        Clause::new(vec![Literal::negative(50), Literal::negative(100)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    assert!(solver.solve().unwrap());
}

// ========================================================================
// Luby Sequence Tests
// ========================================================================

#[test]
fn test_luby_sequence_values() {
    // The Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    assert_eq!(CDCLSolver::luby(0), 1);
    assert_eq!(CDCLSolver::luby(1), 1);
    assert_eq!(CDCLSolver::luby(2), 2);
    assert_eq!(CDCLSolver::luby(3), 1);
    assert_eq!(CDCLSolver::luby(4), 1);
    assert_eq!(CDCLSolver::luby(5), 2);
    assert_eq!(CDCLSolver::luby(6), 4);
    assert_eq!(CDCLSolver::luby(7), 1);
    assert_eq!(CDCLSolver::luby(8), 1);
    assert_eq!(CDCLSolver::luby(9), 2);
    assert_eq!(CDCLSolver::luby(10), 1);
    assert_eq!(CDCLSolver::luby(11), 1);
    assert_eq!(CDCLSolver::luby(12), 2);
    assert_eq!(CDCLSolver::luby(13), 4);
    assert_eq!(CDCLSolver::luby(14), 8);
}

#[test]
fn test_luby_powers_of_two() {
    // At indices 2^n - 2, the Luby value is 2^(n-1)
    // Index 0: 1, Index 2: 2, Index 6: 4, Index 14: 8, Index 30: 16
    assert_eq!(CDCLSolver::luby(0), 1);
    assert_eq!(CDCLSolver::luby(2), 2);
    assert_eq!(CDCLSolver::luby(6), 4);
    assert_eq!(CDCLSolver::luby(14), 8);
    assert_eq!(CDCLSolver::luby(30), 16);
}

// ========================================================================
// Phase Saving Tests
// ========================================================================

#[test]
fn test_phase_saving_initialization() {
    // All phases should default to true (positive)
    let clauses = vec![make_clause(&[(1, false), (2, false)])];
    let solver = CDCLSolver::new(clauses);
    assert!(solver.saved_phase[1]);
    assert!(solver.saved_phase[2]);
}

#[test]
fn test_phase_saving_updates() {
    // Phase should be saved when a variable is assigned
    let clauses = vec![
        make_clause(&[(1, true)]),  // Forces x1 = false
        make_clause(&[(2, false), (3, false)]),
    ];
    let mut solver = CDCLSolver::new(clauses);
    solver.solve().unwrap();
    // x1 was forced to false, so saved_phase should be false
    assert!(!solver.saved_phase[1]);
}

// ========================================================================
// Restart Tests
// ========================================================================

#[test]
fn test_restart_initialization() {
    let clauses = vec![make_clause(&[(1, false), (2, false)])];
    let solver = CDCLSolver::new(clauses);
    assert_eq!(solver.conflicts, 0);
    assert_eq!(solver.luby_index, 0);
    assert_eq!(solver.luby_unit, 100);
    assert_eq!(solver.conflicts_until_restart, 100);
}

#[test]
fn test_should_restart() {
    let clauses = vec![make_clause(&[(1, false), (2, false)])];
    let mut solver = CDCLSolver::new(clauses);
    assert!(!solver.should_restart());
    solver.conflicts = 100;
    assert!(solver.should_restart());
    solver.conflicts = 99;
    assert!(!solver.should_restart());
}

#[test]
fn test_restart_updates_schedule() {
    let clauses = vec![make_clause(&[(1, false), (2, false)])];
    let mut solver = CDCLSolver::new(clauses);
    let _initial_restart = solver.conflicts_until_restart;
    solver.restart();
    // After restart, luby_index increases and schedule is updated
    assert_eq!(solver.luby_index, 1);
    // Luby(1) = 1, so conflicts_until_restart = 100 * 1 = 100
    assert_eq!(solver.conflicts_until_restart, 100);
    solver.restart();
    assert_eq!(solver.luby_index, 2);
    // Luby(2) = 2, so conflicts_until_restart = 100 * 2 = 200
    assert_eq!(solver.conflicts_until_restart, 200);
}
