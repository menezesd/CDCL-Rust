//! Integration tests using external test cases from CDCL-SAT-Solver project.
//!
//! These tests verify the solver against a comprehensive suite of SAT and UNSAT
//! formulas, including timed tests that must complete within specified limits.

use std::fs;
use std::time::{Duration, Instant};
use cdcl_sat::solve_formula;

/// Helper to run a test file and check the result
fn run_test_file(path: &str, expected_sat: bool) {
    let content = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e));
    let result = solve_formula(&content)
        .unwrap_or_else(|e| panic!("Solver error on {}: {}", path, e));
    assert_eq!(result, expected_sat, "Wrong result for {}", path);
}

/// Helper to run a test file with a time limit
fn run_timed_test(path: &str, expected_sat: bool, time_limit: Duration) {
    let content = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path, e));

    let start = Instant::now();
    let result = solve_formula(&content)
        .unwrap_or_else(|e| panic!("Solver error on {}: {}", path, e));
    let elapsed = start.elapsed();

    assert_eq!(result, expected_sat, "Wrong result for {}", path);
    assert!(
        elapsed < time_limit,
        "Test {} took {:?}, exceeding limit of {:?}",
        path, elapsed, time_limit
    );
}

// ============================================================================
// Sample Input Tests
// ============================================================================

#[test]
fn test_sample_ex1_sat() {
    run_test_file("resources/sample-inputs/ex1", true);
}

#[test]
fn test_sample_ex2_unsat() {
    run_test_file("resources/sample-inputs/ex2", false);
}

#[test]
fn test_sample_ex3_sat() {
    run_test_file("resources/sample-inputs/ex3", true);
}

#[test]
fn test_sample_ex4_sat() {
    run_test_file("resources/sample-inputs/ex4", true);
}

#[test]
fn test_sample_ex5_sat() {
    run_test_file("resources/sample-inputs/ex5", true);
}

#[test]
fn test_sample_ex6_sat() {
    run_test_file("resources/sample-inputs/ex6", true);
}

#[test]
fn test_sample_ex7_sat() {
    run_test_file("resources/sample-inputs/ex7", true);
}

// ============================================================================
// Public Tests with Time Limits
// ============================================================================

#[test]
fn test_public_3sec_sat_ex1() {
    run_timed_test(
        "resources/test-cases/public_tests/3sec/sat/ex1",
        true,
        Duration::from_secs(3),
    );
}

#[test]
fn test_public_3sec_unsat_ex2() {
    run_timed_test(
        "resources/test-cases/public_tests/3sec/unsat/ex2",
        false,
        Duration::from_secs(3),
    );
}

#[test]
fn test_public_5sec_sat_ex3() {
    run_timed_test(
        "resources/test-cases/public_tests/5sec/sat/ex3",
        true,
        Duration::from_secs(5),
    );
}

#[test]
fn test_public_5sec_sat_ex4() {
    run_timed_test(
        "resources/test-cases/public_tests/5sec/sat/ex4",
        true,
        Duration::from_secs(5),
    );
}

#[test]
fn test_public_10sec_unsat_ex5() {
    run_timed_test(
        "resources/test-cases/public_tests/10sec/unsat/ex5",
        false,
        Duration::from_secs(10),
    );
}

#[test]
fn test_public_10sec_unsat_ex6() {
    run_timed_test(
        "resources/test-cases/public_tests/10sec/unsat/ex6",
        false,
        Duration::from_secs(10),
    );
}

// ============================================================================
// SAT Test Cases (generated formulas)
// ============================================================================

macro_rules! sat_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            run_test_file(concat!("resources/test-cases/sat/", $file), true);
        }
    };
}

sat_test!(test_sat_n1355462854, "-1355462854");
sat_test!(test_sat_n1539415788, "-1539415788");
sat_test!(test_sat_n2143000951, "-2143000951");
sat_test!(test_sat_n692091829, "-692091829");
sat_test!(test_sat_1009197172, "1009197172");
sat_test!(test_sat_1110631217, "1110631217");
sat_test!(test_sat_1313911416, "1313911416");
sat_test!(test_sat_161678400, "161678400");
sat_test!(test_sat_1987677209, "1987677209");
sat_test!(test_sat_1990051459, "1990051459");
sat_test!(test_sat_2028613191, "2028613191");
sat_test!(test_sat_2056035330, "2056035330");
sat_test!(test_sat_2060917304, "2060917304");
sat_test!(test_sat_2061276186, "2061276186");
sat_test!(test_sat_2079676545, "2079676545");
sat_test!(test_sat_2105154, "2105154");
sat_test!(test_sat_250236, "250236");
sat_test!(test_sat_3136956, "3136956");
sat_test!(test_sat_356453600, "356453600");
sat_test!(test_sat_439348863, "439348863");
sat_test!(test_sat_6129729, "6129729");
sat_test!(test_sat_617723004, "617723004");
sat_test!(test_sat_66191232, "66191232");
sat_test!(test_sat_68956062, "68956062");
sat_test!(test_sat_6987928, "6987928");
sat_test!(test_sat_6992766, "6992766");
sat_test!(test_sat_8872514, "8872514");

// ============================================================================
// UNSAT Test Cases (generated formulas)
// ============================================================================

macro_rules! unsat_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            run_test_file(concat!("resources/test-cases/unsat/", $file), false);
        }
    };
}

unsat_test!(test_unsat_n1551300520, "-1551300520");
unsat_test!(test_unsat_n1801562976, "-1801562976");
unsat_test!(test_unsat_n1985629568, "-1985629568");
unsat_test!(test_unsat_n2017382368, "-2017382368");
unsat_test!(test_unsat_n387486151, "-387486151");
unsat_test!(test_unsat_1437267936, "1437267936");
unsat_test!(test_unsat_1455428640, "1455428640");
unsat_test!(test_unsat_1692978230, "1692978230");
unsat_test!(test_unsat_192117696, "192117696");
unsat_test!(test_unsat_2116025441, "2116025441");
unsat_test!(test_unsat_436446176, "436446176");
unsat_test!(test_unsat_66061280, "66061280");
unsat_test!(test_unsat_68350854, "68350854");
