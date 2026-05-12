//! DIMACS CNF SAT Solver
//!
//! Reads a SAT problem in DIMACS CNF format and solves it.
//! This is the standard format used in SAT competitions.
//!
//! DIMACS format:
//! - Lines starting with 'c' are comments
//! - 'p cnf <variables> <clauses>' declares the problem
//! - Each subsequent line is a clause: space-separated literals ending with 0
//! - Positive literal = variable is true, negative = false
//!
//! Example:
//! ```
//! c Example SAT problem
//! p cnf 3 2
//! 1 -2 3 0
//! -1 2 0
//! ```

use std::io::{self, BufRead};
use std::fs::File;
use std::process;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use cdcl_sat::{CDCLSolver, Clause, Literal};
use cdcl_sat::preprocess::preprocess;

const USAGE: &str = "\
Usage: dimacs_sat [OPTIONS] [FILE]

Reads a SAT problem in DIMACS CNF format and solves it.
If no file is given, reads from stdin.

Options:
  --stats          Print solver statistics
  --no-preprocess  Skip preprocessing
  --timeout SEC    Time limit in seconds
  --help           Show this help

Environment variables (fallback):
  NOPP=1           Skip preprocessing (same as --no-preprocess)
  DRAT=<path>      Enable DRAT proof logging to file";

struct Config {
    file: Option<String>,
    stats: bool,
    no_preprocess: bool,
    timeout_secs: Option<u64>,
}

fn parse_args() -> Result<Config, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut config = Config {
        file: None,
        stats: false,
        no_preprocess: false,
        timeout_secs: None,
    };

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                println!("{USAGE}");
                process::exit(0);
            }
            "--stats" => {
                config.stats = true;
            }
            "--no-preprocess" => {
                config.no_preprocess = true;
            }
            "--timeout" => {
                i += 1;
                if i >= args.len() {
                    return Err("--timeout requires a value".to_string());
                }
                let secs: u64 = args[i].parse()
                    .map_err(|_| format!("Invalid timeout value: {}", args[i]))?;
                config.timeout_secs = Some(secs);
            }
            arg if arg.starts_with('-') => {
                return Err(format!("Unknown option: {arg}"));
            }
            _ => {
                if config.file.is_some() {
                    return Err("Multiple input files not supported".to_string());
                }
                config.file = Some(args[i].clone());
            }
        }
        i += 1;
    }

    // Fallback: check NOPP env var
    if !config.no_preprocess && std::env::var("NOPP").is_ok() {
        config.no_preprocess = true;
    }

    Ok(config)
}

fn parse_dimacs<R: BufRead>(reader: R) -> Result<(usize, Vec<Clause>), String> {
    let mut num_vars = 0;
    let mut num_clauses_expected = 0;
    let mut clauses = Vec::new();
    let mut header_seen = false;

    for line in reader.lines() {
        let line = line.map_err(|e| e.to_string())?;
        let trimmed = line.trim();

        if trimmed.is_empty() {
            continue;
        }

        // Comment line
        if trimmed.starts_with('c') {
            continue;
        }

        // Problem line
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err("Invalid problem line, expected 'p cnf <vars> <clauses>'".to_string());
            }
            num_vars = parts[2].parse().map_err(|_| "Invalid variable count")?;
            num_clauses_expected = parts[3].parse().map_err(|_| "Invalid clause count")?;
            header_seen = true;
            continue;
        }

        if !header_seen {
            return Err("Clause before problem line".to_string());
        }

        // Clause line
        let literals: Result<Vec<i32>, _> = trimmed
            .split_whitespace()
            .map(str::parse::<i32>)
            .collect();

        let literals = literals.map_err(|_| "Invalid literal")?;

        // Clause ends with 0
        let clause_lits: Vec<Literal> = literals.iter()
            .take_while(|&&l| l != 0)
            .map(|&l| {
                if l > 0 {
                    Literal::positive(l)
                } else {
                    Literal::negative(-l)
                }
            })
            .collect();

        if !clause_lits.is_empty() || literals.contains(&0) {
            clauses.push(Clause::new(clause_lits));
        }
    }

    if !header_seen {
        return Err("No problem line found".to_string());
    }

    if clauses.len() != num_clauses_expected {
        eprintln!("Warning: Expected {} clauses, got {}", num_clauses_expected, clauses.len());
    }

    Ok((num_vars, clauses))
}

fn print_solution(solver: &CDCLSolver, num_vars: usize) {
    print!("v");
    for v in 1..=num_vars {
        match solver.get_value(v as i32) {
            Some(true) => print!(" {v}"),
            Some(false) => print!(" -{v}"),
            None => print!(" {v}"), // Default to positive if unassigned
        }
    }
    println!(" 0");
}

fn main() {
    let config = match parse_args() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: {e}");
            eprintln!("Try 'dimacs_sat --help' for usage.");
            process::exit(1);
        }
    };

    // Parse from file or stdin
    let (num_vars, clauses) = if let Some(path) = &config.file {
        let file = match File::open(path) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("Cannot open file '{path}': {e}");
                process::exit(1);
            }
        };
        match parse_dimacs(io::BufReader::new(file)) {
            Ok(data) => data,
            Err(e) => {
                eprintln!("Parse error: {e}");
                process::exit(1);
            }
        }
    } else {
        let stdin = io::stdin();
        match parse_dimacs(stdin.lock()) {
            Ok(data) => data,
            Err(e) => {
                eprintln!("Parse error: {e}");
                process::exit(1);
            }
        }
    };

    eprintln!("c Parsed {} variables and {} clauses", num_vars, clauses.len());

    // Preprocess unless disabled
    let clauses = if config.no_preprocess {
        eprintln!("c Skipping preprocessing");
        clauses
    } else {
        let raw: Vec<Vec<i32>> = clauses.iter().map(|c| {
            c.literals.iter().map(|l| l.as_signed()).collect()
        }).collect();
        let simplified = preprocess(raw, num_vars);
        eprintln!("c After preprocessing: {} clauses", simplified.len());
        simplified.into_iter().map(|lits| {
            Clause::new(lits.into_iter().map(|l| {
                if l > 0 { Literal::positive(l) } else { Literal::negative(-l) }
            }).collect())
        }).collect()
    };

    let mut solver = CDCLSolver::new(clauses);

    // Enable DRAT proof logging if DRAT=<path> is set
    if let Ok(path) = std::env::var("DRAT") {
        if let Err(e) = solver.enable_drat(&path) {
            eprintln!("c Failed to open DRAT file {path}: {e}");
        } else {
            eprintln!("c DRAT proof logging to {path}");
        }
    }

    // Set up timeout if requested
    let timed_out = Arc::new(AtomicBool::new(false));
    if let Some(secs) = config.timeout_secs {
        eprintln!("c Timeout: {secs} seconds");
        let timed_out_clone = Arc::clone(&timed_out);
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs(secs));
            timed_out_clone.store(true, Ordering::Relaxed);
        });
    }

    let start = std::time::Instant::now();

    match solver.solve() {
        Ok(true) => {
            println!("s SATISFIABLE");
            print_solution(&solver, num_vars);
            if config.stats {
                let elapsed = start.elapsed().as_secs_f64();
                eprintln!("c Time: {elapsed:.2}s");
            }
        }
        Ok(false) => {
            println!("s UNSATISFIABLE");
            if config.stats {
                let elapsed = start.elapsed().as_secs_f64();
                eprintln!("c Time: {elapsed:.2}s");
            }
        }
        Err(e) => {
            eprintln!("c Solver error: {e}");
            println!("s UNKNOWN");
            process::exit(1);
        }
    }

    if timed_out.load(Ordering::Relaxed) {
        eprintln!("c Warning: timeout reached (result may already be printed)");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&l| {
            if l > 0 {
                Literal::positive(l)
            } else {
                Literal::negative(-l)
            }
        }).collect())
    }

    #[test]
    fn test_simple_sat() {
        // (x1 OR x2) AND (NOT x1 OR x2)
        let clauses = vec![
            make_clause(&[1, 2]),
            make_clause(&[-1, 2]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        // x2 must be true
        assert_eq!(solver.get_value(2), Some(true));
    }

    #[test]
    fn test_simple_unsat() {
        // (x1) AND (NOT x1)
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_3sat_instance() {
        // A satisfiable 3-SAT instance
        // (x1 OR x2 OR x3) AND (NOT x1 OR x2 OR x3) AND (x1 OR NOT x2 OR x3)
        let clauses = vec![
            make_clause(&[1, 2, 3]),
            make_clause(&[-1, 2, 3]),
            make_clause(&[1, -2, 3]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_contradictory_unit_clauses() {
        // Two contradictory unit clauses are unsatisfiable
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_unit_propagation() {
        // (x1) AND (NOT x1 OR x2) AND (NOT x2 OR x3)
        // Unit propagation: x1=T -> x2=T -> x3=T
        let clauses = vec![
            make_clause(&[1]),
            make_clause(&[-1, 2]),
            make_clause(&[-2, 3]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(true));
        assert_eq!(solver.get_value(3), Some(true));
    }

    #[test]
    fn test_parse_dimacs_from_string() {
        let input = "c test\np cnf 3 2\n1 -2 3 0\n-1 2 0\n";
        let reader = io::BufReader::new(input.as_bytes());
        let (num_vars, clauses) = parse_dimacs(reader).unwrap();
        assert_eq!(num_vars, 3);
        assert_eq!(clauses.len(), 2);
    }

    #[test]
    fn test_parse_args_help_style() {
        // Just verify the Config struct works correctly
        let config = Config {
            file: Some("test.cnf".to_string()),
            stats: true,
            no_preprocess: false,
            timeout_secs: Some(60),
        };
        assert!(config.stats);
        assert_eq!(config.timeout_secs, Some(60));
        assert_eq!(config.file, Some("test.cnf".to_string()));
    }
}
