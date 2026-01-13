//! CDCL SAT Solver - Command Line Interface
//!
//! Reads a boolean formula from stdin and outputs SAT or UNSAT.

use std::io::{self, Read};
use std::process;

use cdcl_sat::solve_formula;

fn main() {
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("Error reading input: {}", e);
        process::exit(1);
    }

    match solve_formula(&input) {
        Ok(true) => println!("SAT"),
        Ok(false) => println!("UNSAT"),
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    }
}
