//! Cryptarithmetic Solver using CDCL SAT Solver
//!
//! Solves puzzles like SEND + MORE = MONEY where each letter represents
//! a unique digit (0-9).
//!
//! Usage: cryptarithmetic <WORD1> <WORD2> <RESULT>
//! Example: cryptarithmetic SEND MORE MONEY

use std::collections::{HashMap, HashSet};
use std::env;
use std::process;

use cdcl_sat::{CDCLSolver, Clause, Literal};

/// Variable: letter L has digit D
fn var(letter_idx: usize, digit: usize) -> i32 {
    (letter_idx * 10 + digit + 1) as i32
}

fn solve_cryptarithmetic(word1: &str, word2: &str, result: &str) -> Option<HashMap<char, usize>> {
    // Collect unique letters
    let mut letters: Vec<char> = Vec::new();
    let mut letter_set: HashSet<char> = HashSet::new();

    for c in word1.chars().chain(word2.chars()).chain(result.chars()) {
        if !letter_set.contains(&c) {
            letter_set.insert(c);
            letters.push(c);
        }
    }

    let num_letters = letters.len();
    if num_letters > 10 {
        return None; // Too many letters
    }

    let letter_to_idx: HashMap<char, usize> = letters
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, i))
        .collect();

    // Leading digits (can't be zero)
    let mut leading = HashSet::new();
    if let Some(c) = word1.chars().next() {
        leading.insert(c);
    }
    if let Some(c) = word2.chars().next() {
        leading.insert(c);
    }
    if let Some(c) = result.chars().next() {
        leading.insert(c);
    }

    let mut clauses = Vec::new();

    // Each letter has exactly one digit
    for l in 0..num_letters {
        // At least one
        let clause: Vec<Literal> = (0..10)
            .map(|d| Literal::positive(var(l, d)))
            .collect();
        clauses.push(Clause::new(clause));

        // At most one
        for d1 in 0..10 {
            for d2 in (d1 + 1)..10 {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(l, d1)),
                    Literal::negative(var(l, d2)),
                ]));
            }
        }
    }

    // Each digit used by at most one letter
    for d in 0..10 {
        for l1 in 0..num_letters {
            for l2 in (l1 + 1)..num_letters {
                clauses.push(Clause::new(vec![
                    Literal::negative(var(l1, d)),
                    Literal::negative(var(l2, d)),
                ]));
            }
        }
    }

    // Leading digits can't be zero
    for &c in &leading {
        let l = letter_to_idx[&c];
        clauses.push(Clause::new(vec![Literal::negative(var(l, 0))]));
    }

    // Enumerate all valid digit assignments and check which satisfy the equation
    // For up to 10 letters, we enumerate all permutations of digits
    let valid_assignments = find_valid_assignments(word1, word2, result, &letters, &letter_to_idx);

    if valid_assignments.is_empty() {
        return None;
    }

    // Add clause: at least one of the valid assignments must hold
    // For each valid assignment, create a conjunction of (letter=digit) conditions
    // Then add the disjunction of all these conjunctions

    // Using auxiliary variables for each valid assignment
    let aux_base = (num_letters * 10 + 1) as i32;
    let aux_vars: Vec<i32> = (0..valid_assignments.len())
        .map(|i| aux_base + i as i32)
        .collect();

    // At least one valid assignment
    clauses.push(Clause::new(
        aux_vars.iter().map(|&v| Literal::positive(v)).collect(),
    ));

    // Each aux implies its assignment
    for (i, assignment) in valid_assignments.iter().enumerate() {
        for (&c, &d) in assignment {
            let l = letter_to_idx[&c];
            clauses.push(Clause::new(vec![
                Literal::negative(aux_vars[i]),
                Literal::positive(var(l, d)),
            ]));
        }
    }

    let mut solver = CDCLSolver::new(clauses);

    if solver.solve().unwrap_or(false) {
        let mut solution = HashMap::new();
        for (l, &c) in letters.iter().enumerate() {
            for d in 0..10 {
                if solver.get_value(var(l, d)) == Some(true) {
                    solution.insert(c, d);
                    break;
                }
            }
        }
        Some(solution)
    } else {
        None
    }
}

fn find_valid_assignments(
    word1: &str,
    word2: &str,
    result: &str,
    letters: &[char],
    letter_to_idx: &HashMap<char, usize>,
) -> Vec<HashMap<char, usize>> {
    let mut valid = Vec::new();
    let num_letters = letters.len();

    // Leading letters
    let leading: HashSet<char> = [word1, word2, result]
        .iter()
        .filter_map(|w| w.chars().next())
        .collect();

    // Generate all permutations of digits for the letters
    permute_digits(
        letters,
        num_letters,
        &leading,
        &mut vec![None; num_letters],
        &mut [false; 10],
        0,
        word1,
        word2,
        result,
        letter_to_idx,
        &mut valid,
    );

    valid
}

#[allow(clippy::too_many_arguments)]
fn permute_digits(
    letters: &[char],
    num_letters: usize,
    leading: &HashSet<char>,
    assignment: &mut Vec<Option<usize>>,
    used: &mut [bool; 10],
    pos: usize,
    word1: &str,
    word2: &str,
    result: &str,
    letter_to_idx: &HashMap<char, usize>,
    valid: &mut Vec<HashMap<char, usize>>,
) {
    if pos == num_letters {
        // Check if this assignment satisfies the equation
        let v1 = word_value(word1, assignment, letter_to_idx);
        let v2 = word_value(word2, assignment, letter_to_idx);
        let vr = word_value(result, assignment, letter_to_idx);

        if v1 + v2 == vr {
            let mut map = HashMap::new();
            for (i, &c) in letters.iter().enumerate() {
                map.insert(c, assignment[i].unwrap());
            }
            valid.push(map);
        }
        return;
    }

    let c = letters[pos];
    let start = usize::from(leading.contains(&c));

    for d in start..10 {
        if !used[d] {
            used[d] = true;
            assignment[pos] = Some(d);
            permute_digits(
                letters,
                num_letters,
                leading,
                assignment,
                used,
                pos + 1,
                word1,
                word2,
                result,
                letter_to_idx,
                valid,
            );
            used[d] = false;
            assignment[pos] = None;
        }
    }
}

fn word_value(
    word: &str,
    assignment: &[Option<usize>],
    letter_to_idx: &HashMap<char, usize>,
) -> usize {
    word.chars().fold(0, |acc, c| {
        acc * 10 + assignment[letter_to_idx[&c]].unwrap()
    })
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 4 {
        eprintln!("Usage: {} <WORD1> <WORD2> <RESULT>", args[0]);
        eprintln!("Example: {} SEND MORE MONEY", args[0]);
        process::exit(1);
    }

    let word1 = args[1].to_uppercase();
    let word2 = args[2].to_uppercase();
    let result = args[3].to_uppercase();

    for c in word1.chars().chain(word2.chars()).chain(result.chars()) {
        if !c.is_ascii_alphabetic() {
            eprintln!("Error: Words must contain only letters");
            process::exit(1);
        }
    }

    let all_letters: HashSet<char> = word1
        .chars()
        .chain(word2.chars())
        .chain(result.chars())
        .collect();

    if all_letters.len() > 10 {
        eprintln!("Error: Too many unique letters (max 10)");
        process::exit(1);
    }

    println!("Solving: {word1} + {word2} = {result}");
    println!();

    match solve_cryptarithmetic(&word1, &word2, &result) {
        Some(solution) => {
            println!("Solution:");
            let mut sorted: Vec<_> = solution.iter().collect();
            sorted.sort_by_key(|&(c, _)| c);
            for (&c, &d) in &sorted {
                println!("  {c} = {d}");
            }
            println!();

            let v1: usize = word1.chars().fold(0, |acc, c| acc * 10 + solution[&c]);
            let v2: usize = word2.chars().fold(0, |acc, c| acc * 10 + solution[&c]);
            let vr: usize = result.chars().fold(0, |acc, c| acc * 10 + solution[&c]);

            println!("  {:>width$}", v1, width = result.len());
            println!("+ {:>width$}", v2, width = result.len());
            println!("{}", "-".repeat(result.len() + 2));
            println!("  {vr}");
        }
        None => {
            println!("No solution exists");
        }
    }
}
