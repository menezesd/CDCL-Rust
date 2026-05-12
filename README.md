# CDCL SAT Solver

A modern CDCL (Conflict-Driven Clause Learning) SAT solver implemented in Rust. Solves 80K-variable industrial SAT instances in ~2 minutes.

## Features

### Core Solver
- **Two-watched literals** with MiniSAT-style in-place compaction
- **Binary implication graph** for fast binary clause propagation
- **First-UIP conflict analysis** with recursive clause minimization
- **Non-chronological backtracking**
- **VSIDS variable selection** with position-indexed heap (MiniSAT-style)
- **Phase saving** for polarity decisions
- **Glucose-style restarts** with Luby fallback
- **Clause activity decay** for learned clause quality tracking

### Clause Database
- **Arena allocator** -- contiguous memory for cache-efficient propagation
- **LBD-based clause management** -- glue clauses (LBD <= 2) kept permanently
- **Activity-based reduction** -- low-activity clauses deleted first
- **Arena garbage collection** -- compacts when >30% fragmented

### Preprocessing & Inprocessing
- **Bounded variable elimination** (BVE)
- **Failed literal probing**
- **Equivalent literal substitution**
- **Subsumption** and **self-subsumption strengthening**
- **Pure literal elimination**
- **Vivification** (opt-in clause shortening)

### Input Formats
- **DIMACS CNF** -- standard SAT competition format
- **Prefix notation** -- `(and x1 (or x2 (not x3)))`

### Extras
- **DRAT proof logging** for UNSAT verification
- **Incremental solving** API for CEGAR loops
- Puzzle solver binaries (Sudoku, N-Queens, Nonogram, graph coloring, etc.)

## Quick Start

```bash
# Solve a DIMACS CNF file
cargo build --release --bin dimacs_sat
./target/release/dimacs_sat problem.cnf

# Solve from stdin
echo "p cnf 3 2
1 -2 3 0
-1 2 0" | ./target/release/dimacs_sat

# Prefix notation
echo "(and x1 (or (not x1) x2))" | cargo run
```

## DIMACS Solver Options

```
Usage: dimacs_sat [OPTIONS] [FILE]

Options:
  --stats          Print solver statistics
  --no-preprocess  Skip preprocessing
  --timeout SEC    Time limit in seconds
  --help           Show help

Environment variables:
  NOPP=1           Skip preprocessing
  DRAT=<path>      Enable DRAT proof logging
```

### Optimization History

| Change | Impact |
|--------|--------|
| Position-indexed heap | 4K -> 10K conflicts/sec |
| Clause arena allocator | +21% cps, better cache locality |
| MiniSAT-style propagation | Cleaner watch management |
| Recursive clause minimization | ~17% fewer conflicts |
| Arena-stored clause activity | ~50% fewer conflicts to solve |
| Binary implication graph | Fast binary propagation |
| Arena GC | Memory reclamation |

## Architecture

```
src/
  solver/
    mod.rs          -- CDCLSolver struct, public API, new(), solve()
    propagate.rs    -- BCP with two-watched literals + BIG
    analyze.rs      -- 1-UIP conflict analysis, clause minimization
    decide.rs       -- VSIDS variable selection with random noise
    reduce.rs       -- Clause database reduction + arena GC
    restart.rs      -- Glucose/Luby restart strategy
    backtrack.rs    -- Non-chronological backtracking
    inprocess.rs    -- Inprocessing + vivification
    incremental.rs  -- Incremental solving API
    stats.rs        -- Statistics reporting
    tests.rs        -- Unit tests
  clause_arena.rs   -- Contiguous clause storage
  heap.rs           -- Position-indexed variable heap
  drat.rs           -- DRAT proof logging
  preprocess.rs     -- BVE, probing, subsumption
  parser.rs         -- Prefix notation parser
  tseitin.rs        -- Tseitin CNF transformation
  cnf.rs            -- CNF detection/extraction
  expr.rs           -- Boolean expression AST
  bin/
    dimacs_sat.rs   -- DIMACS CNF solver CLI
    sudoku_solver.rs, nqueens_solver.rs, ...  -- Puzzle solvers
```

## Testing

```bash
cargo test              # All tests (~300)
cargo test --lib        # Library tests (141)
cargo test --test satlib     # SATLIB benchmarks (pigeonhole, Latin square, graph coloring)
cargo test --test properties # Property-based tests (proptest)
cargo clippy --all-targets --features stats  # Zero warnings
```

## Library Usage

```rust
use cdcl_sat::{CDCLSolver, Clause, Literal};

// Build clauses: (x1 OR x2) AND (NOT x1 OR x3)
let clauses = vec![
    Clause::new(vec![Literal::positive(1), Literal::positive(2)]),
    Clause::new(vec![Literal::negative(1), Literal::positive(3)]),
];

let mut solver = CDCLSolver::new(clauses);
assert!(solver.solve().unwrap()); // SAT

// Incremental solving (for CEGAR loops)
let mut solver = CDCLSolver::new_incremental(100);
solver.add_raw_clause(&[1, 2, 3]);
solver.add_raw_clause(&[-1, -2]);
assert!(solver.solve().unwrap());

// Add blocking clause and re-solve
solver.add_raw_clause(&[-3]);
solver.solve().unwrap();
```

## License

MIT
