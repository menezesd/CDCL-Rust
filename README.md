# CDCL SAT Solver

A CDCL (Conflict-Driven Clause Learning) SAT solver implemented in Rust.

## Features

- **Prefix notation parser** for boolean expressions with operators: `and`, `or`, `not`, `impl`, `equiv`
- **Automatic CNF conversion** using Tseitin transformation when needed
- **Two-watched literals** for efficient unit propagation
- **Conflict analysis** with first-UIP learning
- **Non-chronological backtracking**
- **VSIDS-style** variable activity heuristics

## Usage

```bash
cargo build --release
echo "(and x1 (or (not x1) x2))" | ./target/release/cdcl_sat
```

### Input Format

Boolean formulas in prefix (Polish) notation:

| Operator | Syntax | Example |
|----------|--------|---------|
| Variable | `xN` | `x1`, `x2` |
| Negation | `(not expr)` | `(not x1)` |
| Conjunction | `(and expr expr)` | `(and x1 x2)` |
| Disjunction | `(or expr expr)` | `(or x1 x2)` |
| Implication | `(impl expr expr)` | `(impl x1 x2)` |
| Equivalence | `(equiv expr expr)` | `(equiv x1 x2)` |

### Output

- `SAT` if the formula is satisfiable
- `UNSAT` if the formula is unsatisfiable

## Examples

```bash
# Satisfiable formula
echo "(and x1 x2)" | cargo run
# Output: SAT

# Unsatisfiable formula (x1 AND NOT x1)
echo "(and x1 (not x1))" | cargo run
# Output: UNSAT

# Implication
echo "(impl x1 x2)" | cargo run
# Output: SAT
```

## License

MIT
