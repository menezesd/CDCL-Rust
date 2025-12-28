use std::collections::VecDeque;
use std::io::{self, Read};

// ============================================================================
// Expression AST
// ============================================================================

#[derive(Debug, Clone)]
enum Expr {
    Var(i32),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Impl(Box<Expr>, Box<Expr>),
    Equiv(Box<Expr>, Box<Expr>),
}

// ============================================================================
// Parser for prefix notation
// ============================================================================

struct Parser {
    tokens: VecDeque<String>,
}

impl Parser {
    fn new(input: &str) -> Self {
        let mut tokens = VecDeque::new();
        let mut current = String::new();

        for c in input.chars() {
            match c {
                '(' | ')' => {
                    if !current.is_empty() {
                        tokens.push_back(std::mem::take(&mut current));
                    }
                    tokens.push_back(c.to_string());
                }
                c if c.is_whitespace() => {
                    if !current.is_empty() {
                        tokens.push_back(std::mem::take(&mut current));
                    }
                }
                _ => current.push(c),
            }
        }
        if !current.is_empty() {
            tokens.push_back(current);
        }

        Parser { tokens }
    }

    fn peek(&self) -> Option<&str> {
        self.tokens.front().map(|s| s.as_str())
    }

    fn consume(&mut self) -> Option<String> {
        self.tokens.pop_front()
    }

    fn parse(&mut self) -> Expr {
        match self.peek() {
            Some("(") => {
                self.consume();
                let op = self.consume().expect("Expected operator");
                let expr = match op.as_str() {
                    "not" => Expr::Not(Box::new(self.parse())),
                    "and" => Expr::And(Box::new(self.parse()), Box::new(self.parse())),
                    "or" => Expr::Or(Box::new(self.parse()), Box::new(self.parse())),
                    "impl" => Expr::Impl(Box::new(self.parse()), Box::new(self.parse())),
                    "equiv" => Expr::Equiv(Box::new(self.parse()), Box::new(self.parse())),
                    _ => {
                        if let Some(num_str) = op.strip_prefix('x') {
                            let var_num: i32 = num_str.parse().expect("Invalid variable number");
                            self.expect(")");
                            return Expr::Var(var_num);
                        }
                        panic!("Unknown operator: {}", op);
                    }
                };
                self.expect(")");
                expr
            }
            Some(s) if s.starts_with('x') => {
                let var = self.consume().unwrap();
                let var_num: i32 = var.strip_prefix('x').unwrap().parse().expect("Invalid variable number");
                Expr::Var(var_num)
            }
            other => panic!("Unexpected token: {:?}", other),
        }
    }

    fn expect(&mut self, expected: &str) {
        let token = self.consume();
        if token.as_deref() != Some(expected) {
            panic!("Expected '{}', got '{:?}'", expected, token);
        }
    }
}

// ============================================================================
// Literal and Clause
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Literal {
    var: i32,
    negated: bool,
}

impl Literal {
    fn positive(var: i32) -> Self {
        Literal { var, negated: false }
    }

    fn negative(var: i32) -> Self {
        Literal { var, negated: true }
    }

    fn as_signed(self) -> i32 {
        if self.negated { -self.var } else { self.var }
    }
}

#[derive(Debug, Clone)]
struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    fn unit(lit: Literal) -> Self {
        Clause { literals: vec![lit] }
    }
}

// ============================================================================
// CNF Extraction (for already-CNF formulas)
// ============================================================================

fn is_clause(expr: &Expr) -> bool {
    match expr {
        Expr::Var(_) => true,
        Expr::Not(e) => matches!(e.as_ref(), Expr::Var(_)),
        Expr::Or(e1, e2) => is_clause(e1) && is_clause(e2),
        _ => false,
    }
}

fn extract_clause_literals(expr: &Expr, lits: &mut Vec<Literal>) -> bool {
    match expr {
        Expr::Var(v) => {
            lits.push(Literal::positive(*v));
            true
        }
        Expr::Not(e) => {
            if let Expr::Var(v) = e.as_ref() {
                lits.push(Literal::negative(*v));
                true
            } else {
                false
            }
        }
        Expr::Or(e1, e2) => {
            extract_clause_literals(e1, lits) && extract_clause_literals(e2, lits)
        }
        _ => false,
    }
}

fn is_cnf(expr: &Expr) -> bool {
    match expr {
        Expr::And(e1, e2) => {
            (is_cnf(e1) || is_clause(e1)) && (is_cnf(e2) || is_clause(e2))
        }
        _ => is_clause(expr),
    }
}

fn extract_cnf_clauses(expr: &Expr, clauses: &mut Vec<Clause>) -> bool {
    match expr {
        Expr::And(e1, e2) => {
            extract_cnf_clauses(e1, clauses) && extract_cnf_clauses(e2, clauses)
        }
        _ => {
            let mut lits = Vec::new();
            if extract_clause_literals(expr, &mut lits) {
                clauses.push(Clause::new(lits));
                true
            } else {
                false
            }
        }
    }
}

// ============================================================================
// Tseitin Transformation to CNF
// ============================================================================

struct TseitinTransformer {
    next_var: i32,
    clauses: Vec<Clause>,
}

impl TseitinTransformer {
    fn new(max_var: i32) -> Self {
        TseitinTransformer {
            next_var: max_var + 1,
            clauses: Vec::new(),
        }
    }

    fn fresh_var(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn transform(&mut self, expr: &Expr) -> i32 {
        match expr {
            Expr::Var(v) => *v,

            Expr::Not(e) => {
                let sub = self.transform(e);
                let result = self.fresh_var();
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::positive(sub),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::negative(sub),
                ]));
                result
            }

            Expr::And(e1, e2) => {
                let sub1 = self.transform(e1);
                let sub2 = self.transform(e2);
                let result = self.fresh_var();
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::positive(sub1),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::positive(sub2),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::negative(sub1),
                    Literal::negative(sub2),
                ]));
                result
            }

            Expr::Or(e1, e2) => {
                let sub1 = self.transform(e1);
                let sub2 = self.transform(e2);
                let result = self.fresh_var();
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::positive(sub1),
                    Literal::positive(sub2),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::negative(sub1),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::negative(sub2),
                ]));
                result
            }

            Expr::Impl(e1, e2) => {
                let sub1 = self.transform(e1);
                let sub2 = self.transform(e2);
                let result = self.fresh_var();
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::negative(sub1),
                    Literal::positive(sub2),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::positive(sub1),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::negative(sub2),
                ]));
                result
            }

            Expr::Equiv(e1, e2) => {
                let sub1 = self.transform(e1);
                let sub2 = self.transform(e2);
                let result = self.fresh_var();
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::negative(sub1),
                    Literal::positive(sub2),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::negative(result),
                    Literal::negative(sub2),
                    Literal::positive(sub1),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::positive(sub1),
                    Literal::positive(sub2),
                ]));
                self.clauses.push(Clause::new(vec![
                    Literal::positive(result),
                    Literal::negative(sub1),
                    Literal::negative(sub2),
                ]));
                result
            }
        }
    }

    fn into_clauses(mut self, root_var: i32) -> Vec<Clause> {
        self.clauses.push(Clause::unit(Literal::positive(root_var)));
        self.clauses
    }
}

fn find_max_var(expr: &Expr) -> i32 {
    match expr {
        Expr::Var(v) => *v,
        Expr::Not(e) => find_max_var(e),
        Expr::And(e1, e2) | Expr::Or(e1, e2) | Expr::Impl(e1, e2) | Expr::Equiv(e1, e2) => {
            find_max_var(e1).max(find_max_var(e2))
        }
    }
}

// ============================================================================
// CDCL Solver with Two-Watched Literals
// ============================================================================

#[derive(Debug, Clone)]
struct Assignment {
    decision_level: i32,
    antecedent_clause: Option<usize>,
}

struct CDCLSolver {
    clauses: Vec<Vec<i32>>,
    num_vars: i32,
    values: Vec<i8>,
    assignments: Vec<Option<Assignment>>,
    trail: Vec<i32>,
    trail_lim: Vec<usize>,
    decision_level: i32,
    var_activity: Vec<f64>,
    activity_inc: f64,
    watches: Vec<Vec<usize>>,
    propagation_queue: VecDeque<i32>,
    initial_conflict: bool,
}

impl CDCLSolver {
    fn new(clauses: Vec<Clause>) -> Self {
        let mut max_var = 0i32;
        for clause in &clauses {
            for lit in &clause.literals {
                max_var = max_var.max(lit.var);
            }
        }

        let num_vars = max_var;
        let num_lits = (num_vars as usize + 1) * 2;

        let mut solver_clauses: Vec<Vec<i32>> = Vec::new();
        let mut watches: Vec<Vec<usize>> = vec![Vec::new(); num_lits];
        let mut unit_clauses: Vec<(i32, usize)> = Vec::new();

        for clause in &clauses {
            let signed_lits: Vec<i32> = clause.literals.iter()
                .map(|l| l.as_signed())
                .collect();

            if signed_lits.is_empty() {
                continue;
            }

            let clause_idx = solver_clauses.len();

            if signed_lits.len() >= 2 {
                let w1 = Self::lit_to_watch_idx(signed_lits[0], num_vars);
                let w2 = Self::lit_to_watch_idx(signed_lits[1], num_vars);
                watches[w1].push(clause_idx);
                watches[w2].push(clause_idx);
            } else {
                unit_clauses.push((signed_lits[0], clause_idx));
            }

            solver_clauses.push(signed_lits);
        }

        let mut var_activity = vec![0.0; num_vars as usize + 1];
        for clause in &solver_clauses {
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                var_activity[var] += 1.0;
            }
        }

        let mut solver = CDCLSolver {
            clauses: solver_clauses,
            num_vars,
            values: vec![0; num_vars as usize + 1],
            assignments: vec![None; num_vars as usize + 1],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            var_activity,
            activity_inc: 1.0,
            watches,
            propagation_queue: VecDeque::new(),
            initial_conflict: false,
        };

        // Assign unit clauses
        for (lit, _clause_idx) in unit_clauses {
            let var = lit.unsigned_abs() as usize;
            if solver.values[var] == 0 {
                solver.assign(lit, None);
            } else {
                // Check for conflict
                let expected_val = if lit > 0 { 1 } else { -1 };
                if solver.values[var] != expected_val {
                    solver.initial_conflict = true;
                }
            }
        }

        solver
    }

    fn lit_to_watch_idx(lit: i32, _num_vars: i32) -> usize {
        let var = lit.abs();
        if lit > 0 {
            (var * 2) as usize
        } else {
            (var * 2 + 1) as usize
        }
    }

    fn lit_value(&self, lit: i32) -> i8 {
        let var = lit.unsigned_abs() as usize;
        let val = self.values[var];
        if lit < 0 { -val } else { val }
    }

    fn assign(&mut self, lit: i32, antecedent: Option<usize>) {
        let var = lit.unsigned_abs() as usize;
        self.values[var] = if lit > 0 { 1 } else { -1 };
        self.assignments[var] = Some(Assignment {
            decision_level: self.decision_level,
            antecedent_clause: antecedent,
        });
        self.trail.push(lit);
        self.propagation_queue.push_back(lit);
    }

    fn unassign(&mut self, var: usize) {
        self.values[var] = 0;
        self.assignments[var] = None;
    }

    fn propagate(&mut self) -> Option<usize> {
        while let Some(lit) = self.propagation_queue.pop_front() {
            let false_lit = -lit;
            let watch_idx = Self::lit_to_watch_idx(false_lit, self.num_vars);

            let mut i = 0;
            while i < self.watches[watch_idx].len() {
                let clause_idx = self.watches[watch_idx][i];
                let clause = &self.clauses[clause_idx];

                // Ensure false_lit is at position 1
                if clause[0] == false_lit {
                    self.clauses[clause_idx].swap(0, 1);
                }
                let clause = &self.clauses[clause_idx];

                let other_lit = clause[0];
                if self.lit_value(other_lit) == 1 {
                    i += 1;
                    continue;
                }

                // Find new watch
                let mut found_new = false;
                for (j, &new_lit) in clause.iter().enumerate().skip(2) {
                    if self.lit_value(new_lit) != -1 {
                        self.clauses[clause_idx].swap(1, j);
                        self.watches[watch_idx].swap_remove(i);
                        let new_watch_idx = Self::lit_to_watch_idx(self.clauses[clause_idx][1], self.num_vars);
                        self.watches[new_watch_idx].push(clause_idx);
                        found_new = true;
                        break;
                    }
                }

                if found_new {
                    continue;
                }

                let other_val = self.lit_value(other_lit);
                if other_val == -1 {
                    self.propagation_queue.clear();
                    return Some(clause_idx);
                } else if other_val == 0 {
                    self.assign(other_lit, Some(clause_idx));
                }

                i += 1;
            }
        }

        None
    }

    fn pick_branching_variable(&self) -> Option<i32> {
        let mut best_var = None;
        let mut best_activity = -1.0;

        for var in 1..=self.num_vars as usize {
            if self.values[var] == 0 {
                let activity = self.var_activity[var];
                if activity > best_activity {
                    best_activity = activity;
                    best_var = Some(var as i32);
                }
            }
        }

        best_var
    }

    fn analyze_conflict(&mut self, conflict_clause: usize) -> (Vec<i32>, i32) {
        let mut seen = vec![false; self.num_vars as usize + 1];
        let mut counter = 0;
        let mut learned: Vec<i32> = Vec::new();
        let mut p: Option<i32> = None;
        let mut clause_to_resolve = self.clauses[conflict_clause].clone();
        let mut trail_idx = self.trail.len();

        loop {
            // Add literals from the current clause
            for &lit in &clause_to_resolve {
                let var = lit.unsigned_abs() as usize;
                if Some(lit) == p || Some(-lit) == p {
                    continue;
                }
                if !seen[var] {
                    seen[var] = true;
                    let a = self.assignments[var].as_ref().unwrap();
                    if a.decision_level == self.decision_level {
                        counter += 1;
                    } else if a.decision_level > 0 {
                        learned.push(lit);
                        self.var_activity[var] += self.activity_inc;
                    }
                }
            }

            // Find next literal to resolve
            loop {
                trail_idx -= 1;
                let lit = self.trail[trail_idx];
                let var = lit.unsigned_abs() as usize;
                if seen[var] {
                    seen[var] = false;
                    p = Some(lit);
                    counter -= 1;

                    if counter == 0 {
                        // Found UIP
                        learned.insert(0, -lit);

                        // Calculate backtrack level
                        let mut bt_level = 0;
                        if learned.len() > 1 {
                            let mut max_idx = 1;
                            for i in 2..learned.len() {
                                let lvl = self.assignments[learned[i].unsigned_abs() as usize]
                                    .as_ref().unwrap().decision_level;
                                let max_lvl = self.assignments[learned[max_idx].unsigned_abs() as usize]
                                    .as_ref().unwrap().decision_level;
                                if lvl > max_lvl {
                                    max_idx = i;
                                }
                            }
                            learned.swap(1, max_idx);
                            bt_level = self.assignments[learned[1].unsigned_abs() as usize]
                                .as_ref().unwrap().decision_level;
                        }

                        // Bump activities
                        for &lit in &learned {
                            self.var_activity[lit.unsigned_abs() as usize] += self.activity_inc;
                        }

                        return (learned, bt_level);
                    }

                    // Get antecedent
                    if let Some(ante) = self.assignments[var].as_ref().unwrap().antecedent_clause {
                        clause_to_resolve = self.clauses[ante].clone();
                        break;
                    } else {
                        panic!("Decision variable in conflict analysis with counter > 0");
                    }
                }
            }
        }
    }

    fn backtrack(&mut self, level: i32) {
        while self.trail.len() > *self.trail_lim.get(level as usize).unwrap_or(&0) {
            let lit = self.trail.pop().unwrap();
            let var = lit.unsigned_abs() as usize;
            self.unassign(var);
        }
        self.trail_lim.truncate(level as usize);
        self.decision_level = level;
        self.propagation_queue.clear();
    }

    fn add_learned_clause(&mut self, learned: Vec<i32>) {
        if learned.is_empty() {
            return;
        }

        let clause_idx = self.clauses.len();

        if learned.len() >= 2 {
            let w1 = Self::lit_to_watch_idx(learned[0], self.num_vars);
            let w2 = Self::lit_to_watch_idx(learned[1], self.num_vars);
            self.watches[w1].push(clause_idx);
            self.watches[w2].push(clause_idx);
        }

        self.clauses.push(learned);
    }

    fn decay_activities(&mut self) {
        self.activity_inc *= 1.05;
        if self.activity_inc > 1e100 {
            for i in 1..=self.num_vars as usize {
                self.var_activity[i] *= 1e-100;
            }
            self.activity_inc *= 1e-100;
        }
    }

    fn solve(&mut self) -> bool {
        if self.initial_conflict {
            return false;
        }
        if self.propagate().is_some() {
            return false;
        }

        loop {
            match self.pick_branching_variable() {
                Some(var) => {
                    self.decision_level += 1;
                    self.trail_lim.push(self.trail.len());
                    self.assign(var, None);

                    loop {
                        match self.propagate() {
                            None => break,
                            Some(conflict_clause) => {
                                if self.decision_level == 0 {
                                    return false;
                                }

                                let (learned, backtrack_level) = self.analyze_conflict(conflict_clause);
                                self.backtrack(backtrack_level);

                                let unit_lit = learned[0];
                                self.add_learned_clause(learned);
                                self.assign(unit_lit, Some(self.clauses.len() - 1));

                                self.decay_activities();
                            }
                        }
                    }
                }
                None => {
                    return true;
                }
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // Parser Tests
    // ------------------------------------------------------------------------

    mod parser_tests {
        use super::*;

        #[test]
        fn test_parse_single_variable() {
            let mut parser = Parser::new("x1");
            let expr = parser.parse();
            assert!(matches!(expr, Expr::Var(1)));
        }

        #[test]
        fn test_parse_variable_with_parens() {
            let mut parser = Parser::new("(x42)");
            let expr = parser.parse();
            assert!(matches!(expr, Expr::Var(42)));
        }

        #[test]
        fn test_parse_not() {
            let mut parser = Parser::new("(not x1)");
            let expr = parser.parse();
            if let Expr::Not(inner) = expr {
                assert!(matches!(*inner, Expr::Var(1)));
            } else {
                panic!("Expected Not expression");
            }
        }

        #[test]
        fn test_parse_and() {
            let mut parser = Parser::new("(and x1 x2)");
            let expr = parser.parse();
            if let Expr::And(left, right) = expr {
                assert!(matches!(*left, Expr::Var(1)));
                assert!(matches!(*right, Expr::Var(2)));
            } else {
                panic!("Expected And expression");
            }
        }

        #[test]
        fn test_parse_or() {
            let mut parser = Parser::new("(or x3 x4)");
            let expr = parser.parse();
            if let Expr::Or(left, right) = expr {
                assert!(matches!(*left, Expr::Var(3)));
                assert!(matches!(*right, Expr::Var(4)));
            } else {
                panic!("Expected Or expression");
            }
        }

        #[test]
        fn test_parse_impl() {
            let mut parser = Parser::new("(impl x1 x2)");
            let expr = parser.parse();
            if let Expr::Impl(left, right) = expr {
                assert!(matches!(*left, Expr::Var(1)));
                assert!(matches!(*right, Expr::Var(2)));
            } else {
                panic!("Expected Impl expression");
            }
        }

        #[test]
        fn test_parse_equiv() {
            let mut parser = Parser::new("(equiv x1 x2)");
            let expr = parser.parse();
            if let Expr::Equiv(left, right) = expr {
                assert!(matches!(*left, Expr::Var(1)));
                assert!(matches!(*right, Expr::Var(2)));
            } else {
                panic!("Expected Equiv expression");
            }
        }

        #[test]
        fn test_parse_nested() {
            let mut parser = Parser::new("(and (or x1 x2) (not x3))");
            let expr = parser.parse();
            if let Expr::And(left, right) = expr {
                assert!(matches!(*left, Expr::Or(_, _)));
                assert!(matches!(*right, Expr::Not(_)));
            } else {
                panic!("Expected nested And expression");
            }
        }

        #[test]
        fn test_parse_deeply_nested() {
            let mut parser = Parser::new("(and (or (not x1) x2) (impl x3 (equiv x4 x5)))");
            let expr = parser.parse();
            assert!(matches!(expr, Expr::And(_, _)));
        }

        #[test]
        fn test_parse_whitespace_handling() {
            let mut parser = Parser::new("  (  and   x1    x2  )  ");
            let expr = parser.parse();
            assert!(matches!(expr, Expr::And(_, _)));
        }

        #[test]
        fn test_parse_large_variable_number() {
            let mut parser = Parser::new("x999");
            let expr = parser.parse();
            assert!(matches!(expr, Expr::Var(999)));
        }
    }

    // ------------------------------------------------------------------------
    // Literal Tests
    // ------------------------------------------------------------------------

    mod literal_tests {
        use super::*;

        #[test]
        fn test_positive_literal() {
            let lit = Literal::positive(5);
            assert_eq!(lit.var, 5);
            assert!(!lit.negated);
            assert_eq!(lit.as_signed(), 5);
        }

        #[test]
        fn test_negative_literal() {
            let lit = Literal::negative(5);
            assert_eq!(lit.var, 5);
            assert!(lit.negated);
            assert_eq!(lit.as_signed(), -5);
        }

        #[test]
        fn test_literal_equality() {
            let lit1 = Literal::positive(3);
            let lit2 = Literal::positive(3);
            let lit3 = Literal::negative(3);
            assert_eq!(lit1, lit2);
            assert_ne!(lit1, lit3);
        }

        #[test]
        fn test_clause_creation() {
            let clause = Clause::new(vec![
                Literal::positive(1),
                Literal::negative(2),
            ]);
            assert_eq!(clause.literals.len(), 2);
        }

        #[test]
        fn test_unit_clause() {
            let clause = Clause::unit(Literal::positive(7));
            assert_eq!(clause.literals.len(), 1);
            assert_eq!(clause.literals[0].var, 7);
        }
    }

    // ------------------------------------------------------------------------
    // CNF Detection and Extraction Tests
    // ------------------------------------------------------------------------

    mod cnf_tests {
        use super::*;

        #[test]
        fn test_is_clause_single_var() {
            let expr = Expr::Var(1);
            assert!(is_clause(&expr));
        }

        #[test]
        fn test_is_clause_negated_var() {
            let expr = Expr::Not(Box::new(Expr::Var(1)));
            assert!(is_clause(&expr));
        }

        #[test]
        fn test_is_clause_or_of_literals() {
            let expr = Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Not(Box::new(Expr::Var(2)))),
            );
            assert!(is_clause(&expr));
        }

        #[test]
        fn test_is_clause_nested_or() {
            let expr = Expr::Or(
                Box::new(Expr::Or(
                    Box::new(Expr::Var(1)),
                    Box::new(Expr::Var(2)),
                )),
                Box::new(Expr::Var(3)),
            );
            assert!(is_clause(&expr));
        }

        #[test]
        fn test_is_clause_and_not_clause() {
            let expr = Expr::And(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            assert!(!is_clause(&expr));
        }

        #[test]
        fn test_is_clause_double_negation_not_clause() {
            let expr = Expr::Not(Box::new(Expr::Not(Box::new(Expr::Var(1)))));
            assert!(!is_clause(&expr));
        }

        #[test]
        fn test_is_cnf_single_clause() {
            let expr = Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            assert!(is_cnf(&expr));
        }

        #[test]
        fn test_is_cnf_and_of_clauses() {
            let expr = Expr::And(
                Box::new(Expr::Or(
                    Box::new(Expr::Var(1)),
                    Box::new(Expr::Var(2)),
                )),
                Box::new(Expr::Or(
                    Box::new(Expr::Var(3)),
                    Box::new(Expr::Not(Box::new(Expr::Var(4)))),
                )),
            );
            assert!(is_cnf(&expr));
        }

        #[test]
        fn test_is_cnf_nested_and() {
            let expr = Expr::And(
                Box::new(Expr::And(
                    Box::new(Expr::Var(1)),
                    Box::new(Expr::Var(2)),
                )),
                Box::new(Expr::Var(3)),
            );
            assert!(is_cnf(&expr));
        }

        #[test]
        fn test_is_cnf_impl_not_cnf() {
            let expr = Expr::Impl(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            assert!(!is_cnf(&expr));
        }

        #[test]
        fn test_extract_clause_literals() {
            let expr = Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Not(Box::new(Expr::Var(2)))),
            );
            let mut lits = Vec::new();
            assert!(extract_clause_literals(&expr, &mut lits));
            assert_eq!(lits.len(), 2);
            assert_eq!(lits[0].var, 1);
            assert!(!lits[0].negated);
            assert_eq!(lits[1].var, 2);
            assert!(lits[1].negated);
        }

        #[test]
        fn test_extract_cnf_clauses() {
            let expr = Expr::And(
                Box::new(Expr::Or(
                    Box::new(Expr::Var(1)),
                    Box::new(Expr::Var(2)),
                )),
                Box::new(Expr::Or(
                    Box::new(Expr::Var(3)),
                    Box::new(Expr::Var(4)),
                )),
            );
            let mut clauses = Vec::new();
            assert!(extract_cnf_clauses(&expr, &mut clauses));
            assert_eq!(clauses.len(), 2);
        }
    }

    // ------------------------------------------------------------------------
    // Tseitin Transformation Tests
    // ------------------------------------------------------------------------

    mod tseitin_tests {
        use super::*;

        #[test]
        fn test_find_max_var() {
            let expr = Expr::And(
                Box::new(Expr::Var(5)),
                Box::new(Expr::Or(
                    Box::new(Expr::Var(3)),
                    Box::new(Expr::Var(10)),
                )),
            );
            assert_eq!(find_max_var(&expr), 10);
        }

        #[test]
        fn test_tseitin_single_var() {
            let expr = Expr::Var(1);
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            assert_eq!(root, 1);
            assert!(transformer.clauses.is_empty());
        }

        #[test]
        fn test_tseitin_not() {
            let expr = Expr::Not(Box::new(Expr::Var(1)));
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            // root should be a fresh variable (2)
            assert_eq!(root, 2);
            // NOT creates 2 clauses
            assert_eq!(transformer.clauses.len(), 2);
        }

        #[test]
        fn test_tseitin_and() {
            let expr = Expr::And(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            // AND creates 3 clauses
            assert_eq!(transformer.clauses.len(), 3);
            assert_eq!(root, 3);
        }

        #[test]
        fn test_tseitin_or() {
            let expr = Expr::Or(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            // OR creates 3 clauses
            assert_eq!(transformer.clauses.len(), 3);
            assert_eq!(root, 3);
        }

        #[test]
        fn test_tseitin_impl() {
            let expr = Expr::Impl(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            // IMPL creates 3 clauses
            assert_eq!(transformer.clauses.len(), 3);
            assert_eq!(root, 3);
        }

        #[test]
        fn test_tseitin_equiv() {
            let expr = Expr::Equiv(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            // EQUIV creates 4 clauses
            assert_eq!(transformer.clauses.len(), 4);
            assert_eq!(root, 3);
        }

        #[test]
        fn test_tseitin_into_clauses_adds_unit() {
            let expr = Expr::And(
                Box::new(Expr::Var(1)),
                Box::new(Expr::Var(2)),
            );
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root = transformer.transform(&expr);
            let clauses = transformer.into_clauses(root);
            // AND creates 3 clauses + 1 unit clause for root
            assert_eq!(clauses.len(), 4);
            // Last clause should be unit clause asserting root
            let last = &clauses[clauses.len() - 1];
            assert_eq!(last.literals.len(), 1);
            assert_eq!(last.literals[0].var, root);
            assert!(!last.literals[0].negated);
        }
    }

    // ------------------------------------------------------------------------
    // CDCL Solver Tests
    // ------------------------------------------------------------------------

    mod solver_tests {
        use super::*;

        fn solve_formula(input: &str) -> bool {
            let mut parser = Parser::new(input);
            let expr = parser.parse();

            let clauses = if is_cnf(&expr) {
                let mut clauses = Vec::new();
                if extract_cnf_clauses(&expr, &mut clauses) {
                    clauses
                } else {
                    let max_var = find_max_var(&expr);
                    let mut transformer = TseitinTransformer::new(max_var);
                    let root_var = transformer.transform(&expr);
                    transformer.into_clauses(root_var)
                }
            } else {
                let max_var = find_max_var(&expr);
                let mut transformer = TseitinTransformer::new(max_var);
                let root_var = transformer.transform(&expr);
                transformer.into_clauses(root_var)
            };

            let mut solver = CDCLSolver::new(clauses);
            solver.solve()
        }

        // Basic SAT tests
        #[test]
        fn test_single_variable_sat() {
            assert!(solve_formula("x1"));
        }

        #[test]
        fn test_two_variables_sat() {
            assert!(solve_formula("(and x1 x2)"));
        }

        #[test]
        fn test_or_sat() {
            assert!(solve_formula("(or x1 x2)"));
        }

        // Basic UNSAT tests
        #[test]
        fn test_contradiction_unsat() {
            assert!(!solve_formula("(and x1 (not x1))"));
        }

        #[test]
        fn test_complex_unsat() {
            // (x1 OR x2) AND (NOT x1) AND (NOT x2) is UNSAT
            assert!(!solve_formula("(and (and (or x1 x2) (not x1)) (not x2))"));
        }

        // Tautology tests
        #[test]
        fn test_tautology_sat() {
            assert!(solve_formula("(or x1 (not x1))"));
        }

        // Implication tests
        #[test]
        fn test_impl_sat() {
            assert!(solve_formula("(impl x1 x2)"));
        }

        #[test]
        fn test_impl_chain_sat() {
            // (x1 -> x2) AND (x2 -> x3) AND x1 should be SAT
            assert!(solve_formula("(and (and (impl x1 x2) (impl x2 x3)) x1)"));
        }

        // Equivalence tests
        #[test]
        fn test_equiv_sat() {
            assert!(solve_formula("(equiv x1 x2)"));
        }

        #[test]
        fn test_equiv_contradiction_unsat() {
            // x1 <-> x2 AND x1 AND NOT x2 is UNSAT
            assert!(!solve_formula("(and (and (equiv x1 x2) x1) (not x2))"));
        }

        // Complex formula tests
        #[test]
        fn test_nested_formula_sat() {
            assert!(solve_formula("(or x1 (not (and x2 x3)))"));
        }

        #[test]
        fn test_deeply_nested_sat() {
            assert!(solve_formula("(and (or (not x1) x2) (or x1 x3))"));
        }

        // Edge cases
        #[test]
        fn test_unit_propagation_simple() {
            // x1 AND (x1 -> x2) should result in both x1 and x2 being true
            assert!(solve_formula("(and x1 (impl x1 x2))"));
        }

        #[test]
        fn test_pigeonhole_small() {
            // Simple pigeonhole: 2 pigeons, 1 hole (UNSAT)
            // p11 = pigeon 1 in hole 1, p21 = pigeon 2 in hole 1
            // Each pigeon must be in some hole: p11, p21
            // At most one pigeon per hole: NOT (p11 AND p21)
            // Combined: p11 AND p21 AND NOT (p11 AND p21) = UNSAT
            assert!(!solve_formula("(and (and x1 x2) (not (and x1 x2)))"));
        }
    }

    // ------------------------------------------------------------------------
    // Integration Tests
    // ------------------------------------------------------------------------

    mod integration_tests {
        use super::*;

        fn solve_formula(input: &str) -> bool {
            let mut parser = Parser::new(input);
            let expr = parser.parse();

            let clauses = if is_cnf(&expr) {
                let mut clauses = Vec::new();
                if extract_cnf_clauses(&expr, &mut clauses) {
                    clauses
                } else {
                    let max_var = find_max_var(&expr);
                    let mut transformer = TseitinTransformer::new(max_var);
                    let root_var = transformer.transform(&expr);
                    transformer.into_clauses(root_var)
                }
            } else {
                let max_var = find_max_var(&expr);
                let mut transformer = TseitinTransformer::new(max_var);
                let root_var = transformer.transform(&expr);
                transformer.into_clauses(root_var)
            };

            let mut solver = CDCLSolver::new(clauses);
            solver.solve()
        }

        #[test]
        fn test_ex1_single_var() {
            // ex1: x1 (SAT)
            assert!(solve_formula("x1"));
        }

        #[test]
        fn test_ex2_contradiction() {
            // ex2: (and x1 (not x1)) (UNSAT)
            assert!(!solve_formula("(and x1 (not x1))"));
        }

        #[test]
        fn test_ex3_nested_or() {
            // ex3: (or x1 (not (and x2 x3))) (SAT)
            assert!(solve_formula("(or x1 (not (and x2 x3)))"));
        }

        #[test]
        fn test_all_operators_combined() {
            // Test formula using all operators
            let formula = "(and (impl x1 x2) (equiv x3 (or x1 (not x4))))";
            // This should be satisfiable
            assert!(solve_formula(formula));
        }

        #[test]
        fn test_cnf_direct_extraction() {
            // A CNF formula that should be extracted directly
            // (x1 OR x2) AND (NOT x1 OR x3)
            let formula = "(and (or x1 x2) (or (not x1) x3))";
            assert!(solve_formula(formula));
        }

        #[test]
        fn test_larger_cnf() {
            // Larger CNF formula
            let formula = "(and (and (and (or x1 x2) (or (not x1) x3)) (or (not x2) x4)) (or x1 (not x4)))";
            assert!(solve_formula(formula));
        }

        #[test]
        fn test_unsat_3_clauses() {
            // (x1) AND (NOT x1 OR x2) AND (NOT x2) is UNSAT
            // After unit propagation: x1=T, x2=T, but (NOT x2) conflicts
            let formula = "(and (and x1 (or (not x1) x2)) (not x2))";
            assert!(!solve_formula(formula));
        }

        #[test]
        fn test_chain_implication_sat() {
            // Chain of implications that is satisfiable
            let formula = "(and (and (and (impl x1 x2) (impl x2 x3)) (impl x3 x4)) (and x1 x4))";
            assert!(solve_formula(formula));
        }

        #[test]
        fn test_chain_implication_unsat() {
            // Chain of implications with contradiction
            // x1 -> x2 -> x3, x1 AND NOT x3
            let formula = "(and (and (and (impl x1 x2) (impl x2 x3)) x1) (not x3))";
            assert!(!solve_formula(formula));
        }

        #[test]
        fn test_equiv_chain_sat() {
            // x1 <-> x2 <-> x3 with x1 AND x3
            let formula = "(and (and (equiv x1 x2) (equiv x2 x3)) (and x1 x3))";
            assert!(solve_formula(formula));
        }

        #[test]
        fn test_equiv_chain_unsat() {
            // x1 <-> x2 <-> x3 with x1 AND NOT x3
            let formula = "(and (and (equiv x1 x2) (equiv x2 x3)) (and x1 (not x3)))";
            assert!(!solve_formula(formula));
        }
    }

    // ------------------------------------------------------------------------
    // Property-Based Tests
    // ------------------------------------------------------------------------

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        fn solve_formula(input: &str) -> bool {
            let mut parser = Parser::new(input);
            let expr = parser.parse();

            let clauses = if is_cnf(&expr) {
                let mut clauses = Vec::new();
                if extract_cnf_clauses(&expr, &mut clauses) {
                    clauses
                } else {
                    let max_var = find_max_var(&expr);
                    let mut transformer = TseitinTransformer::new(max_var);
                    let root_var = transformer.transform(&expr);
                    transformer.into_clauses(root_var)
                }
            } else {
                let max_var = find_max_var(&expr);
                let mut transformer = TseitinTransformer::new(max_var);
                let root_var = transformer.transform(&expr);
                transformer.into_clauses(root_var)
            };

            let mut solver = CDCLSolver::new(clauses);
            solver.solve()
        }

        // Strategy to generate expression AST
        fn arb_expr(depth: u32, max_var: i32) -> impl Strategy<Value = Expr> {
            let leaf = (1..=max_var).prop_map(Expr::Var);

            if depth == 0 {
                leaf.boxed()
            } else {
                prop_oneof![
                    // Variables (more weight)
                    3 => (1..=max_var).prop_map(Expr::Var),
                    // Unary
                    1 => arb_expr(depth - 1, max_var).prop_map(|e| Expr::Not(Box::new(e))),
                    // Binary ops
                    1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                        .prop_map(|(a, b)| Expr::And(Box::new(a), Box::new(b))),
                    1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                        .prop_map(|(a, b)| Expr::Or(Box::new(a), Box::new(b))),
                    1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                        .prop_map(|(a, b)| Expr::Impl(Box::new(a), Box::new(b))),
                    1 => (arb_expr(depth - 1, max_var), arb_expr(depth - 1, max_var))
                        .prop_map(|(a, b)| Expr::Equiv(Box::new(a), Box::new(b))),
                ].boxed()
            }
        }

        // Convert Expr to string representation
        fn expr_to_string(expr: &Expr) -> String {
            match expr {
                Expr::Var(v) => format!("x{}", v),
                Expr::Not(e) => format!("(not {})", expr_to_string(e)),
                Expr::And(a, b) => format!("(and {} {})", expr_to_string(a), expr_to_string(b)),
                Expr::Or(a, b) => format!("(or {} {})", expr_to_string(a), expr_to_string(b)),
                Expr::Impl(a, b) => format!("(impl {} {})", expr_to_string(a), expr_to_string(b)),
                Expr::Equiv(a, b) => format!("(equiv {} {})", expr_to_string(a), expr_to_string(b)),
            }
        }

        proptest! {
            // Property: Any single variable is satisfiable
            #[test]
            fn prop_single_var_sat(var in 1..100i32) {
                let formula = format!("x{}", var);
                prop_assert!(solve_formula(&formula));
            }

            // Property: x AND NOT x is always unsatisfiable
            #[test]
            fn prop_contradiction_unsat(var in 1..100i32) {
                let formula = format!("(and x{} (not x{}))", var, var);
                prop_assert!(!solve_formula(&formula));
            }

            // Property: x OR NOT x is always satisfiable (tautology)
            #[test]
            fn prop_tautology_sat(var in 1..100i32) {
                let formula = format!("(or x{} (not x{}))", var, var);
                prop_assert!(solve_formula(&formula));
            }

            // Property: x IMPL x is always satisfiable (reflexive implication)
            #[test]
            fn prop_reflexive_impl_sat(var in 1..100i32) {
                let formula = format!("(impl x{} x{})", var, var);
                prop_assert!(solve_formula(&formula));
            }

            // Property: x EQUIV x is always satisfiable (reflexive equivalence)
            #[test]
            fn prop_reflexive_equiv_sat(var in 1..100i32) {
                let formula = format!("(equiv x{} x{})", var, var);
                prop_assert!(solve_formula(&formula));
            }

            // Property: NOT NOT x is equivalent to x (solver terminates)
            #[test]
            fn prop_double_negation(var in 1..100i32) {
                let formula = format!("(not (not x{}))", var);
                prop_assert!(solve_formula(&formula));
            }

            // Property: (x AND y) OR (NOT x AND NOT y) is satisfiable
            #[test]
            fn prop_xor_like_sat(x in 1..50i32, y in 51..100i32) {
                let formula = format!(
                    "(or (and x{} x{}) (and (not x{}) (not x{})))",
                    x, y, x, y
                );
                prop_assert!(solve_formula(&formula));
            }

            // Property: Implication chain with antecedent true is satisfiable
            #[test]
            fn prop_impl_chain_sat(n in 2..5usize) {
                let mut formula = format!("x1");
                for i in 1..n {
                    formula = format!("(and {} (impl x{} x{}))", formula, i, i + 1);
                }
                prop_assert!(solve_formula(&formula));
            }

            // Property: Implication chain with contradiction is unsatisfiable
            #[test]
            fn prop_impl_chain_unsat(n in 2..5usize) {
                let mut formula = format!("(and x1 (not x{}))", n);
                for i in 1..n {
                    formula = format!("(and {} (impl x{} x{}))", formula, i, i + 1);
                }
                prop_assert!(!solve_formula(&formula));
            }

            // Property: Random expressions should terminate (solver doesn't hang)
            #[test]
            fn prop_solver_terminates(expr in arb_expr(3, 5)) {
                let formula = expr_to_string(&expr);
                // Just verify it terminates and returns a boolean
                let _result = solve_formula(&formula);
            }

            // Property: Parser round-trip works for generated expressions
            #[test]
            fn prop_parser_roundtrip(expr in arb_expr(2, 5)) {
                let formula = expr_to_string(&expr);
                let mut parser = Parser::new(&formula);
                let parsed = parser.parse();
                let reparsed = expr_to_string(&parsed);
                prop_assert_eq!(formula, reparsed);
            }

            // Property: CNF formulas should solve faster (via direct extraction)
            #[test]
            fn prop_cnf_formula_solves(
                num_clauses in 2..5usize,
                clause_size in 2..4usize,
                num_vars in 3..6i32
            ) {
                // Generate a random CNF formula
                let mut clauses = Vec::new();
                for _ in 0..num_clauses {
                    let mut clause = String::new();
                    for j in 0..clause_size {
                        let var = (j as i32 % num_vars) + 1;
                        let lit = if j % 2 == 0 {
                            format!("x{}", var)
                        } else {
                            format!("(not x{})", var)
                        };
                        if clause.is_empty() {
                            clause = lit;
                        } else {
                            clause = format!("(or {} {})", clause, lit);
                        }
                    }
                    clauses.push(clause);
                }
                let mut formula = clauses[0].clone();
                for clause in clauses.iter().skip(1) {
                    formula = format!("(and {} {})", formula, clause);
                }
                // Just verify it terminates
                let _result = solve_formula(&formula);
            }

            // Property: De Morgan's laws - NOT (a AND b) = NOT a OR NOT b
            #[test]
            fn prop_demorgan_and(a in 1..50i32, b in 51..100i32) {
                // Both should be equisatisfiable with any assignment
                let formula1 = format!("(not (and x{} x{}))", a, b);
                let formula2 = format!("(or (not x{}) (not x{}))", a, b);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: De Morgan's laws - NOT (a OR b) = NOT a AND NOT b
            #[test]
            fn prop_demorgan_or(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(not (or x{} x{}))", a, b);
                let formula2 = format!("(and (not x{}) (not x{}))", a, b);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Implication equivalence - (a IMPL b) = (NOT a OR b)
            #[test]
            fn prop_impl_equiv(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(impl x{} x{})", a, b);
                let formula2 = format!("(or (not x{}) x{})", a, b);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Equivalence definition - (a EQUIV b) = (a IMPL b) AND (b IMPL a)
            #[test]
            fn prop_equiv_definition(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(equiv x{} x{})", a, b);
                let formula2 = format!("(and (impl x{} x{}) (impl x{} x{}))", a, b, b, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Commutative AND
            #[test]
            fn prop_and_commutative(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(and x{} x{})", a, b);
                let formula2 = format!("(and x{} x{})", b, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Commutative OR
            #[test]
            fn prop_or_commutative(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(or x{} x{})", a, b);
                let formula2 = format!("(or x{} x{})", b, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Commutative EQUIV
            #[test]
            fn prop_equiv_commutative(a in 1..50i32, b in 51..100i32) {
                let formula1 = format!("(equiv x{} x{})", a, b);
                let formula2 = format!("(equiv x{} x{})", b, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Associative AND - solver gives same result
            #[test]
            fn prop_and_associative(a in 1..33i32, b in 34..66i32, c in 67..100i32) {
                let formula1 = format!("(and (and x{} x{}) x{})", a, b, c);
                let formula2 = format!("(and x{} (and x{} x{}))", a, b, c);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Associative OR - solver gives same result
            #[test]
            fn prop_or_associative(a in 1..33i32, b in 34..66i32, c in 67..100i32) {
                let formula1 = format!("(or (or x{} x{}) x{})", a, b, c);
                let formula2 = format!("(or x{} (or x{} x{}))", a, b, c);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Absorption - a AND (a OR b) = a
            #[test]
            fn prop_absorption_and(a in 1..50i32, b in 51..100i32) {
                let formula = format!("(and x{} (or x{} x{}))", a, a, b);
                // Should be SAT if and only if x_a is assigned true
                prop_assert!(solve_formula(&formula));
            }

            // Property: Idempotent AND - a AND a = a
            #[test]
            fn prop_idempotent_and(a in 1..100i32) {
                let formula1 = format!("x{}", a);
                let formula2 = format!("(and x{} x{})", a, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }

            // Property: Idempotent OR - a OR a = a
            #[test]
            fn prop_idempotent_or(a in 1..100i32) {
                let formula1 = format!("x{}", a);
                let formula2 = format!("(or x{} x{})", a, a);
                prop_assert_eq!(solve_formula(&formula1), solve_formula(&formula2));
            }
        }
    }
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("Failed to read input");

    let mut parser = Parser::new(&input);
    let expr = parser.parse();

    let clauses = if is_cnf(&expr) {
        let mut clauses = Vec::new();
        if extract_cnf_clauses(&expr, &mut clauses) {
            clauses
        } else {
            let max_var = find_max_var(&expr);
            let mut transformer = TseitinTransformer::new(max_var);
            let root_var = transformer.transform(&expr);
            transformer.into_clauses(root_var)
        }
    } else {
        let max_var = find_max_var(&expr);
        let mut transformer = TseitinTransformer::new(max_var);
        let root_var = transformer.transform(&expr);
        transformer.into_clauses(root_var)
    };

    let mut solver = CDCLSolver::new(clauses);
    let result = solver.solve();

    if result {
        println!("SAT");
    } else {
        println!("UNSAT");
    }
}
