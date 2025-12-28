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
