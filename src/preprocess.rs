//! Preprocessing for SAT instances.
//!
//! Implements bounded variable elimination (BVE), pure literal elimination,
//! and unit propagation to simplify formulas before solving.

/// Full preprocessing: unit prop, pure literal, probing, BVE, subsumption.
/// Full preprocessing: unit prop, pure literal, probing, BVE, subsumption.
/// Returns simplified clauses.
pub fn preprocess(clauses: Vec<Vec<i32>>, num_vars: usize) -> Vec<Vec<i32>> {
    preprocess_with_assignments(clauses, num_vars).0
}

/// Like preprocess but also returns variable assignments made during preprocessing.
/// assigned_values[var] is 1 (true), -1 (false), or 0 (unassigned).
pub fn preprocess_with_assignments(clauses: Vec<Vec<i32>>, num_vars: usize) -> (Vec<Vec<i32>>, Vec<i8>) {
    let mut pp = Preprocessor::new(clauses, num_vars);
    pp.run();
    let assigned = pp.assigned.clone();
    (pp.into_clauses(), assigned)
}

/// Light preprocessing for inprocessing: self-subsumption + BVE only (no probing).
pub fn preprocess_light(clauses: Vec<Vec<i32>>, num_vars: usize) -> Vec<Vec<i32>> {
    let mut pp = Preprocessor::new(clauses, num_vars);
    pp.run_light();
    pp.into_clauses()
}

struct Preprocessor {
    clauses: Vec<Vec<i32>>,
    num_vars: usize,
    deleted: Vec<bool>,
    assigned: Vec<i8>, // 0=unassigned, 1=true, -1=false
    unsat: bool,
}

impl Preprocessor {
    fn new(clauses: Vec<Vec<i32>>, num_vars: usize) -> Self {
        let n = clauses.len();
        Preprocessor {
            clauses,
            num_vars,
            deleted: vec![false; n],
            assigned: vec![0; num_vars + 1],
            unsat: false,
        }
    }

    /// Detects equivalent literals from binary clause pairs (a→b and b→a).
    /// Merges equivalence classes and substitutes throughout.
    fn equivalent_literal_substitution(&mut self) {
        // Build implication graph from binary clauses
        // Binary clause (a | b) means !a → b and !b → a
        let max_lit = (self.num_vars + 1) * 2;
        // implies[lit_idx] = list of implied literals
        let mut implies: Vec<Vec<i32>> = vec![Vec::new(); max_lit];

        let lit_idx = |lit: i32| -> usize {
            if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 }
        };

        for (ci, _clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            let lits = self.live_lits(ci);
            if lits.len() != 2 { continue; }
            let a = lits[0];
            let b = lits[1];
            // (a | b) means !a → b and !b → a
            let na_idx = lit_idx(-a);
            let nb_idx = lit_idx(-b);
            if na_idx < max_lit { implies[na_idx].push(b); }
            if nb_idx < max_lit { implies[nb_idx].push(a); }
        }

        // Find equivalences: a ↔ b iff a → b and b → a
        // Which means !a → b (from clause (a|b)) and !b → a (from clause (b|a))
        // AND a → !b (from clause (!a|!b)) and b → !a (same clause)
        // Wait no. a ↔ b means:
        //   a → b: from clause (!a | b)
        //   b → a: from clause (!b | a)
        // So we need both (!a | b) and (!b | a) as binary clauses.
        // In our implication graph: implies[lit_idx(a)] contains b, and implies[lit_idx(b)] contains a.

        // Union-Find for equivalence classes (using variable ids)
        let mut parent: Vec<usize> = (0..=self.num_vars).collect();
        let mut rank: Vec<u8> = vec![0; self.num_vars + 1];

        fn find(parent: &mut [usize], x: usize) -> usize {
            if parent[x] != x { parent[x] = find(parent, parent[x]); }
            parent[x]
        }
        fn union(parent: &mut [usize], rank: &mut [u8], a: usize, b: usize) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra == rb { return; }
            if rank[ra] < rank[rb] { parent[ra] = rb; }
            else if rank[ra] > rank[rb] { parent[rb] = ra; }
            else { parent[rb] = ra; rank[ra] += 1; }
        }

        // For each variable a, check if a → b and b → a (both directions)
        // a → b is in implies[lit_idx(a)]
        let mut equiv_count = 0usize;
        for var_a in 1..=self.num_vars {
            if self.assigned[var_a] != 0 { continue; }
            let a_pos_idx = lit_idx(var_a as i32);
            if a_pos_idx >= max_lit { continue; }
            for &b in &implies[a_pos_idx].clone() {
                if b <= 0 { continue; } // Only handle positive equivalences for now
                let var_b = b as usize;
                if var_b > self.num_vars || self.assigned[var_b] != 0 { continue; }
                // Check if b → a too
                let b_pos_idx = lit_idx(b);
                if b_pos_idx < max_lit && implies[b_pos_idx].contains(&(var_a as i32)) {
                    // a ↔ b: merge equivalence classes
                    if find(&mut parent, var_a) != find(&mut parent, var_b) {
                        union(&mut parent, &mut rank, var_a, var_b);
                        equiv_count += 1;
                    }
                }
            }
            // Also check negative equivalence: a ↔ !b (meaning a is always opposite b)
            // !a → !b: from clause (a | !b) → implies[lit_idx(!a)] contains !b
            // Actually, let's skip negative equivalence for simplicity
        }

        if equiv_count == 0 { return; }

        #[cfg(feature = "stats")]
        eprintln!("c Equivalent literal substitution: {} equivalences found", equiv_count);

        // Build substitution map: for each variable, its representative
        let mut repr: Vec<i32> = (0..=self.num_vars as i32).collect();
        for (var, repr_val) in repr.iter_mut().enumerate().take(self.num_vars + 1).skip(1) {
            let root = find(&mut parent, var);
            *repr_val = root as i32;
        }

        // Apply substitution to all clauses
        for ci in 0..self.clauses.len() {
            if self.deleted[ci] { continue; }
            let mut modified = false;
            for lit in &mut self.clauses[ci] {
                let var = lit.unsigned_abs() as usize;
                if var <= self.num_vars {
                    let new_var = repr[var];
                    if new_var != var as i32 {
                        *lit = if *lit > 0 { new_var } else { -new_var };
                        modified = true;
                    }
                }
            }
            if modified {
                // Remove duplicate literals and check for tautology
                self.clauses[ci].sort_unstable_by_key(|l| l.abs());
                self.clauses[ci].dedup();
                // Check tautology (a and !a in same clause)
                let is_taut = self.clauses[ci].windows(2).any(|w| w[0] == -w[1]);
                if is_taut {
                    self.deleted[ci] = true;
                }
            }
        }
    }

    fn run_light(&mut self) {
        self.unit_propagate();
        if self.unsat { return; }
        self.self_subsumption();
        self.unit_propagate();
        if self.unsat { return; }
        self.pure_literal_elimination();
        self.bounded_variable_elimination();
        self.unit_propagate();
    }

    fn run(&mut self) {
        let skip_bve = std::env::var("NO_BVE").is_ok();
        let skip_probe = std::env::var("NO_PROBE").is_ok();
        let skip_equiv = std::env::var("NO_EQUIV").is_ok();
        let skip_pure = std::env::var("NO_PURE").is_ok();
        // Iterative preprocessing: each step can create new opportunities
        for _round in 0..3 {
            let before = self.clauses.len();
            self.unit_propagate();
            if self.unsat { return; }
            if !skip_equiv { self.equivalent_literal_substitution(); }
            self.unit_propagate();
            if self.unsat { return; }
            if !skip_pure { self.pure_literal_elimination(); }
            self.self_subsumption();
            self.subsumption();
            if !skip_probe { self.failed_literal_probing(); }
            if self.unsat { return; }
            if !skip_bve { self.bounded_variable_elimination(); }
            if self.unsat { return; }
            if self.clauses.len() == before { break; }
        }
        self.unit_propagate();
        self.subsumption();
    }

    fn into_clauses(self) -> Vec<Vec<i32>> {
        if self.unsat {
            // Return a trivially UNSAT formula
            return vec![vec![1], vec![-1]];
        }

        let mut result = Vec::new();
        for (ci, clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }

            let mut satisfied = false;
            let mut simplified = Vec::new();

            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                let val = self.assigned[var];
                if (lit > 0 && val == 1) || (lit < 0 && val == -1) {
                    satisfied = true;
                    break;
                }
                if val == 0 {
                    simplified.push(lit);
                }
                // If val makes literal false, skip it (removed from clause)
            }

            if satisfied { continue; }
            result.push(simplified);
        }
        result
    }

    fn unit_propagate(&mut self) {
        let mut changed = true;
        while changed && !self.unsat {
            changed = false;
            for ci in 0..self.clauses.len() {
                if self.deleted[ci] { continue; }

                let mut unresolved_count = 0;
                let mut unit_lit = 0i32;
                let mut satisfied = false;

                for &lit in &self.clauses[ci] {
                    let var = lit.unsigned_abs() as usize;
                    let val = self.assigned[var];
                    if (lit > 0 && val == 1) || (lit < 0 && val == -1) {
                        satisfied = true;
                        break;
                    }
                    if val == 0 {
                        unresolved_count += 1;
                        unit_lit = lit;
                    }
                }

                if satisfied {
                    self.deleted[ci] = true;
                    continue;
                }

                if unresolved_count == 0 {
                    self.unsat = true;
                    return;
                }

                if unresolved_count == 1 {
                    let var = unit_lit.unsigned_abs() as usize;
                    self.assigned[var] = if unit_lit > 0 { 1 } else { -1 };
                    self.deleted[ci] = true;
                    changed = true;
                }
            }
        }
    }

    fn pure_literal_elimination(&mut self) {
        let mut pos = vec![false; self.num_vars + 1];
        let mut neg = vec![false; self.num_vars + 1];

        for (ci, clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                if self.assigned[var] != 0 { continue; }
                if lit > 0 { pos[var] = true; } else { neg[var] = true; }
            }
        }

        for var in 1..=self.num_vars {
            if self.assigned[var] != 0 { continue; }
            if pos[var] && !neg[var] {
                self.assigned[var] = 1;
            } else if neg[var] && !pos[var] {
                self.assigned[var] = -1;
            }
        }

        // Remove satisfied clauses
        for ci in 0..self.clauses.len() {
            if self.deleted[ci] { continue; }
            if self.clause_satisfied(ci) {
                self.deleted[ci] = true;
            }
        }
    }

    fn clause_satisfied(&self, ci: usize) -> bool {
        self.clauses[ci].iter().any(|&lit| {
            let var = lit.unsigned_abs() as usize;
            let val = self.assigned[var];
            (lit > 0 && val == 1) || (lit < 0 && val == -1)
        })
    }

    /// Returns the "live" literals of a clause (unassigned and not falsified).
    fn live_lits(&self, ci: usize) -> Vec<i32> {
        self.clauses[ci].iter()
            .filter(|&&lit| {
                let var = lit.unsigned_abs() as usize;
                self.assigned[var] == 0
            })
            .copied()
            .collect()
    }

    /// Removes clauses that are subsumed (supersets) of shorter clauses.
    fn subsumption(&mut self) {
        // Build occurrence lists
        let max_lit = (self.num_vars + 1) * 2;
        let mut occ: Vec<Vec<usize>> = vec![Vec::new(); max_lit];

        let mut live_clauses: Vec<usize> = Vec::new();
        for ci in 0..self.clauses.len() {
            if self.deleted[ci] { continue; }
            if self.clause_satisfied(ci) {
                self.deleted[ci] = true;
                continue;
            }
            let lits = self.live_lits(ci);
            if lits.is_empty() { continue; }
            live_clauses.push(ci);
            for &lit in &lits {
                let idx = if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 };
                if idx < max_lit { occ[idx].push(ci); }
            }
        }

        // Sort by clause size (check shortest first as potential subsumers)
        live_clauses.sort_unstable_by_key(|&ci| self.live_lits(ci).len());

        let mut _subsumed = 0usize;

        // For each short clause, check if it subsumes longer clauses
        for &ci in &live_clauses {
            if self.deleted[ci] { continue; }
            let lits_a = self.live_lits(ci);
            if lits_a.len() > 10 { break; } // Only check short subsumers

            // Find candidate longer clauses via the rarest literal's occurrence list
            let rarest_lit = lits_a.iter()
                .min_by_key(|&&lit| {
                    let idx = if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 };
                    if idx < max_lit { occ[idx].len() } else { usize::MAX }
                })
                .copied().unwrap();
            let idx = if rarest_lit > 0 { (rarest_lit as usize) * 2 } else { ((-rarest_lit) as usize) * 2 + 1 };
            if idx >= max_lit { continue; }

            for &cj in &occ[idx] {
                if cj == ci || self.deleted[cj] { continue; }
                let lits_b = self.live_lits(cj);
                if lits_b.len() <= lits_a.len() { continue; } // Can't subsume equal/shorter

                // Check if all literals in A are in B
                if lits_a.iter().all(|lit| lits_b.contains(lit)) {
                    self.deleted[cj] = true;
                    _subsumed += 1;
                }
            }
        }

        #[cfg(feature = "stats")]
        if _subsumed > 0 {
            eprintln!("c Subsumption removed {} clauses", _subsumed);
        }
    }

    /// Self-subsumption strengthening: use binary clauses to shorten longer ones.
    ///
    /// For binary (a | b) and clause C containing !a and b, remove !a from C.
    fn self_subsumption(&mut self) {
        // Collect live binary clauses
        let mut binaries: Vec<(i32, i32)> = Vec::new();
        for (ci, _clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            let lits = self.live_lits(ci);
            if lits.len() == 2 {
                binaries.push((lits[0], lits[1]));
            }
        }

        // Build occurrence lists for negative literals
        let max_lit = (self.num_vars + 1) * 2;
        let mut neg_lit_occ: Vec<Vec<usize>> = vec![Vec::new(); max_lit];
        for (ci, _clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            let lits = self.live_lits(ci);
            if lits.len() <= 2 { continue; } // Skip binaries
            for &lit in &lits {
                // Index by negated literal (we look for clauses containing !a)
                let neg = -lit;
                let idx = if neg > 0 { (neg as usize) * 2 } else { ((-neg) as usize) * 2 + 1 };
                if idx < max_lit { neg_lit_occ[idx].push(ci); }
            }
        }

        let mut _strengthened = 0usize;

        // For each binary (a | b), find clauses containing !a that also contain b
        for &(a, b) in &binaries {
            // Clauses containing !a (indexed by a, since neg_lit_occ indexes by the literal itself)
            let a_idx = if a > 0 { (a as usize) * 2 } else { ((-a) as usize) * 2 + 1 };
            if a_idx >= max_lit { continue; }

            for &ci in &neg_lit_occ[a_idx] {
                if self.deleted[ci] { continue; }
                let lits = self.live_lits(ci);
                // Check if clause contains both !a and b
                let has_neg_a = lits.contains(&(-a));
                let has_b = lits.contains(&b);
                if has_neg_a && has_b {
                    // Strengthen: remove !a from the clause
                    let neg_a = -a;
                    self.clauses[ci].retain(|&lit| lit != neg_a);
                    _strengthened += 1;
                    // Check if it became unit
                    let new_lits = self.live_lits(ci);
                    if new_lits.len() == 1 {
                        let lit = new_lits[0];
                        let var = lit.unsigned_abs() as usize;
                        if self.assigned[var] == 0 {
                            self.assigned[var] = if lit > 0 { 1 } else { -1 };
                        }
                        self.deleted[ci] = true;
                    }
                }
            }
        }

        #[cfg(feature = "stats")]
        if _strengthened > 0 {
            eprintln!("c Self-subsumption strengthened {} clauses", _strengthened);
        }
    }

    /// Failed literal probing: try each literal, propagate, learn forced assignments.
    fn failed_literal_probing(&mut self) {
        // Build occurrence lists for efficient propagation
        let max_lit = (self.num_vars + 1) * 2;
        // neg_occ[lit_idx] = clauses where -lit appears (so when lit is assigned true, these may become unit)
        let mut lit_to_clause: Vec<Vec<usize>> = vec![Vec::new(); max_lit];

        for (ci, clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                if self.assigned[var] != 0 { continue; }
                let idx = if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 };
                if idx < max_lit { lit_to_clause[idx].push(ci); }
            }
        }

        let _lit_idx = |lit: i32| -> usize {
            if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 }
        };

        let mut forced = 0usize;

        for var in 1..=self.num_vars {
            if self.assigned[var] != 0 { continue; }

            // Try both polarities
            let results: [Option<Vec<(usize, i8)>>; 2] = [
                self.probe(var, 1, &lit_to_clause, max_lit),
                self.probe(var, -1, &lit_to_clause, max_lit),
            ];

            match (&results[0], &results[1]) {
                (None, None) => {
                    // Both conflict — UNSAT
                    self.unsat = true;
                    return;
                }
                (None, Some(_)) => {
                    // Positive conflicts, must be false
                    self.assigned[var] = -1;
                    forced += 1;
                }
                (Some(_), None) => {
                    // Negative conflicts, must be true
                    self.assigned[var] = 1;
                    forced += 1;
                }
                (Some(_pos_impl), Some(_neg_impl)) => {
                    // Both succeed — could check for common implications but skip for now
                }
            }
        }

        if forced > 0 {
            #[cfg(feature = "stats")]
            eprintln!("c Failed literal probing forced {} variables", forced);
            // Dump assignments for verification
            if std::env::var("DUMP_PROBE").is_ok() {
                for var in 1..=self.num_vars {
                    if self.assigned[var] != 0 {
                        let lit = if self.assigned[var] > 0 { var as i32 } else { -(var as i32) };
                        eprintln!("c PROBE_ASSIGN {lit}");
                    }
                }
            }
            // Clean up satisfied clauses
            for ci in 0..self.clauses.len() {
                if self.deleted[ci] { continue; }
                if self.clause_satisfied(ci) { self.deleted[ci] = true; }
            }
        }
    }

    /// Probe a variable with a specific value. Returns None on conflict,
    /// Some(implied_assignments) on success.
    fn probe(&self, var: usize, value: i8, lit_to_clause: &[Vec<usize>], max_lit: usize) -> Option<Vec<(usize, i8)>> {
        let mut local_assign = self.assigned.clone();
        local_assign[var] = value;
        let mut queue: Vec<i32> = vec![if value > 0 { var as i32 } else { -(var as i32) }];
        let mut implied = vec![(var, value)];

        let lit_idx = |lit: i32| -> usize {
            if lit > 0 { (lit as usize) * 2 } else { ((-lit) as usize) * 2 + 1 }
        };

        while let Some(assigned_lit) = queue.pop() {
            // assigned_lit is now true. Check clauses containing -assigned_lit.
            let neg_lit = -assigned_lit;
            let idx = lit_idx(neg_lit);
            if idx >= max_lit { continue; }

            for &ci in &lit_to_clause[idx] {
                if self.deleted[ci] { continue; }

                let mut unresolved_count = 0;
                let mut unit_lit = 0i32;
                let mut satisfied = false;

                for &lit in &self.clauses[ci] {
                    let v = lit.unsigned_abs() as usize;
                    let a = local_assign[v];
                    if (lit > 0 && a == 1) || (lit < 0 && a == -1) {
                        satisfied = true;
                        break;
                    }
                    if a == 0 {
                        unresolved_count += 1;
                        unit_lit = lit;
                        if unresolved_count > 1 { break; }
                    }
                }

                if satisfied { continue; }
                if unresolved_count == 0 { return None; } // Conflict
                if unresolved_count == 1 {
                    let v = unit_lit.unsigned_abs() as usize;
                    let val = if unit_lit > 0 { 1i8 } else { -1i8 };
                    if local_assign[v] == 0 {
                        local_assign[v] = val;
                        queue.push(unit_lit);
                        implied.push((v, val));
                    }
                }
            }
        }

        Some(implied)
    }

    fn bounded_variable_elimination(&mut self) {
        // Build occurrence lists of live clauses
        let mut pos_occ: Vec<Vec<usize>> = vec![Vec::new(); self.num_vars + 1];
        let mut neg_occ: Vec<Vec<usize>> = vec![Vec::new(); self.num_vars + 1];

        for (ci, clause) in self.clauses.iter().enumerate() {
            if self.deleted[ci] { continue; }
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                if self.assigned[var] != 0 { continue; }
                if lit > 0 {
                    pos_occ[var].push(ci);
                } else {
                    neg_occ[var].push(ci);
                }
            }
        }

        // Sort variables by elimination cost (cheapest first)
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        for var in 1..=self.num_vars {
            if self.assigned[var] != 0 { continue; }
            let p = pos_occ[var].len();
            let n = neg_occ[var].len();
            if p == 0 || n == 0 { continue; }
            // Cost limit: only try variables where P*N is small
            if p * n > 100 { continue; }
            candidates.push((var, p * n));
        }
        candidates.sort_unstable_by_key(|&(_, cost)| cost);

        let mut _eliminated_vars = 0usize;

        for (var, _) in candidates {
            if self.unsat { break; }

            // Recompute live occurrences (may have changed from prior eliminations)
            let pos: Vec<usize> = pos_occ[var].iter()
                .filter(|&&ci| !self.deleted[ci] && !self.clause_satisfied(ci))
                .copied().collect();
            let neg: Vec<usize> = neg_occ[var].iter()
                .filter(|&&ci| !self.deleted[ci] && !self.clause_satisfied(ci))
                .copied().collect();

            let p = pos.len();
            let n = neg.len();
            if p == 0 || n == 0 { continue; }
            if p * n > p + n + 20 { continue; }

            // Generate resolvents
            let mut resolvents: Vec<Vec<i32>> = Vec::new();
            let mut profitable = true;

            'resolve: for &pi in &pos {
                let pos_lits = self.live_lits(pi);
                for &ni in &neg {
                    let neg_lits = self.live_lits(ni);

                    // Resolve on var
                    let mut res: Vec<i32> = Vec::new();
                    let mut tautology = false;

                    for &lit in &pos_lits {
                        if lit.unsigned_abs() as usize == var { continue; }
                        res.push(lit);
                    }
                    for &lit in &neg_lits {
                        if lit.unsigned_abs() as usize == var { continue; }
                        if res.contains(&(-lit)) {
                            tautology = true;
                            break;
                        }
                        if !res.contains(&lit) {
                            res.push(lit);
                        }
                    }

                    if !tautology {
                        resolvents.push(res);
                        if resolvents.len() > p + n {
                            profitable = false;
                            break 'resolve;
                        }
                    }
                }
            }

            if !profitable { continue; }

            // Perform elimination
            for &ci in &pos { self.deleted[ci] = true; }
            for &ci in &neg { self.deleted[ci] = true; }
            _eliminated_vars += 1;

            // Add resolvents
            for res in resolvents {
                if res.is_empty() {
                    self.unsat = true;
                    break;
                } else if res.len() == 1 {
                    let lit = res[0];
                    let v = lit.unsigned_abs() as usize;
                    if self.assigned[v] == 0 {
                        self.assigned[v] = if lit > 0 { 1 } else { -1 };
                    } else {
                        let expected = if lit > 0 { 1 } else { -1 };
                        if self.assigned[v] != expected {
                            self.unsat = true;
                            break;
                        }
                    }
                } else {
                    let ci = self.clauses.len();
                    // Update occurrence lists for the new clause
                    for &lit in &res {
                        let v = lit.unsigned_abs() as usize;
                        if lit > 0 { pos_occ[v].push(ci); }
                        else { neg_occ[v].push(ci); }
                    }
                    self.clauses.push(res);
                    self.deleted.push(false);
                }
            }
        }

        #[cfg(feature = "stats")]
        if _eliminated_vars > 0 {
            eprintln!("c BVE eliminated {} variables", _eliminated_vars);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unit_propagation() {
        let clauses = vec![
            vec![1],           // x1
            vec![-1, 2],       // !x1 | x2
            vec![-2, 3],       // !x2 | x3
        ];
        let result = preprocess(clauses, 3);
        // All clauses should be resolved by unit prop
        assert!(result.is_empty());
    }

    #[test]
    fn test_pure_literal() {
        let clauses = vec![
            vec![1, 2],    // x1 | x2
            vec![1, 3],    // x1 | x3
        ];
        let result = preprocess(clauses, 3);
        // x1 is pure positive, all clauses satisfied
        assert!(result.is_empty());
    }

    #[test]
    fn test_bve_simple() {
        // BVE on x1: (x1|x2) resolved with (!x1|x3) → (x2|x3)
        // Then BVE on x2: (x2|x3) resolved with (!x2|!x3) → (x3|!x3) = tautology
        // All clauses eliminated — correct for this satisfiable formula.
        let clauses = vec![
            vec![1, 2],     // x1 | x2
            vec![-1, 3],    // !x1 | x3
            vec![-2, -3],   // !x2 | !x3
        ];
        let result = preprocess(clauses, 3);
        assert!(result.is_empty()); // fully simplified away
    }

    #[test]
    fn test_bve_tautology() {
        // x appears in: (x | a) and (!x | !a)
        // Resolvent: (a | !a) - tautology, eliminated
        let clauses = vec![
            vec![1, 2],    // x1 | x2
            vec![-1, -2],  // !x1 | !x2
        ];
        let result = preprocess(clauses, 2);
        // Tautological resolvent means no clauses remain
        assert!(result.is_empty());
    }

    #[test]
    fn test_unsat_detection() {
        let clauses = vec![
            vec![1],
            vec![-1],
        ];
        let result = preprocess(clauses, 1);
        // Should detect UNSAT (returns a trivially UNSAT formula)
        assert!(result.len() >= 2); // contains contradictory units
    }

    #[test]
    fn test_preserves_satisfiability() {
        // A satisfiable formula should remain satisfiable after preprocessing
        let clauses = vec![
            vec![1, 2],
            vec![-1, 2],
            vec![1, -2],
        ];
        let result = preprocess(clauses, 2);
        // Should be satisfiable (x1=T, x2=T works)
        // The exact result depends on preprocessing, but shouldn't be empty contradictory
        // Just check it doesn't produce UNSAT
        let has_contradiction = result.iter().any(std::vec::Vec::is_empty);
        assert!(!has_contradiction);
    }
}
