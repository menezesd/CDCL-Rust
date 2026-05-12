use super::*;

impl CDCLSolver {
    /// Analyzes a conflict to learn a new clause.
    ///
    /// Uses the first-UIP (Unique Implication Point) scheme:
    /// 1. Start with the conflict clause
    /// 2. Resolve backward through the implication graph
    /// 3. Stop at the first UIP (single literal from current decision level)
    /// 4. Return the learned clause and backtrack level
    pub(super) fn analyze_conflict(&mut self, conflict_clause: CRef) -> Result<(Vec<i32>, i32), SolverError> {
        let mut touched: Vec<usize> = Vec::new();
        let mut counter = 0;
        let mut learned: Vec<i32> = Vec::new();
        let mut p: Option<i32> = None;
        let mut resolve_cr = conflict_clause;
        let mut trail_idx = self.trail.len();

        loop {
            // Bump clause activity — this clause participated in conflict analysis
            if self.arena.is_learnt(resolve_cr) {
                self.arena.bump_activity(resolve_cr, self.clause_act_inc);
            }

            let clause_len = self.arena.len(resolve_cr);
            for k in 0..clause_len {
                let lit = self.arena.lits(resolve_cr)[k];
                let var = lit.unsigned_abs() as usize;

                if Some(lit) == p || Some(-lit) == p {
                    continue;
                }

                if !self.seen[var] {
                    self.seen[var] = true;
                    touched.push(var);
                    let a = &self.assignments[var];
                    if a.decision_level < 0 {
                        for &v in &touched { self.seen[v] = false; }
                        return Err(SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Variable in conflict clause is not assigned".to_string(),
                        });
                    }
                    if a.decision_level == self.decision_level {
                        counter += 1;
                    } else if a.decision_level > 0 {
                        learned.push(lit);
                        self.bump_activity(var);
                    }
                }
            }

            loop {
                if trail_idx == 0 {
                    for &v in &touched { self.seen[v] = false; }
                    return Err(SolverError::InternalError(
                        "Trail exhausted during conflict analysis".to_string()
                    ));
                }
                trail_idx -= 1;
                let lit = self.trail[trail_idx];
                let var = lit.unsigned_abs() as usize;
                if self.seen[var] {
                    self.seen[var] = false;
                    p = Some(lit);
                    counter -= 1;

                    if counter == 0 {
                        learned.push(-lit);
                        let last = learned.len() - 1;
                        learned.swap(0, last);

                        self.minimize_clause(&mut learned);

                        let mut bt_level = 0;
                        if learned.len() > 1 {
                            let mut max_idx = 1;
                            for i in 2..learned.len() {
                                let lvl = self.assignments[learned[i].unsigned_abs() as usize].decision_level;
                                let max_lvl = self.assignments[learned[max_idx].unsigned_abs() as usize].decision_level;
                                if lvl > max_lvl {
                                    max_idx = i;
                                }
                            }
                            learned.swap(1, max_idx);
                            bt_level = self.assignments[learned[1].unsigned_abs() as usize].decision_level;
                        }

                        for &lit in &learned {
                            self.bump_activity(lit.unsigned_abs() as usize);
                        }

                        for &v in &touched { self.seen[v] = false; }
                        return Ok((learned, bt_level));
                    }

                    let a = &self.assignments[var];
                    if a.decision_level < 0 {
                        for &v in &touched { self.seen[v] = false; }
                        return Err(SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Variable on trail is not assigned".to_string(),
                        });
                    }

                    if a.antecedent == CREF_UNDEF {
                        for &v in &touched { self.seen[v] = false; }
                        return Err(SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Decision variable encountered during conflict analysis with counter > 0".to_string(),
                        });
                    } else {
                        resolve_cr = a.antecedent;
                        break;
                    }
                }
            }
        }
    }

    /// Minimizes a learned clause by removing redundant literals.
    pub(super) fn minimize_clause(&self, learned: &mut Vec<i32>) {
        if learned.len() <= 1 {
            return;
        }

        let mut in_clause = vec![false; self.num_vars as usize + 1];
        for &lit in learned.iter() {
            in_clause[lit.unsigned_abs() as usize] = true;
        }

        let mut j = 1;
        for i in 1..learned.len() {
            let lit = learned[i];
            let var = lit.unsigned_abs() as usize;
            if self.lit_redundant(var, &in_clause) {
                in_clause[var] = false;
            } else {
                learned[j] = lit;
                j += 1;
            }
        }
        learned.truncate(j);
    }

    /// Checks if a variable is redundant via recursive antecedent analysis.
    pub(super) fn lit_redundant(&self, var: usize, in_clause: &[bool]) -> bool {
        let mut stack: Vec<usize> = vec![var];
        let mut visited: Vec<usize> = Vec::new();

        while let Some(v) = stack.pop() {
            let a = &self.assignments[v];
            if a.antecedent == CREF_UNDEF {
                return false; // decision variable — not redundant
            }

            for &lit in self.arena.lits(a.antecedent) {
                let u = lit.unsigned_abs() as usize;
                if u == v { continue; }
                if in_clause[u] { continue; }
                let dl = self.assignments[u].decision_level;
                if dl <= 0 { continue; }

                if visited.contains(&u) { continue; }

                if self.assignments[u].antecedent == CREF_UNDEF {
                    return false;
                }

                visited.push(u);
                stack.push(u);
            }
        }

        true
    }

    /// Bump activity for a variable and update heap position.
    pub(super) fn bump_activity(&mut self, var: usize) {
        self.var_heap.activity[var] += self.activity_inc;
        self.var_heap.decrease(var as i32);
    }

    /// Decays all variable activities and clause activities.
    pub(super) fn decay_activities(&mut self) {
        self.activity_inc *= 1.0 / 0.95;
        if self.activity_inc > 1e100 {
            for i in 1..=self.num_vars as usize {
                self.var_heap.activity[i] *= 1e-100;
            }
            self.activity_inc *= 1e-100;
            self.var_heap.build_heap();
        }

        // Clause activity decay
        self.clause_act_inc *= 1.0 / 0.999_f32;
        if self.clause_act_inc > 1e20 {
            for &cr in &self.clause_refs[self.first_learned_idx..] {
                if !self.arena.is_deleted(cr) && self.arena.is_learnt(cr) {
                    let old = self.arena.activity(cr);
                    self.arena.set_activity(cr, old * 1e-20);
                }
            }
            self.clause_act_inc *= 1e-20;
        }
    }
}
