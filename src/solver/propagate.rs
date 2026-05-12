use super::*;

impl CDCLSolver {
    /// Converts a literal to its watch list index.
    ///
    /// Positive literals map to even indices, negative to odd.
    #[inline]
    pub(super) fn lit_to_watch_idx(lit: i32, _num_vars: i32) -> usize {
        // Branchless: positive → var*2, negative → var*2+1
        let var = lit.unsigned_abs();
        ((var * 2) + (lit < 0) as u32) as usize
    }

    /// Gets the current value of a literal.
    ///
    /// Returns 1 if the literal is satisfied, -1 if falsified, 0 if unassigned.
    #[inline]
    pub(super) fn lit_value(&self, lit: i32) -> i8 {
        let var = lit.unsigned_abs() as usize;
        let val = self.values[var];
        if lit < 0 { -val } else { val }
    }

    /// Assigns a value to a literal.
    ///
    /// Records the assignment on the trail, adds it to the propagation queue,
    /// and saves the phase for future branching decisions.
    pub(super) fn assign(&mut self, lit: i32, antecedent: Option<CRef>) {
        let var = lit.unsigned_abs() as usize;
        let is_positive = lit > 0;
        self.values[var] = if is_positive { 1 } else { -1 };
        self.assignments[var] = Assignment {
            decision_level: self.decision_level,
            antecedent: antecedent.unwrap_or(CREF_UNDEF),
        };
        self.trail.push(lit);
        self.saved_phase[var] = is_positive;
    }

    /// Unassigns a variable.
    ///
    /// Clears the value and assignment info, and re-adds to the variable heap.
    pub(super) fn unassign(&mut self, var: usize) {
        self.values[var] = 0;
        self.assignments[var] = Assignment::UNASSIGNED;
        self.var_heap.insert(var as i32);
    }

    /// Performs Boolean Constraint Propagation (BCP).
    ///
    /// Uses the two-watched literal scheme for efficient propagation.
    /// When a watched literal becomes false, the clause either finds a
    /// new watch or becomes unit (triggering propagation) or conflicting.
    ///
    /// # Returns
    ///
    /// - `None` if propagation completed without conflict
    /// - `Some(cr)` if a conflict was detected in that clause
    ///
    /// MiniSAT-style propagation with in-place watch list compaction.
    /// When a watcher is removed (clause found a new watch), the slot is
    /// not copied to the output, avoiding swap_remove overhead.
    pub(super) fn propagate(&mut self) -> Option<CRef> {
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;

            // ---- Phase 1: Binary implication graph (tight loop, no watch overhead) ----
            let big_idx = Self::lit_to_watch_idx(lit, self.num_vars);
            // Iterate by index to avoid borrow issues with self.assign
            let n_bin = self.bin_implies[big_idx].len();
            for bi in 0..n_bin {
                let (implied, cr) = self.bin_implies[big_idx][bi];
                let val = self.lit_value(implied);
                if val == -1 {
                    // Conflict in binary clause
                    self.qhead = self.trail.len();
                    return Some(cr);
                }
                if val == 0 {
                    self.assign(implied, Some(cr));
                }
                // val == 1: already satisfied, skip
            }

            // ---- Phase 2: Long clauses via watched literals ----
            let false_lit = -lit;
            let watch_idx = Self::lit_to_watch_idx(false_lit, self.num_vars);

            let mut i = 0;
            let mut j = 0;
            while i < self.watches[watch_idx].len() {
                let watcher = self.watches[watch_idx][i];
                let cr = watcher.clause_idx();

                // Skip deleted clauses
                if self.arena.is_deleted(cr) {
                    i += 1;
                    continue;
                }

                // Blocking literal — avoid touching the clause
                if self.lit_value(watcher.blocker) == 1 {
                    self.watches[watch_idx][j] = watcher;
                    j += 1; i += 1;
                    continue;
                }

                // Access clause: swap false_lit to position 1
                {
                    let lits = self.arena.lits_mut(cr);
                    if lits[0] == false_lit {
                        lits.swap(0, 1);
                    }
                }
                let first = self.arena.lits(cr)[0];
                i += 1;

                // If first watch is true, clause is satisfied
                if first != watcher.blocker && self.lit_value(first) == 1 {
                    self.watches[watch_idx][j] = Watcher::long(cr, first);
                    j += 1;
                    continue;
                }

                // Search for a new watch literal
                let clen = self.arena.len(cr);
                let mut found_new = false;
                for k in 2..clen {
                    if self.lit_value(self.arena.lits(cr)[k]) != -1 {
                        self.arena.lits_mut(cr).swap(1, k);
                        let new_lit = self.arena.lits(cr)[1];
                        let nw = Self::lit_to_watch_idx(new_lit, self.num_vars);
                        self.watches[nw].push(Watcher::long(cr, first));
                        found_new = true;
                        break;
                    }
                }
                if found_new {
                    continue;
                }

                // No new watch: clause is unit or conflict
                let w = Watcher::long(cr, first);
                self.watches[watch_idx][j] = w;
                j += 1;

                if self.lit_value(first) == -1 {
                    // Conflict — copy remaining long watches
                    while i < self.watches[watch_idx].len() {
                        self.watches[watch_idx][j] = self.watches[watch_idx][i];
                        j += 1; i += 1;
                    }
                    self.watches[watch_idx].truncate(j);
                    self.qhead = self.trail.len();
                    return Some(cr);
                } else {
                    self.assign(first, Some(cr));
                }
            }
            self.watches[watch_idx].truncate(j);
        }

        None
    }
}
