use super::*;

impl CDCLSolver {
    /// Runs inprocessing: extracts current formula, preprocesses, rebuilds.
    /// Must be called at decision level 0 (after a restart).
    pub(super) fn inprocess(&mut self) {
        assert_eq!(self.decision_level, 0);

        // Extract live clauses as raw literals, removing falsified literals
        let mut raw_clauses: Vec<Vec<i32>> = Vec::new();
        for &cr in &self.clause_refs {
            if self.arena.is_deleted(cr) { continue; }
            let clause = self.arena.lits(cr);
            if clause.len() <= 1 { continue; } // unit clauses are already propagated

            let mut simplified = Vec::new();
            let mut satisfied = false;
            for &lit in clause {
                let val = self.lit_value(lit);
                if val == 1 { satisfied = true; break; }
                if val == 0 { simplified.push(lit); }
            }
            if satisfied { continue; }
            if !simplified.is_empty() {
                raw_clauses.push(simplified);
            }
        }

        let before_clauses = raw_clauses.len();
        // Use lightweight preprocessing (skip probing — too slow during inprocessing)
        let simplified = preprocess::preprocess_light(raw_clauses, self.num_vars as usize);
        let after_clauses = simplified.len();

        // Only rebuild if preprocessing actually helped
        if after_clauses >= before_clauses {
            self.next_inprocess = self.conflicts + 100000;
            return;
        }

        #[cfg(feature = "stats")]
        eprintln!("c Inprocessing: {} -> {} clauses", before_clauses, after_clauses);

        // Rebuild clause database from simplified clauses
        // Keep level-0 trail assignments intact
        self.arena = ClauseArena::new();
        self.clause_refs.clear();

        let num_lits = (self.num_vars as usize + 1) * 2;
        self.watches = vec![Vec::new(); num_lits];

        for lits in &simplified {
            if lits.len() == 1 {
                // New unit from preprocessing — propagate at level 0
                let lit = lits[0];
                let var = lit.unsigned_abs() as usize;
                if self.values[var] == 0 {
                    self.assign(lit, None);
                }
                // Don't add to clause database (it's a fact now)
                continue;
            }
            let cr = self.arena.alloc(lits, false, 0);
            self.clause_refs.push(cr);
            if lits.len() == 2 {
                let w1 = Self::lit_to_watch_idx(lits[0], self.num_vars);
                let w2 = Self::lit_to_watch_idx(lits[1], self.num_vars);
                self.watches[w1].push(Watcher::binary(cr, lits[1]));
                self.watches[w2].push(Watcher::binary(cr, lits[0]));
            } else {
                let w1 = Self::lit_to_watch_idx(lits[0], self.num_vars);
                let w2 = Self::lit_to_watch_idx(lits[1], self.num_vars);
                self.watches[w1].push(Watcher::long(cr, lits[1]));
                self.watches[w2].push(Watcher::long(cr, lits[0]));
            }
        }

        self.first_learned_idx = self.clause_refs.len();
        self.num_learned_alive = 0;
        self.max_learned = (self.clause_refs.len() / 10).max(100) + 2000;

        // Schedule next inprocessing (with increasing intervals)
        self.next_inprocess = self.conflicts + 50000;
    }

    /// Vivification: shorten learned clauses by propagating literal negations.
    ///
    /// For each candidate learned clause C = (l1 ∨ l2 ∨ ... ∨ lk), try
    /// assuming ¬l1, ¬l2, ... in sequence. If propagation forces some lj
    /// in C to true, then that literal is implied and the clause can be
    /// shortened. If a conflict arises, the clause is subsumed by a shorter
    /// implied clause.
    ///
    /// Must be called at decision level 0.
    /// Runs vivification on the current clause database.
    /// Call at decision level 0 (e.g., after a restart or as part of inprocessing).
    pub fn vivify(&mut self) {
        assert_eq!(self.decision_level, 0);

        // Collect candidate learned clauses (long, non-glue)
        let mut candidates: Vec<CRef> = Vec::new();
        for &cr in &self.clause_refs[self.first_learned_idx..] {
            if self.arena.is_deleted(cr) { continue; }
            let len = self.arena.len(cr);
            if len <= 2 { continue; } // skip binary (already minimal)
            if self.arena.is_learnt(cr) && self.arena.lbd(cr) <= 2 { continue; } // skip glue
            candidates.push(cr);
        }

        // Limit work: vivify at most 500 clauses per round (less aggressive for SAT)
        let limit = candidates.len().min(500);
        let mut shortened = 0u32;
        let mut deleted = 0u32;

        for &cr in candidates.iter().take(limit) {
            if self.arena.is_deleted(cr) { continue; }

            // Copy clause literals (we may modify the clause)
            let lits: Vec<i32> = self.arena.lits(cr).to_vec();
            let orig_len = lits.len();

            // Try negating each literal in order
            let mut new_lits: Vec<i32> = Vec::new();
            let mut clause_subsumed = false;

            // Push a new decision level for probing
            self.decision_level += 1;
            self.trail_lim.push(self.trail.len());

            for (i, &lit) in lits.iter().enumerate() {
                let val = self.lit_value(lit);

                if val == 1 {
                    // Literal is already true at level 0 — clause is satisfied, delete it
                    clause_subsumed = true;
                    break;
                }
                if val == -1 {
                    // Literal is already false at level 0 — skip (effectively removed)
                    continue;
                }

                // Assume ¬lit and propagate
                self.assign(-lit, None);
                let conflict = self.propagate();

                if conflict.is_some() {
                    // Conflict: the remaining literals (already added to new_lits)
                    // form a sufficient clause. The current literal and all
                    // following ones are subsumed.
                    clause_subsumed = false; // we'll replace, not delete
                    break;
                }

                // Check if any remaining literal in C became true
                let mut implied = false;
                for &other_lit in &lits[i + 1..] {
                    if self.lit_value(other_lit) == 1 {
                        // other_lit is implied — add it and stop
                        new_lits.push(other_lit);
                        implied = true;
                        break;
                    }
                }
                if implied {
                    break;
                }

                // This literal wasn't helpful — keep it
                new_lits.push(lit);
            }

            // Undo all probing assignments
            self.backtrack(0);

            if clause_subsumed {
                self.arena.set_deleted(cr);
                if self.arena.is_learnt(cr) {
                    self.num_learned_alive -= 1;
                }
                deleted += 1;
                continue;
            }

            // If we shortened the clause, replace it
            if new_lits.len() < orig_len && !new_lits.is_empty() {
                shortened += 1;

                // Delete old clause
                self.arena.set_deleted(cr);
                if self.arena.is_learnt(cr) {
                    self.num_learned_alive -= 1;
                }

                if new_lits.len() == 1 {
                    // Became unit — propagate at level 0
                    let unit = new_lits[0];
                    let var = unit.unsigned_abs() as usize;
                    if self.values[var] == 0 {
                        self.assign(unit, None);
                        if self.propagate().is_some() {
                            // Conflict at level 0 — formula is UNSAT
                            return;
                        }
                    }
                } else {
                    // Allocate shortened clause
                    let learnt = self.arena.is_learnt(cr);
                    let lbd = if learnt {
                        self.arena.lbd(cr).min(new_lits.len() as u32)
                    } else {
                        0
                    };
                    let new_cr = self.arena.alloc(&new_lits, learnt, lbd);
                    self.clause_refs.push(new_cr);
                    if learnt {
                        self.num_learned_alive += 1;
                    }

                    // Set up watches/BIG for the new clause
                    if new_lits.len() == 2 {
                        let idx_a = Self::lit_to_watch_idx(-new_lits[0], self.num_vars);
                        let idx_b = Self::lit_to_watch_idx(-new_lits[1], self.num_vars);
                        self.bin_implies[idx_a].push((new_lits[1], new_cr));
                        self.bin_implies[idx_b].push((new_lits[0], new_cr));
                    } else {
                        let w1 = Self::lit_to_watch_idx(new_lits[0], self.num_vars);
                        let w2 = Self::lit_to_watch_idx(new_lits[1], self.num_vars);
                        self.watches[w1].push(Watcher::long(new_cr, new_lits[1]));
                        self.watches[w2].push(Watcher::long(new_cr, new_lits[0]));
                    }
                }
            }
        }

        #[cfg(feature = "stats")]
        if shortened > 0 || deleted > 0 {
            eprintln!("c Vivification: shortened {} clauses, deleted {} (of {} candidates)",
                shortened, deleted, limit);
        }
    }
}
