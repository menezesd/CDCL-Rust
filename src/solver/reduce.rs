use super::*;

impl CDCLSolver {
    /// Adds a learned clause to the solver.
    ///
    /// Sets up watches for the new clause and computes LBD.
    /// Returns the CRef of the new clause and its LBD.
    pub(super) fn add_learned_clause(&mut self, learned: Vec<i32>) -> (CRef, u32) {
        if learned.is_empty() {
            return (crate::clause_arena::CREF_UNDEF, 0);
        }

        // Compute LBD using seen buffer to avoid allocation
        let mut lbd = 0u32;
        let mut levels_touched = Vec::new();
        for &lit in &learned {
            let var = lit.unsigned_abs() as usize;
            {
                let dl = self.assignments[var].decision_level;
                if dl < 0 { continue; }
                let dl = dl as usize;
                // Reuse seen buffer (indexed by level) — safe because levels < num_vars
                if dl < self.seen.len() && !self.seen[dl] {
                    self.seen[dl] = true;
                    levels_touched.push(dl);
                    lbd += 1;
                }
            }
        }
        for &dl in &levels_touched { self.seen[dl] = false; }

        let cr = self.arena.alloc(&learned, true, lbd);
        self.clause_refs.push(cr);

        if learned.len() == 2 {
            // Binary learned clause: add to implication graph
            let idx_a = Self::lit_to_watch_idx(-learned[0], self.num_vars);
            let idx_b = Self::lit_to_watch_idx(-learned[1], self.num_vars);
            self.bin_implies[idx_a].push((learned[1], cr));
            self.bin_implies[idx_b].push((learned[0], cr));
        } else if learned.len() > 2 {
            let w1 = Self::lit_to_watch_idx(learned[0], self.num_vars);
            let w2 = Self::lit_to_watch_idx(learned[1], self.num_vars);
            self.watches[w1].push(Watcher::long(cr, learned[1]));
            self.watches[w2].push(Watcher::long(cr, learned[0]));
        }

        self.num_learned_alive += 1;
        (cr, lbd)
    }

    /// Reduces the learned clause database by deleting low-quality clauses.
    ///
    /// Keeps "glue" clauses (LBD <= 2) and clauses that are antecedents of
    /// current trail assignments. Removes roughly half of the remaining
    /// learned clauses, preferring those with higher LBD.
    pub(super) fn reduce_db(&mut self) {
        self.reductions += 1;
        // Build set of antecedent CRefs
        let mut antecedent_set: Vec<CRef> = Vec::new();
        for &lit in &self.trail {
            let var = lit.unsigned_abs() as usize;
            let a = &self.assignments[var];
            if a.antecedent != CREF_UNDEF {
                antecedent_set.push(a.antecedent);
            }
        }
        antecedent_set.sort_unstable();
        antecedent_set.dedup();

        // Collect candidate clause CRefs for deletion
        let mut candidates: Vec<(CRef, u32)> = Vec::new();
        for &cr in &self.clause_refs[self.first_learned_idx..] {
            if self.arena.is_deleted(cr) {
                continue;
            }
            if antecedent_set.binary_search(&cr).is_ok() {
                continue;
            }
            let lbd = self.arena.lbd(cr);
            // Never delete glue clauses (LBD <= 2) or unit learned clauses
            if lbd <= 2 || self.arena.len(cr) <= 1 {
                continue;
            }
            candidates.push((cr, lbd));
        }

        // Sort by quality: low activity and high LBD = worst (delete first)
        // MiniSAT: sort by activity ascending, delete bottom half
        candidates.sort_unstable_by(|a, b| {
            let act_a = self.arena.activity(a.0);
            let act_b = self.arena.activity(b.0);
            act_a.partial_cmp(&act_b).unwrap_or(std::cmp::Ordering::Equal)
                .then(b.1.cmp(&a.1))
        });

        // Delete the worst half (lowest activity)
        let to_delete = candidates.len() / 2;
        for &(cr, _) in candidates.iter().take(to_delete) {
            self.arena.set_deleted(cr);
            self.num_learned_alive -= 1;
        }

        // Increase threshold for next reduction
        self.max_learned = (self.max_learned + 300).min(self.first_learned_idx / 3 + 5000);

        // Remove deleted CRefs from clause_refs and rebuild watches if too fragmented
        let before_len = self.clause_refs.len();
        self.clause_refs.retain(|&cr| !self.arena.is_deleted(cr));
        let after_len = self.clause_refs.len();

        // Recompute first_learned_idx: find the first learnt clause in clause_refs
        self.first_learned_idx = self.clause_refs.iter()
            .position(|&cr| self.arena.is_learnt(cr))
            .unwrap_or(self.clause_refs.len());

        // Rebuild watches if we removed a significant fraction
        if before_len > after_len * 2 {
            self.rebuild_watches();
        }

        // Arena GC: compact when >30% of arena is wasted
        let total_words = self.arena.total_words();
        if total_words > 0 && self.arena.wasted() * 100 / total_words > 30 {
            self.gc_arena();
        }
    }

    /// Compacts the clause arena by reallocating all live clauses into a new
    /// arena, updating all CRef references (clause_refs, watches, antecedents).
    fn gc_arena(&mut self) {
        let mut new_arena = ClauseArena::with_capacity(
            self.arena.total_words() - self.arena.wasted()
        );
        let mut remap: std::collections::HashMap<CRef, CRef> = std::collections::HashMap::new();

        // Reallocate all live clauses
        for &old_cr in &self.clause_refs {
            if self.arena.is_deleted(old_cr) { continue; }
            let lits = self.arena.lits(old_cr);
            let learnt = self.arena.is_learnt(old_cr);
            let lbd = if learnt { self.arena.lbd(old_cr) } else { 0 };
            let new_cr = new_arena.alloc(lits, learnt, lbd);
            if learnt {
                let act = self.arena.activity(old_cr);
                new_arena.set_activity(new_cr, act);
            }
            remap.insert(old_cr, new_cr);
        }

        // Update clause_refs
        self.clause_refs.retain(|cr| !self.arena.is_deleted(*cr));
        for cr in &mut self.clause_refs {
            *cr = remap[cr];
        }

        // Update antecedent references
        for var in 1..=self.num_vars as usize {
            let a = &mut self.assignments[var];
            if a.antecedent != CREF_UNDEF {
                if let Some(&new_cr) = remap.get(&a.antecedent) {
                    a.antecedent = new_cr;
                } else {
                    a.antecedent = CREF_UNDEF;
                }
            }
        }

        // Replace arena and rebuild watches
        self.arena = new_arena;
        self.rebuild_watches();

        // Recompute first_learned_idx
        self.first_learned_idx = self.clause_refs.iter()
            .position(|&cr| self.arena.is_learnt(cr))
            .unwrap_or(self.clause_refs.len());
    }

    /// Rebuilds all watch lists and binary implication graph from clause_refs.
    pub(super) fn rebuild_watches(&mut self) {
        let num_lits = (self.num_vars as usize + 1) * 2;
        self.watches = vec![Vec::new(); num_lits];
        self.bin_implies = vec![Vec::new(); num_lits];
        for &cr in &self.clause_refs {
            if self.arena.is_deleted(cr) { continue; }
            let lits = self.arena.lits(cr);
            if lits.len() == 2 {
                // Binary: add to implication graph
                let idx_a = Self::lit_to_watch_idx(-lits[0], self.num_vars);
                let idx_b = Self::lit_to_watch_idx(-lits[1], self.num_vars);
                self.bin_implies[idx_a].push((lits[1], cr));
                self.bin_implies[idx_b].push((lits[0], cr));
            } else if lits.len() > 2 {
                let w1 = Self::lit_to_watch_idx(lits[0], self.num_vars);
                let w2 = Self::lit_to_watch_idx(lits[1], self.num_vars);
                self.watches[w1].push(Watcher::long(cr, lits[1]));
                self.watches[w2].push(Watcher::long(cr, lits[0]));
            }
        }
    }
}
