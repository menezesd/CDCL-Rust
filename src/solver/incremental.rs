use super::*;

impl CDCLSolver {
    /// Creates an empty solver for incremental clause addition.
    ///
    /// Use `add_raw_clause()` to add clauses, then call `solve()`.
    /// After `solve()` returns, add more clauses and call `solve()` again.
    pub fn new_incremental(num_vars: i32) -> Self {
        let num_lits = (num_vars as usize + 1) * 2;

        let activity = vec![0.0; num_vars as usize + 1];
        let mut var_heap = VarHeap::new(num_vars as usize);
        var_heap.set_activity(&activity);
        for var in 1..=num_vars as usize {
            var_heap.insert(var as i32);
        }

        CDCLSolver {
            arena: ClauseArena::new(),
            clause_refs: Vec::new(),
            num_vars,
            values: vec![0; num_vars as usize + 1],
            assignments: vec![Assignment::UNASSIGNED; num_vars as usize + 1],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            activity_inc: 1.0,
            watches: vec![Vec::new(); num_lits],
            bin_implies: vec![Vec::new(); num_lits],
            qhead: 0,
            seen: vec![false; num_vars as usize + 1],
            var_heap,
            initial_conflict: false,
            saved_phase: vec![true; num_vars as usize + 1],
            conflicts: 0,
            conflicts_until_restart: 100,
            luby_index: 0,
            luby_unit: 100,
            lbd_sum: 0.0,
            last_restart_conflicts: 0,
            recent_lbds: vec![0; 50],
            recent_lbd_idx: 0,
            recent_lbd_full: false,
            first_learned_idx: 0,
            num_learned_alive: 0,
            max_learned: 2000,
            next_inprocess: u64::MAX,
            rng_state: 91648253,
            random_var_freq: 0.02,
            decisions: 0,
            propagations: 0,
            restarts: 0,
            reductions: 0,
            drat: crate::drat::DratLogger::disabled(),
            clause_act_inc: 1.0,
        }
    }

    /// Adds a clause specified as signed literals for incremental solving.
    pub fn add_raw_clause(&mut self, lits: &[i32]) {
        if lits.is_empty() {
            self.initial_conflict = true;
            return;
        }

        // Grow num_vars if needed
        for &lit in lits {
            let var = lit.unsigned_abs() as i32;
            if var > self.num_vars {
                let old = self.num_vars as usize;
                self.num_vars = var;
                let new_size = var as usize + 1;
                self.values.resize(new_size, 0);
                self.assignments.resize(new_size, Assignment::UNASSIGNED);
                self.saved_phase.resize(new_size, true);
                self.seen.resize(new_size, false);
                let num_lits = new_size * 2;
                self.watches.resize(num_lits, Vec::new());
                self.bin_implies.resize(num_lits, Vec::new());
                // Grow heap activity and insert new vars
                while self.var_heap.activity.len() < new_size {
                    self.var_heap.activity.push(0.0);
                }
                for v in (old + 1)..new_size {
                    self.var_heap.insert(v as i32);
                }
            }
            // Bump initial activity
            self.var_heap.activity[lit.unsigned_abs() as usize] += 1.0;
        }

        if lits.len() == 1 {
            let lit = lits[0];
            let var = lit.unsigned_abs() as usize;
            if self.values[var] == 0 {
                self.assign(lit, None);
            } else {
                let expected = if lit > 0 { 1 } else { -1 };
                if self.values[var] != expected {
                    self.initial_conflict = true;
                }
            }
            let cr = self.arena.alloc(&[lit], false, 0);
            self.clause_refs.push(cr);
            return;
        }

        // Reorder so unassigned/satisfied literals are watched
        let mut signed_lits: Vec<i32> = lits.to_vec();
        signed_lits.sort_by_key(|&lit| {
            let val = self.lit_value(lit);
            if val == 1 { 0 } else if val == 0 { 1 } else { 2 }
        });

        let cr = self.arena.alloc(&signed_lits, false, 0);
        self.clause_refs.push(cr);

        // Check current state
        let first_val = self.lit_value(signed_lits[0]);
        if first_val == -1 {
            self.initial_conflict = true;
        } else if first_val == 0 && signed_lits.len() >= 2 && self.lit_value(signed_lits[1]) == -1 {
            self.assign(signed_lits[0], Some(cr));
        }

        if signed_lits.len() == 2 {
            let idx_a = Self::lit_to_watch_idx(-signed_lits[0], self.num_vars);
            let idx_b = Self::lit_to_watch_idx(-signed_lits[1], self.num_vars);
            self.bin_implies[idx_a].push((signed_lits[1], cr));
            self.bin_implies[idx_b].push((signed_lits[0], cr));
        } else if signed_lits.len() > 2 {
            let w1 = Self::lit_to_watch_idx(signed_lits[0], self.num_vars);
            let w2 = Self::lit_to_watch_idx(signed_lits[1], self.num_vars);
            self.watches[w1].push(Watcher::long(cr, signed_lits[1]));
            self.watches[w2].push(Watcher::long(cr, signed_lits[0]));
        }
    }

    /// Prepares the solver for a new `solve()` call after adding clauses.
    pub fn prepare_for_resolve(&mut self) {
        if self.decision_level > 0 {
            self.backtrack(0);
        }
        self.first_learned_idx = self.clause_refs.len();
    }

    /// Tunes solver parameters for SAT-heavy workloads (CEGAR loops).
    pub fn tune_for_sat(&mut self) {
        self.max_learned = self.first_learned_idx / 2 + 10000;
        self.luby_unit = 512;

        let mut pos = vec![0u32; self.num_vars as usize + 1];
        let mut neg = vec![0u32; self.num_vars as usize + 1];
        for &cr in &self.clause_refs {
            if self.arena.is_deleted(cr) { continue; }
            for &lit in self.arena.lits(cr) {
                let var = lit.unsigned_abs() as usize;
                if lit > 0 { pos[var] += 1; } else { neg[var] += 1; }
            }
        }
        for v in 1..=self.num_vars as usize {
            self.saved_phase[v] = pos[v] >= neg[v];
        }
    }
}
