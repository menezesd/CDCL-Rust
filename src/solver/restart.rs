use super::*;

impl CDCLSolver {
    /// Computes the i-th element of the Luby sequence (0-indexed).
    ///
    /// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    /// It has theoretical optimality guarantees for restart strategies.
    pub(super) fn luby(i: u32) -> u32 {
        let mut size = 1u32;
        let mut seq = 1u32;

        // Find the smallest complete binary tree containing index i
        while size <= i {
            size = 2 * size + 1;
            seq *= 2;
        }

        // Navigate to find the value
        while size - 1 != i {
            size /= 2;
            if i >= size {
                // Recurse into right subtree
                return Self::luby(i - size);
            }
            seq /= 2;
        }

        seq
    }

    /// Performs a restart by backtracking to decision level 0.
    ///
    /// Learned clauses are kept to guide future search.
    pub(super) fn restart(&mut self) {
        self.backtrack(0);
        self.restarts += 1;
        self.last_restart_conflicts = self.conflicts;

        // Update Luby schedule (used as fallback before Glucose kicks in)
        self.luby_index += 1;
        self.conflicts_until_restart = self.conflicts + self.luby_unit * Self::luby(self.luby_index) as u64;
    }

    /// Records the LBD of a learned clause for restart decision.
    pub(super) fn record_lbd(&mut self, lbd: u32) {
        self.lbd_sum += lbd as f64;
        self.recent_lbds[self.recent_lbd_idx] = lbd;
        self.recent_lbd_idx += 1;
        if self.recent_lbd_idx >= self.recent_lbds.len() {
            self.recent_lbd_idx = 0;
            self.recent_lbd_full = true;
        }
    }

    /// Glucose-style restart: restart when recent learned clause quality degrades.
    ///
    /// Uses the Glucose formula: restart if `recent_avg_lbd * K > global_avg_lbd`
    /// where K = 0.8. This triggers when recent LBDs are 25%+ worse than average,
    /// indicating the solver is in a "bad" part of the search.
    #[inline]
    pub(super) fn should_restart(&self) -> bool {
        // Minimum interval between restarts
        let since_restart = self.conflicts - self.last_restart_conflicts;
        if since_restart < 30 {
            return false;
        }

        if !self.recent_lbd_full || self.conflicts < 100 {
            return self.conflicts >= self.conflicts_until_restart;
        }

        let global_avg = self.lbd_sum / self.conflicts as f64;
        let recent_sum: u32 = self.recent_lbds.iter().sum();
        let recent_avg = recent_sum as f64 / self.recent_lbds.len() as f64;

        // Glucose: recent_avg * K > global_avg. K=0.9 tuned for VarHeap
        recent_avg * 0.9 > global_avg
    }
}
