use super::*;

impl CDCLSolver {
    /// Backtracks to the given decision level.
    ///
    /// Undoes all assignments made at levels higher than `level`.
    /// Level-0 assignments are never undone.
    pub(super) fn backtrack(&mut self, level: i32) {
        // For level 0, we keep all level-0 assignments
        // trail_lim[0] marks where level 1 starts (if any decisions were made)
        // If trail_lim is empty, all current assignments are level 0
        let target = if level == 0 {
            // Keep all level-0 assignments
            self.trail_lim.first().copied().unwrap_or(self.trail.len())
        } else {
            *self.trail_lim.get(level as usize).unwrap_or(&0)
        };

        while self.trail.len() > target {
            let lit = self.trail.pop().unwrap();
            let var = lit.unsigned_abs() as usize;
            self.unassign(var);
        }
        self.trail_lim.truncate(level as usize);
        self.decision_level = level;
        self.qhead = self.trail.len();
    }
}
