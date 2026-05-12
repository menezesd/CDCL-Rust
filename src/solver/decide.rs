use super::*;

impl CDCLSolver {
    /// Selects the next branching literal using VSIDS and phase saving.
    ///
    /// Uses a binary heap to efficiently find the unassigned variable
    /// with the highest activity score, then uses the saved phase to
    /// determine the polarity.
    ///
    /// # Returns
    ///
    /// - `Some(lit)` - The literal to branch on (positive or negative)
    /// - `None` - All variables are assigned (SAT)
    pub(super) fn pick_branching_literal(&mut self) -> Option<i32> {
        self.decisions += 1;

        // Random decision with probability random_var_freq
        if self.random_var_freq > 0.0 && self.rand_float() < self.random_var_freq {
            let start = (self.rand_u32() % self.num_vars as u32) as usize + 1;
            for offset in 0..self.num_vars as usize {
                let v = (start + offset - 1) % self.num_vars as usize + 1;
                if self.values[v] == 0 {
                    let lit = if self.saved_phase[v] { v as i32 } else { -(v as i32) };
                    return Some(lit);
                }
            }
        }

        // VSIDS decision
        while let Some(var) = self.var_heap.remove_min() {
            let v = var as usize;
            if self.values[v] == 0 {
                let lit = if self.saved_phase[v] { var } else { -var };
                return Some(lit);
            }
        }
        None
    }

    /// Xorshift32 random number generator.
    #[inline]
    pub(super) fn rand_u32(&mut self) -> u32 {
        self.rng_state ^= self.rng_state << 13;
        self.rng_state ^= self.rng_state >> 17;
        self.rng_state ^= self.rng_state << 5;
        self.rng_state
    }

    /// Returns a random float in [0, 1).
    #[inline]
    pub(super) fn rand_float(&mut self) -> f64 {
        (self.rand_u32() as f64) / (u32::MAX as f64)
    }
}
