//! CDCL (Conflict-Driven Clause Learning) SAT solver implementation.
//!
//! This module implements a complete CDCL SAT solver with the following features:
//!
//! - **Two-watched literals**: Efficient unit propagation using the two-watched
//!   literal scheme, providing O(1) amortized propagation per assignment.
//!
//! - **First-UIP conflict analysis**: Learns powerful clauses by resolving
//!   conflicts backward to the first Unique Implication Point.
//!
//! - **Non-chronological backtracking**: Jumps directly to the relevant decision
//!   level based on the learned clause, avoiding redundant search.
//!
//! - **VSIDS variable selection**: Uses Variable State Independent Decaying Sum
//!   with a binary heap for O(log n) variable selection.
//!
//! # Example
//!
//! ```
//! use cdcl_sat::{CDCLSolver, Clause, Literal};
//!
//! // Create clauses for (x1 OR x2) AND (NOT x1 OR x3)
//! let clauses = vec![
//!     Clause::new(vec![Literal::positive(1), Literal::positive(2)]),
//!     Clause::new(vec![Literal::negative(1), Literal::positive(3)]),
//! ];
//!
//! let mut solver = CDCLSolver::new(clauses);
//! assert!(solver.solve().unwrap()); // SAT
//! ```

use std::collections::{BinaryHeap, VecDeque};
use std::cmp::Ordering;
use std::fmt;

use crate::Clause;

/// Errors that can occur during SAT solving.
///
/// These errors indicate internal invariant violations that should not
/// occur during normal operation. If encountered, they typically indicate
/// a bug in the solver implementation.
#[derive(Debug, Clone, PartialEq)]
pub enum SolverError {
    /// A decision variable was encountered during conflict analysis where
    /// a propagated variable was expected. This indicates corruption in
    /// the implication graph.
    InvalidConflictAnalysis {
        /// The variable that caused the error.
        variable: i32,
        /// Description of what went wrong.
        message: String,
    },

    /// An internal invariant was violated.
    InternalError(String),
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverError::InvalidConflictAnalysis { variable, message } => {
                write!(f, "Invalid conflict analysis at variable {}: {}", variable, message)
            }
            SolverError::InternalError(msg) => {
                write!(f, "Internal solver error: {}", msg)
            }
        }
    }
}

impl std::error::Error for SolverError {}

/// Tracks information about a variable assignment.
#[derive(Debug, Clone)]
struct Assignment {
    /// The decision level at which this assignment was made.
    decision_level: i32,
    /// The clause that caused this assignment (None for decisions).
    antecedent_clause: Option<usize>,
}

/// Entry in the variable activity heap for VSIDS.
///
/// Implements ordering such that higher activity variables come first.
#[derive(Debug, Clone)]
struct VarHeapEntry {
    var: i32,
    activity: f64,
}

impl PartialEq for VarHeapEntry {
    fn eq(&self, other: &Self) -> bool {
        self.var == other.var
    }
}

impl Eq for VarHeapEntry {}

impl PartialOrd for VarHeapEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarHeapEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher activity comes first (max-heap behavior)
        self.activity.partial_cmp(&other.activity).unwrap_or(Ordering::Equal)
    }
}

/// A CDCL SAT solver.
///
/// This solver implements the Conflict-Driven Clause Learning algorithm
/// with modern optimizations including two-watched literals, first-UIP
/// learning, non-chronological backtracking, VSIDS variable selection,
/// phase saving, and restarts.
pub struct CDCLSolver {
    /// All clauses (original and learned), stored as signed literals.
    clauses: Vec<Vec<i32>>,

    /// The number of variables in the formula.
    num_vars: i32,

    /// Current value of each variable: -1 (false), 0 (unassigned), 1 (true).
    /// Index 0 is unused; variables are 1-indexed.
    values: Vec<i8>,

    /// Assignment information for each variable.
    assignments: Vec<Option<Assignment>>,

    /// Trail of assignments in chronological order.
    trail: Vec<i32>,

    /// Indices into trail marking the start of each decision level.
    trail_lim: Vec<usize>,

    /// Current decision level.
    decision_level: i32,

    /// Activity score for each variable (VSIDS).
    var_activity: Vec<f64>,

    /// Activity increment (increases after each conflict).
    activity_inc: f64,

    /// Watch lists: for each literal, the clause indices watching it.
    watches: Vec<Vec<usize>>,

    /// Queue of literals to propagate.
    propagation_queue: VecDeque<i32>,

    /// Binary heap for variable selection (VSIDS).
    var_heap: BinaryHeap<VarHeapEntry>,

    /// Tracks whether a variable is in the heap.
    in_heap: Vec<bool>,

    /// True if a conflict was detected during initialization.
    initial_conflict: bool,

    // ========================================================================
    // Phase Saving
    // ========================================================================

    /// Saved phase (polarity) for each variable.
    /// When branching, we use the last assigned value for better convergence.
    saved_phase: Vec<bool>,

    // ========================================================================
    // Restart Management
    // ========================================================================

    /// Total number of conflicts encountered.
    conflicts: u64,

    /// Number of conflicts until next restart.
    conflicts_until_restart: u64,

    /// Current index in the Luby sequence.
    luby_index: u32,

    /// Base unit for Luby restarts (number of conflicts).
    luby_unit: u64,
}

impl CDCLSolver {
    /// Creates a new solver for the given clauses.
    ///
    /// The solver initializes all data structures and performs initial
    /// unit propagation. Any unit clauses in the input are immediately
    /// assigned.
    ///
    /// # Arguments
    ///
    /// * `clauses` - The CNF clauses to solve
    ///
    /// # Example
    ///
    /// ```
    /// use cdcl_sat::{CDCLSolver, Clause, Literal};
    ///
    /// let clauses = vec![
    ///     Clause::new(vec![Literal::positive(1)]),
    ///     Clause::new(vec![Literal::negative(1), Literal::positive(2)]),
    /// ];
    /// let solver = CDCLSolver::new(clauses);
    /// ```
    pub fn new(clauses: Vec<Clause>) -> Self {
        // Find the maximum variable number
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

        // Convert clauses and set up watches
        for clause in &clauses {
            let signed_lits: Vec<i32> = clause.literals.iter()
                .map(|l| l.as_signed())
                .collect();

            if signed_lits.is_empty() {
                continue;
            }

            let clause_idx = solver_clauses.len();

            if signed_lits.len() >= 2 {
                // Watch the first two literals
                let w1 = Self::lit_to_watch_idx(signed_lits[0], num_vars);
                let w2 = Self::lit_to_watch_idx(signed_lits[1], num_vars);
                watches[w1].push(clause_idx);
                watches[w2].push(clause_idx);
            } else {
                // Unit clause - record for later assignment
                unit_clauses.push((signed_lits[0], clause_idx));
            }

            solver_clauses.push(signed_lits);
        }

        // Initialize variable activities based on occurrence count
        let mut var_activity = vec![0.0; num_vars as usize + 1];
        for clause in &solver_clauses {
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                var_activity[var] += 1.0;
            }
        }

        // Build the initial variable heap
        let mut var_heap = BinaryHeap::new();
        let in_heap = vec![true; num_vars as usize + 1];
        for var in 1..=num_vars as usize {
            var_heap.push(VarHeapEntry {
                var: var as i32,
                activity: var_activity[var],
            });
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
            var_heap,
            in_heap,
            initial_conflict: false,
            // Phase saving: default to true (positive polarity)
            saved_phase: vec![true; num_vars as usize + 1],
            // Restart management
            conflicts: 0,
            conflicts_until_restart: 100,  // First restart after 100 conflicts
            luby_index: 0,
            luby_unit: 100,
        };

        // Assign unit clauses at decision level 0
        for (lit, _clause_idx) in unit_clauses {
            let var = lit.unsigned_abs() as usize;
            if solver.values[var] == 0 {
                solver.assign(lit, None);
            } else {
                // Check for conflict with existing assignment
                let expected_val = if lit > 0 { 1 } else { -1 };
                if solver.values[var] != expected_val {
                    solver.initial_conflict = true;
                }
            }
        }

        solver
    }

    /// Converts a literal to its watch list index.
    ///
    /// Positive literals map to even indices, negative to odd.
    #[inline]
    fn lit_to_watch_idx(lit: i32, _num_vars: i32) -> usize {
        let var = lit.abs();
        if lit > 0 {
            (var * 2) as usize
        } else {
            (var * 2 + 1) as usize
        }
    }

    /// Gets the current value of a literal.
    ///
    /// Returns 1 if the literal is satisfied, -1 if falsified, 0 if unassigned.
    #[inline]
    fn lit_value(&self, lit: i32) -> i8 {
        let var = lit.unsigned_abs() as usize;
        let val = self.values[var];
        if lit < 0 { -val } else { val }
    }

    /// Assigns a value to a literal.
    ///
    /// Records the assignment on the trail, adds it to the propagation queue,
    /// and saves the phase for future branching decisions.
    fn assign(&mut self, lit: i32, antecedent: Option<usize>) {
        let var = lit.unsigned_abs() as usize;
        let is_positive = lit > 0;
        self.values[var] = if is_positive { 1 } else { -1 };
        self.assignments[var] = Some(Assignment {
            decision_level: self.decision_level,
            antecedent_clause: antecedent,
        });
        self.trail.push(lit);
        self.propagation_queue.push_back(lit);

        // Phase saving: remember the polarity we assigned
        self.saved_phase[var] = is_positive;

        // Remove from heap (mark as not in heap)
        self.in_heap[var] = false;
    }

    /// Unassigns a variable.
    ///
    /// Clears the value and assignment info, and re-adds to the variable heap.
    fn unassign(&mut self, var: usize) {
        self.values[var] = 0;
        self.assignments[var] = None;

        // Re-add to heap with current activity
        if !self.in_heap[var] {
            self.in_heap[var] = true;
            self.var_heap.push(VarHeapEntry {
                var: var as i32,
                activity: self.var_activity[var],
            });
        }
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
    /// - `Some(clause_idx)` if a conflict was detected in that clause
    fn propagate(&mut self) -> Option<usize> {
        while let Some(lit) = self.propagation_queue.pop_front() {
            // The literal `lit` is now true, so `-lit` is false.
            // We need to update clauses watching `-lit`.
            let false_lit = -lit;
            let watch_idx = Self::lit_to_watch_idx(false_lit, self.num_vars);

            let mut i = 0;
            while i < self.watches[watch_idx].len() {
                let clause_idx = self.watches[watch_idx][i];
                let clause = &self.clauses[clause_idx];

                // Ensure the false literal is at position 1
                if clause[0] == false_lit {
                    self.clauses[clause_idx].swap(0, 1);
                }
                let clause = &self.clauses[clause_idx];

                // If the other watched literal is true, clause is satisfied
                let other_lit = clause[0];
                if self.lit_value(other_lit) == 1 {
                    i += 1;
                    continue;
                }

                // Try to find a new literal to watch
                let mut found_new = false;
                for (j, &new_lit) in clause.iter().enumerate().skip(2) {
                    if self.lit_value(new_lit) != -1 {
                        // Found a non-false literal - make it the new watch
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

                // No new watch found - check if conflict or unit
                let other_val = self.lit_value(other_lit);
                if other_val == -1 {
                    // Both watched literals are false - conflict!
                    self.propagation_queue.clear();
                    return Some(clause_idx);
                } else if other_val == 0 {
                    // Other literal is unassigned - propagate it
                    self.assign(other_lit, Some(clause_idx));
                }

                i += 1;
            }
        }

        None
    }

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
    fn pick_branching_literal(&mut self) -> Option<i32> {
        // Pop entries until we find an unassigned variable
        while let Some(entry) = self.var_heap.pop() {
            let var = entry.var as usize;

            // Skip if already assigned or activity is stale
            if self.values[var] == 0 {
                // Check if the activity is current (entry might be stale)
                if (entry.activity - self.var_activity[var]).abs() < 1e-10 {
                    self.in_heap[var] = false;
                    // Use saved phase to determine polarity
                    let lit = if self.saved_phase[var] {
                        entry.var  // positive literal
                    } else {
                        -entry.var // negative literal
                    };
                    return Some(lit);
                } else {
                    // Stale entry - push updated one
                    self.var_heap.push(VarHeapEntry {
                        var: entry.var,
                        activity: self.var_activity[var],
                    });
                }
            }
        }

        None
    }

    /// Analyzes a conflict to learn a new clause.
    ///
    /// Uses the first-UIP (Unique Implication Point) scheme:
    /// 1. Start with the conflict clause
    /// 2. Resolve backward through the implication graph
    /// 3. Stop at the first UIP (single literal from current decision level)
    /// 4. Return the learned clause and backtrack level
    ///
    /// # Arguments
    ///
    /// * `conflict_clause` - Index of the clause that caused the conflict
    ///
    /// # Returns
    ///
    /// - `Ok((learned_clause, backtrack_level))` on success
    /// - `Err(SolverError)` if an internal invariant is violated
    fn analyze_conflict(&mut self, conflict_clause: usize) -> Result<(Vec<i32>, i32), SolverError> {
        let mut seen = vec![false; self.num_vars as usize + 1];
        let mut counter = 0;  // Count of current-level literals not yet resolved
        let mut learned: Vec<i32> = Vec::new();
        let mut p: Option<i32> = None;  // Current pivot literal
        let mut clause_to_resolve = self.clauses[conflict_clause].clone();
        let mut trail_idx = self.trail.len();

        loop {
            // Add literals from the current clause
            for &lit in &clause_to_resolve {
                let var = lit.unsigned_abs() as usize;

                // Skip the pivot
                if Some(lit) == p || Some(-lit) == p {
                    continue;
                }

                if !seen[var] {
                    seen[var] = true;
                    let a = self.assignments[var].as_ref().ok_or_else(|| {
                        SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Variable in conflict clause is not assigned".to_string(),
                        }
                    })?;
                    if a.decision_level == self.decision_level {
                        // Current level - will be resolved away
                        counter += 1;
                    } else if a.decision_level > 0 {
                        // Lower level - add to learned clause
                        learned.push(lit);
                        // Bump activity for variables involved in conflicts
                        self.var_activity[var] += self.activity_inc;
                    }
                }
            }

            // Find the next literal to resolve (most recent on trail from current level)
            loop {
                if trail_idx == 0 {
                    return Err(SolverError::InternalError(
                        "Trail exhausted during conflict analysis".to_string()
                    ));
                }
                trail_idx -= 1;
                let lit = self.trail[trail_idx];
                let var = lit.unsigned_abs() as usize;
                if seen[var] {
                    seen[var] = false;
                    p = Some(lit);
                    counter -= 1;

                    if counter == 0 {
                        // Found first UIP - add its negation to learned clause
                        learned.insert(0, -lit);

                        // Calculate backtrack level (second highest level in learned clause)
                        let mut bt_level = 0;
                        if learned.len() > 1 {
                            let mut max_idx = 1;
                            for i in 2..learned.len() {
                                let lvl = self.assignments[learned[i].unsigned_abs() as usize]
                                    .as_ref()
                                    .map(|a| a.decision_level)
                                    .unwrap_or(0);
                                let max_lvl = self.assignments[learned[max_idx].unsigned_abs() as usize]
                                    .as_ref()
                                    .map(|a| a.decision_level)
                                    .unwrap_or(0);
                                if lvl > max_lvl {
                                    max_idx = i;
                                }
                            }
                            // Put second-highest at position 1 for watching
                            learned.swap(1, max_idx);
                            bt_level = self.assignments[learned[1].unsigned_abs() as usize]
                                .as_ref()
                                .map(|a| a.decision_level)
                                .unwrap_or(0);
                        }

                        // Bump activities for all literals in learned clause
                        for &lit in &learned {
                            self.var_activity[lit.unsigned_abs() as usize] += self.activity_inc;
                        }

                        return Ok((learned, bt_level));
                    }

                    // Get the antecedent clause for further resolution
                    let assignment = self.assignments[var].as_ref().ok_or_else(|| {
                        SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Variable on trail is not assigned".to_string(),
                        }
                    })?;

                    if let Some(ante) = assignment.antecedent_clause {
                        clause_to_resolve = self.clauses[ante].clone();
                        break;
                    } else {
                        return Err(SolverError::InvalidConflictAnalysis {
                            variable: var as i32,
                            message: "Decision variable encountered during conflict analysis with counter > 0".to_string(),
                        });
                    }
                }
            }
        }
    }

    /// Backtracks to the given decision level.
    ///
    /// Undoes all assignments made at levels higher than `level`.
    /// Level-0 assignments are never undone.
    fn backtrack(&mut self, level: i32) {
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
        self.propagation_queue.clear();
    }

    /// Adds a learned clause to the solver.
    ///
    /// Sets up watches for the new clause.
    fn add_learned_clause(&mut self, learned: Vec<i32>) {
        if learned.is_empty() {
            return;
        }

        let clause_idx = self.clauses.len();

        if learned.len() >= 2 {
            // Watch the first two literals
            let w1 = Self::lit_to_watch_idx(learned[0], self.num_vars);
            let w2 = Self::lit_to_watch_idx(learned[1], self.num_vars);
            self.watches[w1].push(clause_idx);
            self.watches[w2].push(clause_idx);
        }

        self.clauses.push(learned);
    }

    /// Decays all variable activities.
    ///
    /// This is done by increasing the activity increment, which effectively
    /// gives more weight to recent conflicts. Rescales when values get too large.
    fn decay_activities(&mut self) {
        self.activity_inc *= 1.05;
        if self.activity_inc > 1e100 {
            // Rescale to prevent overflow
            for i in 1..=self.num_vars as usize {
                self.var_activity[i] *= 1e-100;
            }
            self.activity_inc *= 1e-100;
        }
    }

    // ========================================================================
    // Restart Management
    // ========================================================================

    /// Computes the i-th element of the Luby sequence (0-indexed).
    ///
    /// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    /// It has theoretical optimality guarantees for restart strategies.
    fn luby(i: u32) -> u32 {
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
    fn restart(&mut self) {
        self.backtrack(0);

        // Update restart schedule using Luby sequence
        self.luby_index += 1;
        self.conflicts_until_restart = self.luby_unit * Self::luby(self.luby_index) as u64;
    }

    /// Checks if it's time to restart based on conflict count.
    #[inline]
    fn should_restart(&self) -> bool {
        self.conflicts >= self.conflicts_until_restart
    }

    /// Solves the SAT problem.
    ///
    /// # Returns
    ///
    /// - `Ok(true)` if the formula is satisfiable
    /// - `Ok(false)` if the formula is unsatisfiable
    /// - `Err(SolverError)` if an internal error occurred
    ///
    /// # Example
    ///
    /// ```
    /// use cdcl_sat::{CDCLSolver, Clause, Literal};
    ///
    /// // Satisfiable: (x1 OR x2)
    /// let clauses = vec![
    ///     Clause::new(vec![Literal::positive(1), Literal::positive(2)]),
    /// ];
    /// let mut solver = CDCLSolver::new(clauses);
    /// assert!(solver.solve().unwrap());
    ///
    /// // Unsatisfiable: x1 AND NOT x1
    /// let clauses = vec![
    ///     Clause::new(vec![Literal::positive(1)]),
    ///     Clause::new(vec![Literal::negative(1)]),
    /// ];
    /// let mut solver = CDCLSolver::new(clauses);
    /// assert!(!solver.solve().unwrap());
    /// ```
    pub fn solve(&mut self) -> Result<bool, SolverError> {
        // Check for conflicts detected during initialization
        if self.initial_conflict {
            return Ok(false);
        }

        // Initial propagation
        if self.propagate().is_some() {
            return Ok(false);
        }

        loop {
            // Check if we should restart
            if self.should_restart() {
                self.restart();
            }

            match self.pick_branching_literal() {
                Some(lit) => {
                    // Make a decision (lit already has the correct polarity from phase saving)
                    self.decision_level += 1;
                    self.trail_lim.push(self.trail.len());
                    self.assign(lit, None);

                    // Propagate and handle conflicts
                    loop {
                        match self.propagate() {
                            None => break,
                            Some(conflict_clause) => {
                                // Count conflicts for restart scheduling
                                self.conflicts += 1;

                                if self.decision_level == 0 {
                                    // Conflict at level 0 - unsatisfiable
                                    return Ok(false);
                                }

                                // Learn from the conflict
                                let (learned, backtrack_level) = self.analyze_conflict(conflict_clause)?;
                                self.backtrack(backtrack_level);

                                // Add learned clause and propagate its unit literal
                                let unit_lit = learned[0];
                                self.add_learned_clause(learned);
                                self.assign(unit_lit, Some(self.clauses.len() - 1));

                                self.decay_activities();
                            }
                        }
                    }
                }
                None => {
                    // All variables assigned - satisfiable!
                    return Ok(true);
                }
            }
        }
    }

    /// Returns the current assignment for a variable.
    ///
    /// # Arguments
    ///
    /// * `var` - The variable number (1-indexed)
    ///
    /// # Returns
    ///
    /// - `Some(true)` if the variable is assigned true
    /// - `Some(false)` if the variable is assigned false
    /// - `None` if the variable is unassigned
    pub fn get_value(&self, var: i32) -> Option<bool> {
        let v = var.unsigned_abs() as usize;
        match self.values.get(v) {
            Some(1) => Some(true),
            Some(-1) => Some(false),
            _ => None,
        }
    }

    /// Returns the satisfying assignment if the formula is SAT.
    ///
    /// Should only be called after `solve()` returns `true`.
    ///
    /// # Returns
    ///
    /// A vector where index `i` contains the truth value for variable `i`.
    /// Index 0 is unused.
    pub fn get_model(&self) -> Vec<bool> {
        self.values.iter()
            .map(|&v| v == 1)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;

    fn make_clause(lits: &[(i32, bool)]) -> Clause {
        Clause::new(
            lits.iter()
                .map(|&(var, neg)| {
                    if neg {
                        Literal::negative(var)
                    } else {
                        Literal::positive(var)
                    }
                })
                .collect()
        )
    }

    #[test]
    fn test_single_variable_sat() {
        let clauses = vec![make_clause(&[(1, false)])];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_contradiction_unsat() {
        // x1 AND NOT x1
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(1, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_simple_sat() {
        // (x1 OR x2) AND (NOT x1 OR x2)
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, true), (2, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_unit_propagation() {
        // x1 AND (NOT x1 OR x2) AND (NOT x2 OR x3)
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(1, true), (2, false)]),
            make_clause(&[(2, true), (3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(true));
        assert_eq!(solver.get_value(3), Some(true));
    }

    #[test]
    fn test_conflict_learning() {
        // A formula that requires conflict learning to solve efficiently
        // (x1 OR x2) AND (x1 OR NOT x2) AND (NOT x1 OR x2) AND (NOT x1 OR NOT x2)
        // This is UNSAT
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, false), (2, true)]),
            make_clause(&[(1, true), (2, false)]),
            make_clause(&[(1, true), (2, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_get_model() {
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(2, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        let model = solver.get_model();
        assert!(model[1]);
        assert!(model[2]);
    }

    // ========================================================================
    // Edge Case Tests
    // ========================================================================

    #[test]
    fn test_empty_clause_set() {
        // Empty clause set is trivially SAT
        let clauses: Vec<Clause> = vec![];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_single_unit_clause() {
        // Just x1
        let clauses = vec![make_clause(&[(1, false)])];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
    }

    #[test]
    fn test_single_negative_unit_clause() {
        // Just NOT x1
        let clauses = vec![make_clause(&[(1, true)])];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(false));
    }

    #[test]
    fn test_multiple_unit_clauses_consistent() {
        // x1 AND x2 AND x3
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(2, false)]),
            make_clause(&[(3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(true));
        assert_eq!(solver.get_value(3), Some(true));
    }

    #[test]
    fn test_multiple_unit_clauses_conflict() {
        // x1 AND NOT x1 - immediate conflict
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(1, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_large_variable_numbers() {
        // Use variables with large gaps: x100 AND x200 AND (NOT x100 OR x300)
        let clauses = vec![
            Clause::new(vec![Literal::positive(100)]),
            Clause::new(vec![Literal::positive(200)]),
            Clause::new(vec![Literal::negative(100), Literal::positive(300)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(100), Some(true));
        assert_eq!(solver.get_value(200), Some(true));
        assert_eq!(solver.get_value(300), Some(true));
    }

    #[test]
    fn test_binary_clauses_sat() {
        // (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR x3)
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, true), (3, false)]),
            make_clause(&[(2, true), (3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_binary_clauses_unsat() {
        // (x1 OR x2) AND (NOT x1 OR NOT x2) AND (x1 OR NOT x2) AND (NOT x1 OR x2)
        // This forces x1 = x2 and x1 != x2 simultaneously
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),   // x1 OR x2
            make_clause(&[(1, true), (2, true)]),     // NOT x1 OR NOT x2
            make_clause(&[(1, false), (2, true)]),    // x1 OR NOT x2
            make_clause(&[(1, true), (2, false)]),    // NOT x1 OR x2
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_long_implication_chain() {
        // x1 AND (NOT x1 OR x2) AND (NOT x2 OR x3) AND ... AND (NOT x9 OR x10)
        let mut clauses = vec![make_clause(&[(1, false)])];
        for i in 1..10 {
            clauses.push(make_clause(&[(i, true), (i + 1, false)]));
        }
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        // All variables should be true due to unit propagation
        for i in 1..=10 {
            assert_eq!(solver.get_value(i), Some(true));
        }
    }

    #[test]
    fn test_long_implication_chain_unsat() {
        // x1 AND (NOT x1 OR x2) AND ... AND (NOT x9 OR x10) AND NOT x10
        let mut clauses = vec![make_clause(&[(1, false)])];
        for i in 1..10 {
            clauses.push(make_clause(&[(i, true), (i + 1, false)]));
        }
        clauses.push(make_clause(&[(10, true)])); // NOT x10
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_three_literal_clauses() {
        // (x1 OR x2 OR x3) AND (NOT x1 OR NOT x2 OR NOT x3)
        let clauses = vec![
            make_clause(&[(1, false), (2, false), (3, false)]),
            make_clause(&[(1, true), (2, true), (3, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_pigeonhole_2_1() {
        // 2 pigeons, 1 hole - UNSAT
        // p1 must be in hole 1: x1
        // p2 must be in hole 1: x2
        // At most one pigeon per hole: NOT x1 OR NOT x2
        let clauses = vec![
            make_clause(&[(1, false)]),              // pigeon 1 in hole 1
            make_clause(&[(2, false)]),              // pigeon 2 in hole 1
            make_clause(&[(1, true), (2, true)]),    // at most one per hole
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_pigeonhole_3_2() {
        // 3 pigeons, 2 holes - UNSAT
        // Pigeon 1: x1 (hole 1) OR x2 (hole 2)
        // Pigeon 2: x3 (hole 1) OR x4 (hole 2)
        // Pigeon 3: x5 (hole 1) OR x6 (hole 2)
        // Hole 1 at most one: pairs of NOT xi OR NOT xj for x1,x3,x5
        // Hole 2 at most one: pairs of NOT xi OR NOT xj for x2,x4,x6
        let clauses = vec![
            // Each pigeon in some hole
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(3, false), (4, false)]),
            make_clause(&[(5, false), (6, false)]),
            // Hole 1: at most one
            make_clause(&[(1, true), (3, true)]),
            make_clause(&[(1, true), (5, true)]),
            make_clause(&[(3, true), (5, true)]),
            // Hole 2: at most one
            make_clause(&[(2, true), (4, true)]),
            make_clause(&[(2, true), (6, true)]),
            make_clause(&[(4, true), (6, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_horn_clauses_sat() {
        // Horn clauses: at most one positive literal per clause
        // (NOT x1 OR NOT x2 OR x3) AND (NOT x3 OR x4) AND x1 AND x2
        let clauses = vec![
            make_clause(&[(1, true), (2, true), (3, false)]),
            make_clause(&[(3, true), (4, false)]),
            make_clause(&[(1, false)]),
            make_clause(&[(2, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(true));
        assert_eq!(solver.get_value(3), Some(true));
        assert_eq!(solver.get_value(4), Some(true));
    }

    #[test]
    fn test_get_value_unassigned() {
        // Create solver but don't solve - all variables unassigned
        let clauses = vec![make_clause(&[(1, false), (2, false)])];
        let solver = CDCLSolver::new(clauses);
        // Before solving, variables may be unassigned
        // After solving, let's check
        let mut solver = solver;
        solver.solve().unwrap();
        // At least one should be assigned
        let v1 = solver.get_value(1);
        let v2 = solver.get_value(2);
        assert!(v1.is_some() || v2.is_some());
    }

    #[test]
    fn test_get_value_out_of_bounds() {
        let clauses = vec![make_clause(&[(1, false)])];
        let mut solver = CDCLSolver::new(clauses);
        solver.solve().unwrap();
        // Variable 1000 doesn't exist
        assert_eq!(solver.get_value(1000), None);
    }

    #[test]
    fn test_duplicate_clauses() {
        // Same clause twice shouldn't break anything
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, false), (2, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_all_negative_clause() {
        // (NOT x1 OR NOT x2 OR NOT x3) - SAT (set any to false)
        let clauses = vec![
            make_clause(&[(1, true), (2, true), (3, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    #[test]
    fn test_mixed_polarity_unit_propagation() {
        // x1 AND NOT x2 AND (NOT x1 OR x2 OR x3)
        // x1=T, x2=F makes (NOT x1 OR x2 OR x3) = (F OR F OR x3) = x3
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(2, true)]),
            make_clause(&[(1, true), (2, false), (3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(true));
        assert_eq!(solver.get_value(2), Some(false));
        assert_eq!(solver.get_value(3), Some(true));
    }

    #[test]
    fn test_multiple_backtrack_levels() {
        // Formula requiring backtracking through multiple levels
        // This creates a more complex search tree
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, false), (2, true)]),
            make_clause(&[(1, true), (3, false)]),
            make_clause(&[(1, true), (3, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_solver_error_display() {
        let err = SolverError::InvalidConflictAnalysis {
            variable: 5,
            message: "test error".to_string(),
        };
        let msg = format!("{}", err);
        assert!(msg.contains("variable 5"));
        assert!(msg.contains("test error"));

        let err2 = SolverError::InternalError("internal test".to_string());
        let msg2 = format!("{}", err2);
        assert!(msg2.contains("internal test"));
    }

    #[test]
    fn test_activity_decay() {
        // Create a formula that will cause multiple conflicts
        // to test the activity decay mechanism
        let clauses = vec![
            make_clause(&[(1, false), (2, false)]),
            make_clause(&[(1, false), (2, true)]),
            make_clause(&[(1, true), (2, false)]),
            make_clause(&[(1, true), (2, true)]),
            make_clause(&[(3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        // Should be UNSAT due to clauses 1-4
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_watched_literal_maintenance() {
        // Test that watches are properly maintained
        // by creating clauses that force watch updates
        let clauses = vec![
            make_clause(&[(1, false), (2, false), (3, false)]),
            make_clause(&[(1, true)]),  // Forces x1=F
            make_clause(&[(2, true)]),  // Forces x2=F
            // Now first clause only has x3 as non-false
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
        assert_eq!(solver.get_value(1), Some(false));
        assert_eq!(solver.get_value(2), Some(false));
        assert_eq!(solver.get_value(3), Some(true));
    }

    #[test]
    fn test_initial_conflict_detection() {
        // Conflicting unit clauses detected at initialization
        let clauses = vec![
            make_clause(&[(1, false)]),
            make_clause(&[(1, true)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.solve().unwrap());
    }

    #[test]
    fn test_many_variables_sparse() {
        // Many variables but sparse usage
        let clauses = vec![
            Clause::new(vec![Literal::positive(1), Literal::positive(50)]),
            Clause::new(vec![Literal::negative(1), Literal::positive(100)]),
            Clause::new(vec![Literal::negative(50), Literal::negative(100)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        assert!(solver.solve().unwrap());
    }

    // ========================================================================
    // Luby Sequence Tests
    // ========================================================================

    #[test]
    fn test_luby_sequence_values() {
        // The Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
        assert_eq!(CDCLSolver::luby(0), 1);
        assert_eq!(CDCLSolver::luby(1), 1);
        assert_eq!(CDCLSolver::luby(2), 2);
        assert_eq!(CDCLSolver::luby(3), 1);
        assert_eq!(CDCLSolver::luby(4), 1);
        assert_eq!(CDCLSolver::luby(5), 2);
        assert_eq!(CDCLSolver::luby(6), 4);
        assert_eq!(CDCLSolver::luby(7), 1);
        assert_eq!(CDCLSolver::luby(8), 1);
        assert_eq!(CDCLSolver::luby(9), 2);
        assert_eq!(CDCLSolver::luby(10), 1);
        assert_eq!(CDCLSolver::luby(11), 1);
        assert_eq!(CDCLSolver::luby(12), 2);
        assert_eq!(CDCLSolver::luby(13), 4);
        assert_eq!(CDCLSolver::luby(14), 8);
    }

    #[test]
    fn test_luby_powers_of_two() {
        // At indices 2^n - 2, the Luby value is 2^(n-1)
        // Index 0: 1, Index 2: 2, Index 6: 4, Index 14: 8, Index 30: 16
        assert_eq!(CDCLSolver::luby(0), 1);
        assert_eq!(CDCLSolver::luby(2), 2);
        assert_eq!(CDCLSolver::luby(6), 4);
        assert_eq!(CDCLSolver::luby(14), 8);
        assert_eq!(CDCLSolver::luby(30), 16);
    }

    // ========================================================================
    // Phase Saving Tests
    // ========================================================================

    #[test]
    fn test_phase_saving_initialization() {
        // All phases should default to true (positive)
        let clauses = vec![make_clause(&[(1, false), (2, false)])];
        let solver = CDCLSolver::new(clauses);
        assert!(solver.saved_phase[1]);
        assert!(solver.saved_phase[2]);
    }

    #[test]
    fn test_phase_saving_updates() {
        // Phase should be saved when a variable is assigned
        let clauses = vec![
            make_clause(&[(1, true)]),  // Forces x1 = false
            make_clause(&[(2, false), (3, false)]),
        ];
        let mut solver = CDCLSolver::new(clauses);
        solver.solve().unwrap();
        // x1 was forced to false, so saved_phase should be false
        assert!(!solver.saved_phase[1]);
    }

    // ========================================================================
    // Restart Tests
    // ========================================================================

    #[test]
    fn test_restart_initialization() {
        let clauses = vec![make_clause(&[(1, false), (2, false)])];
        let solver = CDCLSolver::new(clauses);
        assert_eq!(solver.conflicts, 0);
        assert_eq!(solver.luby_index, 0);
        assert_eq!(solver.luby_unit, 100);
        assert_eq!(solver.conflicts_until_restart, 100);
    }

    #[test]
    fn test_should_restart() {
        let clauses = vec![make_clause(&[(1, false), (2, false)])];
        let mut solver = CDCLSolver::new(clauses);
        assert!(!solver.should_restart());
        solver.conflicts = 100;
        assert!(solver.should_restart());
        solver.conflicts = 99;
        assert!(!solver.should_restart());
    }

    #[test]
    fn test_restart_updates_schedule() {
        let clauses = vec![make_clause(&[(1, false), (2, false)])];
        let mut solver = CDCLSolver::new(clauses);
        let _initial_restart = solver.conflicts_until_restart;
        solver.restart();
        // After restart, luby_index increases and schedule is updated
        assert_eq!(solver.luby_index, 1);
        // Luby(1) = 1, so conflicts_until_restart = 100 * 1 = 100
        assert_eq!(solver.conflicts_until_restart, 100);
        solver.restart();
        assert_eq!(solver.luby_index, 2);
        // Luby(2) = 2, so conflicts_until_restart = 100 * 2 = 200
        assert_eq!(solver.conflicts_until_restart, 200);
    }
}
