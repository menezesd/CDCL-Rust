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

mod propagate;
mod analyze;
mod decide;
mod reduce;
mod restart;
mod backtrack;
mod inprocess;
mod incremental;
mod stats;
#[cfg(test)]
mod tests;

use std::fmt;

use crate::Clause;
use crate::preprocess;
use crate::heap::VarHeap;
use crate::clause_arena::{ClauseArena, CRef, CREF_UNDEF};

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
                write!(f, "Invalid conflict analysis at variable {variable}: {message}")
            }
            SolverError::InternalError(msg) => {
                write!(f, "Internal solver error: {msg}")
            }
        }
    }
}

impl std::error::Error for SolverError {}

/// Tracks information about a variable assignment.
///
/// Uses `CREF_UNDEF` as sentinel for decision variables (no antecedent),
/// avoiding the overhead of `Option`. A `decision_level` of -1 means
/// the variable is unassigned.
#[derive(Debug, Clone, Copy)]
struct Assignment {
    decision_level: i32,
    antecedent: CRef, // CREF_UNDEF for decisions
}

impl Assignment {
    const UNASSIGNED: Assignment = Assignment { decision_level: -1, antecedent: CREF_UNDEF };
}

/// A watch list entry with a blocking literal.
///
/// The blocking literal optimization avoids accessing the clause array
/// when a blocker is satisfied, saving ~50% of clause accesses during BCP.
#[derive(Debug, Clone, Copy)]
struct Watcher {
    /// Clause index. If MSB is set, this is a binary clause and the blocker
    /// is the other literal (no clause array access needed during propagation).
    cref: usize,
    blocker: i32,
}

impl Watcher {
    const BINARY_BIT: usize = 1usize << (usize::BITS - 1);

    #[inline]
    fn long(cr: CRef, blocker: i32) -> Self {
        Watcher { cref: cr as usize, blocker }
    }

    #[inline]
    fn binary(cr: CRef, other_lit: i32) -> Self {
        Watcher { cref: (cr as usize) | Self::BINARY_BIT, blocker: other_lit }
    }

    #[inline]
    fn clause_idx(self) -> CRef { (self.cref & !Self::BINARY_BIT) as CRef }
}

/// A CDCL SAT solver.
///
/// This solver implements the Conflict-Driven Clause Learning algorithm
/// with modern optimizations including two-watched literals, first-UIP
/// learning, non-chronological backtracking, VSIDS variable selection,
/// phase saving, and restarts.
pub struct CDCLSolver {
    /// Arena-allocated clause database.
    arena: ClauseArena,

    /// Ordered list of all clause references (for iteration/compaction).
    clause_refs: Vec<CRef>,

    /// The number of variables in the formula.
    num_vars: i32,

    /// Current value of each variable: -1 (false), 0 (unassigned), 1 (true).
    /// Index 0 is unused; variables are 1-indexed.
    values: Vec<i8>,

    /// Assignment information for each variable. Index 0 unused.
    /// Use `assignment.decision_level == -1` to check if unassigned.
    assignments: Vec<Assignment>,

    /// Trail of assignments in chronological order.
    trail: Vec<i32>,

    /// Indices into trail marking the start of each decision level.
    trail_lim: Vec<usize>,

    /// Current decision level.
    decision_level: i32,

    /// Activity increment (increases after each conflict).
    /// Activity scores live in `var_heap.activity` — single source of truth.
    activity_inc: f64,

    /// Watch lists for long clauses (3+ literals) with blocking literals.
    watches: Vec<Vec<Watcher>>,

    /// Binary implication graph: bin_implies[lit_idx] = vec of (implied_lit, cref).
    /// When literal `lit` becomes true, all `implied_lit` values must also be true
    /// (or a conflict is detected). Much faster than watch-list scanning for binaries.
    bin_implies: Vec<Vec<(i32, CRef)>>,

    /// Index into trail for next literal to propagate (replaces VecDeque).
    qhead: usize,

    /// Reusable scratch buffer for conflict analysis (avoids per-conflict allocation).
    seen: Vec<bool>,

    /// Position-indexed heap for variable selection (VSIDS).
    var_heap: VarHeap,

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

    /// Running sum of all learned clause LBDs (for long-term average).
    lbd_sum: f64,

    /// Conflict count at last restart (for minimum interval).
    last_restart_conflicts: u64,

    /// Recent LBDs for short-term average (circular buffer).
    recent_lbds: Vec<u32>,

    /// Index into recent_lbds circular buffer.
    recent_lbd_idx: usize,

    /// Whether we've filled the recent buffer at least once.
    recent_lbd_full: bool,

    // ========================================================================
    // Clause Database Management
    // ========================================================================

    /// Index into clause_refs of the first learned clause.
    first_learned_idx: usize,

    /// Number of learned clauses currently alive.
    num_learned_alive: usize,

    /// Threshold for triggering clause database reduction.
    max_learned: usize,

    /// Conflicts at which next inprocessing round triggers.
    next_inprocess: u64,

    /// Simple RNG state for random decisions (xorshift32).
    rng_state: u32,

    /// Fraction of decisions that are random (0.0 to 1.0). MiniSAT default: 0.02.
    random_var_freq: f64,

    /// Statistics counters.
    decisions: u64,
    propagations: u64,
    restarts: u64,
    reductions: u64,

    /// DRAT proof logger (disabled by default).
    #[allow(dead_code)]
    drat: crate::drat::DratLogger,

    /// Clause activity increment (increases after each conflict, f32 precision).
    clause_act_inc: f32,
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

        let mut arena = ClauseArena::new();
        let mut clause_refs: Vec<CRef> = Vec::new();
        let mut watches: Vec<Vec<Watcher>> = vec![Vec::new(); num_lits];
        let mut bin_implies: Vec<Vec<(i32, CRef)>> = vec![Vec::new(); num_lits];
        let mut unit_clauses: Vec<(i32, CRef)> = Vec::new();

        // Convert clauses and set up watches / binary implication graph
        for clause in &clauses {
            let signed_lits: Vec<i32> = clause.literals.iter()
                .map(|l| l.as_signed())
                .collect();

            if signed_lits.is_empty() {
                continue;
            }

            let cr = arena.alloc(&signed_lits, false, 0);
            clause_refs.push(cr);

            if signed_lits.len() == 2 {
                // Binary clause: add to implication graph
                // When -a is true (a is false), b must be true, and vice versa
                let idx_a = Self::lit_to_watch_idx(-signed_lits[0], num_vars);
                let idx_b = Self::lit_to_watch_idx(-signed_lits[1], num_vars);
                bin_implies[idx_a].push((signed_lits[1], cr));
                bin_implies[idx_b].push((signed_lits[0], cr));
            } else if signed_lits.len() > 2 {
                let w1 = Self::lit_to_watch_idx(signed_lits[0], num_vars);
                let w2 = Self::lit_to_watch_idx(signed_lits[1], num_vars);
                watches[w1].push(Watcher::long(cr, signed_lits[1]));
                watches[w2].push(Watcher::long(cr, signed_lits[0]));
            } else {
                // Unit clause - record for later assignment
                unit_clauses.push((signed_lits[0], cr));
            }
        }

        // Initialize variable activities from occurrence counts
        let mut activity = vec![0.0; num_vars as usize + 1];
        for &cr in &clause_refs {
            for &lit in arena.lits(cr) {
                let var = lit.unsigned_abs() as usize;
                activity[var] += 1.0;
            }
        }

        // Build the initial variable heap (position-indexed, MiniSAT-style)
        let mut var_heap = VarHeap::new(num_vars as usize);
        var_heap.set_activity(&activity);
        for var in 1..=num_vars as usize {
            var_heap.insert(var as i32);
        }

        let num_original = clause_refs.len();

        let mut solver = CDCLSolver {
            arena,
            clause_refs,
            num_vars,
            values: vec![0; num_vars as usize + 1],
            assignments: vec![Assignment::UNASSIGNED; num_vars as usize + 1],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            activity_inc: 1.0,
            watches,
            bin_implies,
            qhead: 0,
            seen: vec![false; num_vars as usize + 1],
            var_heap,
            initial_conflict: false,
            saved_phase: vec![true; num_vars as usize + 1],
            // Restart management
            conflicts: 0,
            conflicts_until_restart: 100,  // First restart after 100 conflicts
            luby_index: 0,
            luby_unit: 100,
            // Glucose-style restart tracking
            lbd_sum: 0.0,
            last_restart_conflicts: 0,
            recent_lbds: vec![0; 50],
            recent_lbd_idx: 0,
            recent_lbd_full: false,
            // Clause database management
            first_learned_idx: num_original,
            num_learned_alive: 0,
            max_learned: (num_original / 10).max(2000),
            next_inprocess: u64::MAX, // disabled by default; enable with set_inprocessing()
            rng_state: 91648253, // MiniSAT default seed
            random_var_freq: 0.02,
            decisions: 0,
            propagations: 0,
            restarts: 0,
            reductions: 0,
            drat: crate::drat::DratLogger::disabled(),
            clause_act_inc: 1.0,
        };

        // Assign unit clauses at decision level 0
        for (lit, _cr) in unit_clauses {
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

        // For incremental solving: backtrack to level 0 before re-solving
        if self.decision_level > 0 {
            self.backtrack(0);
        }

        // Initial/re-propagation
        if self.propagate().is_some() {
            return Ok(false);
        }

        #[cfg(feature = "stats")]
        let start_time = std::time::Instant::now();

        loop {
            // Check if we should restart
            if self.should_restart() {
                self.restart();

                // Inprocessing: run BVE/probing at level 0 periodically
                if self.conflicts >= self.next_inprocess {
                    self.inprocess();
                    // Propagate any new units from inprocessing
                    if self.propagate().is_some() {
                        return Ok(false);
                    }
                }
            }

            // Reduce learned clause database if it's grown too large
            if self.num_learned_alive > self.max_learned {
                self.reduce_db();
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
                                    #[cfg(feature = "stats")]
                                    self.print_stats(start_time);
                                    return Ok(false);
                                }

                                // Learn from the conflict
                                let (learned, backtrack_level) = self.analyze_conflict(conflict_clause)?;
                                self.backtrack(backtrack_level);

                                // Add learned clause and propagate its unit literal
                                let unit_lit = learned[0];
                                let (cr, lbd) = self.add_learned_clause(learned);
                                self.record_lbd(lbd);
                                self.assign(unit_lit, Some(cr));

                                self.decay_activities();

                                #[cfg(feature = "stats")]
                                if self.conflicts.is_multiple_of(10000) {
                                    let elapsed = start_time.elapsed().as_secs_f64();
                                    eprintln!("c conflicts={} restarts={} learned={} trail={} cps={:.0}",
                                        self.conflicts, self.restarts, self.num_learned_alive,
                                        self.trail.len(), self.conflicts as f64 / elapsed);
                                }
                            }
                        }
                    }
                }
                None => {
                    // All variables assigned - satisfiable!
                    #[cfg(feature = "stats")]
                    self.print_stats(start_time);
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

    /// Enables DRAT proof logging to the given file path.
    ///
    /// Must be called before `solve()`. The proof file records every learned
    /// clause addition and deletion, allowing external verification of UNSAT
    /// results using tools like `drat-trim`.
    pub fn enable_drat(&mut self, path: &str) -> std::io::Result<()> {
        self.drat = crate::drat::DratLogger::new(path)?;
        Ok(())
    }
}

