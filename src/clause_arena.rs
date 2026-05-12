//! Arena-allocated clause database for cache-efficient propagation.
//!
//! Clauses are stored contiguously in a single `Vec<u32>` buffer, eliminating
//! per-clause heap allocations and improving cache locality during the
//! propagation hot loop. This design is inspired by MiniSAT's `ClauseAllocator`.
//!
//! # Layout
//!
//! Each clause is stored as a contiguous sequence of `u32` words:
//!
//! ```text
//! [header] [lbd]? [lit0] [lit1] [lit2] ...
//! ```
//!
//! - **Header** (1 word): bits 0-29 = clause length, bit 30 = learnt flag,
//!   bit 31 = deleted flag.
//! - **LBD** (1 word, only present for learned clauses): the Literal Block
//!   Distance, used to gauge clause quality during garbage collection.
//! - **Literals**: `i32` literals stored as `u32` via `transmute`. The solver
//!   continues to use signed `i32` literals externally; the arena handles
//!   the conversion transparently.
//!
//! A [`CRef`] is simply a `u32` index of the clause header inside the buffer.

/// A reference to a clause in the arena. This is the index of the clause's
/// header word inside [`ClauseArena::buf`].
pub type CRef = u32;

/// Sentinel value representing "no clause".
pub const CREF_UNDEF: CRef = u32::MAX;

const LEN_MASK: u32 = 0x3FFF_FFFF; // bits 0-29
const LEARNT_BIT: u32 = 1 << 30;
const DELETED_BIT: u32 = 1 << 31;

/// Arena-allocated clause database.
///
/// All clauses live inside a single contiguous `Vec<u32>` buffer. New clauses
/// are appended at the end; deleted clauses are marked in-place and their
/// space is reclaimed only during an explicit garbage-collection pass (not
/// implemented here — that belongs in the solver).
pub struct ClauseArena {
    /// Backing store. Clauses are packed contiguously.
    buf: Vec<u32>,
    /// Total number of `u32` words occupied by deleted (but not yet reclaimed)
    /// clauses, including their headers and LBD words.
    wasted: usize,
}

impl ClauseArena {
    /// Creates a new, empty arena.
    pub fn new() -> Self {
        ClauseArena {
            buf: Vec::new(),
            wasted: 0,
        }
    }

    /// Creates an arena with the given initial capacity (in `u32` words).
    pub fn with_capacity(cap: usize) -> Self {
        ClauseArena {
            buf: Vec::with_capacity(cap),
            wasted: 0,
        }
    }

    /// Allocates a new clause in the arena.
    ///
    /// # Arguments
    ///
    /// * `lits`   — the clause's literals (signed `i32`, DIMACS-style).
    /// * `learnt` — whether this is a learned clause.
    /// * `lbd`    — Literal Block Distance (only meaningful when `learnt` is true;
    ///   ignored for original clauses).
    ///
    /// # Returns
    ///
    /// A [`CRef`] that can be used to access the clause later.
    ///
    /// # Panics
    ///
    /// Panics if `lits.len()` exceeds 2^30 - 1 (about one billion literals).
    pub fn alloc(&mut self, lits: &[i32], learnt: bool, lbd: u32) -> CRef {
        let len = lits.len();
        assert!(
            len <= LEN_MASK as usize,
            "clause length {len} exceeds maximum {LEN_MASK}"
        );

        let cr = self.buf.len() as CRef;

        // Header
        let mut header = len as u32;
        if learnt {
            header |= LEARNT_BIT;
        }
        self.buf.push(header);

        // LBD + activity (only for learned clauses)
        if learnt {
            self.buf.push(lbd);
            self.buf.push(0); // activity (f32 as bits), initially 0.0
        }

        // Literals (i32 → u32 bit-cast)
        for &lit in lits {
            self.buf.push(lit as u32);
        }

        cr
    }

    // ------- accessors -------

    /// Returns the number of literals in the clause at `cr`.
    #[inline]
    pub fn len(&self, cr: CRef) -> usize {
        (self.buf[cr as usize] & LEN_MASK) as usize
    }

    /// Returns `true` if the clause at `cr` was marked as learned.
    #[inline]
    pub fn is_learnt(&self, cr: CRef) -> bool {
        self.buf[cr as usize] & LEARNT_BIT != 0
    }

    /// Returns `true` if the clause at `cr` has been marked as deleted.
    #[inline]
    pub fn is_deleted(&self, cr: CRef) -> bool {
        self.buf[cr as usize] & DELETED_BIT != 0
    }

    /// Marks the clause at `cr` as deleted.
    ///
    /// The space is not reclaimed immediately; instead the [`wasted`](Self::wasted)
    /// counter is incremented by the clause's total footprint (header + optional
    /// LBD + literals). A future GC pass can use this to decide when compaction
    /// is worthwhile.
    pub fn set_deleted(&mut self, cr: CRef) {
        let header = &mut self.buf[cr as usize];
        if *header & DELETED_BIT != 0 {
            return; // already deleted
        }
        *header |= DELETED_BIT;

        let learnt = *header & LEARNT_BIT != 0;
        let lit_count = (*header & LEN_MASK) as usize;
        // header(1) + lbd+activity(0 or 2) + literals
        self.wasted += 1 + if learnt { 2 } else { 0 } + lit_count;
    }

    /// Returns the LBD of the learned clause at `cr`.
    ///
    /// # Panics
    ///
    /// Panics (in debug builds) if the clause is not learned.
    #[inline]
    pub fn lbd(&self, cr: CRef) -> u32 {
        debug_assert!(self.is_learnt(cr), "lbd() called on non-learnt clause");
        self.buf[cr as usize + 1]
    }

    /// Sets the LBD of the learned clause at `cr`.
    ///
    /// # Panics
    ///
    /// Panics (in debug builds) if the clause is not learned.
    #[inline]
    pub fn set_lbd(&mut self, cr: CRef, lbd: u32) {
        debug_assert!(self.is_learnt(cr), "set_lbd() called on non-learnt clause");
        self.buf[cr as usize + 1] = lbd;
    }

    /// Returns the activity of the learned clause at `cr` (as f32).
    #[inline]
    pub fn activity(&self, cr: CRef) -> f32 {
        debug_assert!(self.is_learnt(cr));
        f32::from_bits(self.buf[cr as usize + 2])
    }

    /// Sets the activity of the learned clause at `cr`.
    #[inline]
    pub fn set_activity(&mut self, cr: CRef, act: f32) {
        debug_assert!(self.is_learnt(cr));
        self.buf[cr as usize + 2] = act.to_bits();
    }

    /// Bumps the activity of a learned clause by the given increment.
    #[inline]
    pub fn bump_activity(&mut self, cr: CRef, inc: f32) {
        debug_assert!(self.is_learnt(cr));
        let idx = cr as usize + 2;
        let old = f32::from_bits(self.buf[idx]);
        self.buf[idx] = (old + inc).to_bits();
    }

    /// Returns the total number of `u32` words occupied by deleted clauses
    /// that have not yet been reclaimed.
    #[inline]
    pub fn wasted(&self) -> usize {
        self.wasted
    }

    /// Returns the total number of words in the buffer.
    #[inline]
    pub fn total_words(&self) -> usize {
        self.buf.len()
    }

    // ------- literal access -------

    /// Returns the starting index in `buf` of the first literal for the
    /// clause at `cr`.
    #[inline]
    fn lits_offset(&self, cr: CRef) -> usize {
        let i = cr as usize;
        if self.buf[i] & LEARNT_BIT != 0 {
            i + 3 // header + lbd + activity
        } else {
            i + 1 // header only
        }
    }

    /// Returns the literals of the clause at `cr` as an `&[i32]` slice.
    ///
    /// The returned slice aliases the arena buffer; this is safe because
    /// `i32` and `u32` have identical size, alignment, and no invalid bit
    /// patterns.
    #[inline]
    pub fn lits(&self, cr: CRef) -> &[i32] {
        let start = self.lits_offset(cr);
        let len = self.len(cr);
        let u32_slice = &self.buf[start..start + len];
        // SAFETY: i32 and u32 have the same size and alignment, and every
        // bit pattern is valid for both types.
        unsafe { std::mem::transmute::<&[u32], &[i32]>(u32_slice) }
    }

    /// Returns the literals of the clause at `cr` as a mutable `&mut [i32]`
    /// slice.
    ///
    /// This is used during propagation to swap watched literals to the front
    /// of the clause.
    #[inline]
    pub fn lits_mut(&mut self, cr: CRef) -> &mut [i32] {
        let start = self.lits_offset(cr);
        let len = self.len(cr);
        let u32_slice = &mut self.buf[start..start + len];
        // SAFETY: same justification as `lits()`.
        unsafe { std::mem::transmute::<&mut [u32], &mut [i32]>(u32_slice) }
    }
}

impl Default for ClauseArena {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- basic allocation and readback ----

    #[test]
    fn test_alloc_original_clause_and_readback() {
        let mut arena = ClauseArena::new();
        let lits: Vec<i32> = vec![1, -2, 3];
        let cr = arena.alloc(&lits, false, 0);

        assert_eq!(cr, 0);
        assert_eq!(arena.len(cr), 3);
        assert!(!arena.is_learnt(cr));
        assert!(!arena.is_deleted(cr));
        assert_eq!(arena.lits(cr), &[1, -2, 3]);
    }

    #[test]
    fn test_alloc_learned_clause_and_readback() {
        let mut arena = ClauseArena::new();
        let lits: Vec<i32> = vec![-5, 7];
        let cr = arena.alloc(&lits, true, 2);

        assert_eq!(cr, 0);
        assert_eq!(arena.len(cr), 2);
        assert!(arena.is_learnt(cr));
        assert!(!arena.is_deleted(cr));
        assert_eq!(arena.lbd(cr), 2);
        assert_eq!(arena.lits(cr), &[-5, 7]);
    }

    #[test]
    fn test_alloc_unit_clause() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[42], false, 0);
        assert_eq!(arena.len(cr), 1);
        assert_eq!(arena.lits(cr), &[42]);
    }

    #[test]
    fn test_alloc_empty_clause() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[], false, 0);
        assert_eq!(arena.len(cr), 0);
        assert_eq!(arena.lits(cr), &[] as &[i32]);
    }

    // ---- multiple clauses, different sizes ----

    #[test]
    fn test_multiple_clauses_original() {
        let mut arena = ClauseArena::new();

        let cr0 = arena.alloc(&[1, -2], false, 0);
        let cr1 = arena.alloc(&[3, 4, 5], false, 0);
        let cr2 = arena.alloc(&[-6], false, 0);

        // Verify each clause independently
        assert_eq!(arena.lits(cr0), &[1, -2]);
        assert_eq!(arena.lits(cr1), &[3, 4, 5]);
        assert_eq!(arena.lits(cr2), &[-6]);

        // CRefs should be at the expected offsets
        // cr0: header(1) + 2 lits = 3 words  => cr1 starts at 3
        assert_eq!(cr1, 3);
        // cr1: header(1) + 3 lits = 4 words  => cr2 starts at 7
        assert_eq!(cr2, 7);
    }

    #[test]
    fn test_multiple_clauses_mixed_learnt() {
        let mut arena = ClauseArena::new();

        // Original clause: header(1) + 2 lits = 3 words
        let cr0 = arena.alloc(&[1, -2], false, 0);
        // Learned clause: header(1) + lbd(1) + activity(1) + 3 lits = 6 words
        let cr1 = arena.alloc(&[3, 4, 5], true, 3);
        // Original clause: header(1) + 1 lit = 2 words
        let cr2 = arena.alloc(&[-6], false, 0);

        assert_eq!(cr0, 0);
        assert_eq!(cr1, 3);
        assert_eq!(cr2, 9);

        assert!(!arena.is_learnt(cr0));
        assert!(arena.is_learnt(cr1));
        assert!(!arena.is_learnt(cr2));

        assert_eq!(arena.lits(cr0), &[1, -2]);
        assert_eq!(arena.lits(cr1), &[3, 4, 5]);
        assert_eq!(arena.lbd(cr1), 3);
        assert_eq!(arena.lits(cr2), &[-6]);
    }

    // ---- mutation ----

    #[test]
    fn test_mutate_literals_swap() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[10, 20, 30], false, 0);

        // Swap first two literals (as the solver does to maintain watch invariant)
        let lits = arena.lits_mut(cr);
        lits.swap(0, 2);

        assert_eq!(arena.lits(cr), &[30, 20, 10]);
    }

    #[test]
    fn test_mutate_literals_overwrite() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, 2, 3, 4], true, 1);

        let lits = arena.lits_mut(cr);
        lits[1] = -99;

        assert_eq!(arena.lits(cr), &[1, -99, 3, 4]);
    }

    #[test]
    fn test_mutate_does_not_affect_neighbors() {
        let mut arena = ClauseArena::new();
        let cr0 = arena.alloc(&[1, 2], false, 0);
        let cr1 = arena.alloc(&[3, 4], false, 0);
        let cr2 = arena.alloc(&[5, 6], false, 0);

        // Mutate the middle clause
        let lits = arena.lits_mut(cr1);
        lits[0] = -100;
        lits[1] = -200;

        // Neighbors should be unaffected
        assert_eq!(arena.lits(cr0), &[1, 2]);
        assert_eq!(arena.lits(cr1), &[-100, -200]);
        assert_eq!(arena.lits(cr2), &[5, 6]);
    }

    // ---- deletion ----

    #[test]
    fn test_delete_original_clause() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, -2, 3], false, 0);

        assert!(!arena.is_deleted(cr));
        assert_eq!(arena.wasted(), 0);

        arena.set_deleted(cr);

        assert!(arena.is_deleted(cr));
        // wasted = header(1) + 3 lits = 4
        assert_eq!(arena.wasted(), 4);
        // Literals are still readable (useful during GC relocation)
        assert_eq!(arena.lits(cr), &[1, -2, 3]);
    }

    #[test]
    fn test_delete_learned_clause() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[-5, 7], true, 2);

        arena.set_deleted(cr);

        assert!(arena.is_deleted(cr));
        // wasted = header(1) + lbd(1) + activity(1) + 2 lits = 5
        assert_eq!(arena.wasted(), 5);
    }

    #[test]
    fn test_double_delete_is_idempotent() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, 2], false, 0);

        arena.set_deleted(cr);
        let w1 = arena.wasted();
        arena.set_deleted(cr);
        let w2 = arena.wasted();

        assert_eq!(w1, w2, "double delete should not double-count wasted space");
    }

    #[test]
    fn test_delete_preserves_other_clauses() {
        let mut arena = ClauseArena::new();
        let cr0 = arena.alloc(&[1, 2], false, 0);
        let cr1 = arena.alloc(&[3, 4, 5], false, 0);
        let cr2 = arena.alloc(&[6, 7], true, 1);

        arena.set_deleted(cr1);

        assert!(!arena.is_deleted(cr0));
        assert!(arena.is_deleted(cr1));
        assert!(!arena.is_deleted(cr2));

        assert_eq!(arena.lits(cr0), &[1, 2]);
        assert_eq!(arena.lits(cr2), &[6, 7]);
    }

    #[test]
    fn test_wasted_accumulates() {
        let mut arena = ClauseArena::new();
        let cr0 = arena.alloc(&[1, 2], false, 0);       // footprint: 1 + 2 = 3
        let cr1 = arena.alloc(&[3, 4, 5], true, 2);     // footprint: 1 + 2 + 3 = 6
        let _cr2 = arena.alloc(&[6], false, 0);          // footprint: 1 + 1 = 2

        arena.set_deleted(cr0);
        assert_eq!(arena.wasted(), 3);

        arena.set_deleted(cr1);
        assert_eq!(arena.wasted(), 3 + 6);
    }

    // ---- LBD ----

    #[test]
    fn test_set_lbd() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, -2, 3], true, 5);

        assert_eq!(arena.lbd(cr), 5);
        arena.set_lbd(cr, 2);
        assert_eq!(arena.lbd(cr), 2);
    }

    #[test]
    fn test_set_lbd_does_not_affect_literals() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[10, 20], true, 99);

        arena.set_lbd(cr, 1);

        assert_eq!(arena.lbd(cr), 1);
        assert_eq!(arena.lits(cr), &[10, 20]);
    }

    // ---- negative literals round-trip correctly ----

    #[test]
    fn test_negative_literal_roundtrip() {
        let mut arena = ClauseArena::new();
        let lits: Vec<i32> = vec![-1, -2, -100, i32::MIN + 1, i32::MAX];
        let cr = arena.alloc(&lits, false, 0);
        assert_eq!(arena.lits(cr), &lits[..]);
    }

    // ---- CREF_UNDEF ----

    #[test]
    fn test_cref_undef_is_max() {
        assert_eq!(CREF_UNDEF, u32::MAX);
    }

    // ---- with_capacity / default ----

    #[test]
    fn test_with_capacity() {
        let arena = ClauseArena::with_capacity(1024);
        assert_eq!(arena.wasted(), 0);
        // Just ensure it doesn't panic and starts empty
        assert_eq!(arena.buf.len(), 0);
    }

    #[test]
    fn test_default() {
        let arena = ClauseArena::default();
        assert_eq!(arena.wasted(), 0);
    }

    // ---- stress: many clauses ----

    #[test]
    fn test_many_clauses() {
        let mut arena = ClauseArena::new();
        let mut refs = Vec::new();

        for i in 0..1000 {
            let size = (i % 7) + 1; // 1..=7
            let lits: Vec<i32> = (0..size).map(|j| if j % 2 == 0 { i + j + 1 } else { -(i + j + 1) }).collect();
            let learnt = i % 3 == 0;
            let lbd = if learnt { (i % 5) as u32 } else { 0 };
            let cr = arena.alloc(&lits, learnt, lbd);
            refs.push((cr, lits, learnt, lbd));
        }

        // Verify all clauses
        for (cr, expected_lits, learnt, lbd) in &refs {
            assert_eq!(arena.lits(*cr), &expected_lits[..]);
            assert_eq!(arena.is_learnt(*cr), *learnt);
            if *learnt {
                assert_eq!(arena.lbd(*cr), *lbd);
            }
            assert!(!arena.is_deleted(*cr));
        }

        // Delete every other clause and verify wasted accounting
        let mut expected_wasted = 0usize;
        for (i, (cr, lits, learnt, _)) in refs.iter().enumerate() {
            if i % 2 == 0 {
                let footprint = 1 + if *learnt { 2 } else { 0 } + lits.len();
                expected_wasted += footprint;
                arena.set_deleted(*cr);
            }
        }
        assert_eq!(arena.wasted(), expected_wasted);

        // Non-deleted clauses should still be intact
        for (i, (cr, expected_lits, _, _)) in refs.iter().enumerate() {
            if i % 2 == 0 {
                assert!(arena.is_deleted(*cr));
            } else {
                assert!(!arena.is_deleted(*cr));
                assert_eq!(arena.lits(*cr), &expected_lits[..]);
            }
        }
    }

    // ---- deletion does not corrupt header flags ----

    #[test]
    fn test_delete_preserves_learnt_flag() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, 2, 3], true, 7);

        assert!(arena.is_learnt(cr));
        arena.set_deleted(cr);
        assert!(arena.is_learnt(cr));
        assert!(arena.is_deleted(cr));
        assert_eq!(arena.len(cr), 3);
    }

    #[test]
    fn test_delete_preserves_length() {
        let mut arena = ClauseArena::new();
        let cr = arena.alloc(&[1, 2, 3, 4, 5], false, 0);

        arena.set_deleted(cr);
        assert_eq!(arena.len(cr), 5);
    }
}
