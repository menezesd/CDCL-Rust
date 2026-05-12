/// Position-indexed binary heap for VSIDS variable ordering.
/// Inspired by MiniSAT's Heap class (MIT licensed).
///
/// Unlike BinaryHeap, this supports O(log n) update-in-place for
/// activity changes and O(1) membership testing.
pub struct VarHeap {
    heap: Vec<i32>,          // heap[i] = variable at position i
    indices: Vec<i32>,       // indices[var] = position in heap, or -1
    pub activity: Vec<f64>,  // activity scores (mirrored from solver)
}

impl VarHeap {
    pub fn new(num_vars: usize) -> Self {
        VarHeap {
            heap: Vec::with_capacity(num_vars),
            indices: vec![-1; num_vars + 1],
            activity: Vec::new(), // set via set_activity
        }
    }

    /// Set the activity array reference (called once, or when activity is rescaled).
    pub fn set_activity(&mut self, activity: &[f64]) {
        self.activity = activity.to_vec();
    }

    /// Update activity for a variable and fix heap position.
    pub fn update_activity(&mut self, var: i32, new_activity: f64) {
        let v = var as usize;
        self.activity[v] = new_activity;
        if self.in_heap(var) {
            let pos = self.indices[v] as usize;
            self.percolate_up(pos);
            self.percolate_down(pos);
        }
    }

    /// Rebuild activity array from external source.
    pub fn sync_activity(&mut self, activity: &[f64]) {
        self.activity = activity.to_vec();
        // Rebuild heap ordering
        self.build_heap();
    }

    pub fn in_heap(&self, var: i32) -> bool {
        let v = var as usize;
        v < self.indices.len() && self.indices[v] >= 0
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn insert(&mut self, var: i32) {
        let v = var as usize;
        if self.in_heap(var) { return; }
        while self.indices.len() <= v { self.indices.push(-1); }
        while self.activity.len() <= v { self.activity.push(0.0); }
        self.indices[v] = self.heap.len() as i32;
        self.heap.push(var);
        self.percolate_up(self.heap.len() - 1);
    }

    /// Remove and return the variable with highest activity.
    pub fn remove_min(&mut self) -> Option<i32> {
        if self.heap.is_empty() { return None; }
        let x = self.heap[0];
        let last = *self.heap.last().unwrap();
        self.heap[0] = last;
        self.indices[last as usize] = 0;
        self.indices[x as usize] = -1;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0);
        }
        Some(x)
    }

    /// Increase priority (activity went up) — percolate up.
    pub fn decrease(&mut self, var: i32) {
        if !self.in_heap(var) { return; }
        let pos = self.indices[var as usize] as usize;
        self.percolate_up(pos);
    }

    pub fn build_heap(&mut self) {
        if self.heap.len() <= 1 { return; }
        for i in (0..self.heap.len() / 2).rev() {
            self.percolate_down(i);
        }
    }

    #[inline]
    fn lt(&self, a: i32, b: i32) -> bool {
        // Higher activity = higher priority (max-heap)
        // Tie-break by lower variable index for determinism
        let aa = self.activity[a as usize];
        let ab = self.activity[b as usize];
        aa > ab || (aa == ab && a < b)
    }

    fn percolate_up(&mut self, mut i: usize) {
        let x = self.heap[i];
        while i > 0 {
            let p = (i - 1) >> 1;
            if !self.lt(x, self.heap[p]) { break; }
            self.heap[i] = self.heap[p];
            self.indices[self.heap[p] as usize] = i as i32;
            i = p;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as i32;
    }

    fn percolate_down(&mut self, mut i: usize) {
        let x = self.heap[i];
        loop {
            let left = i * 2 + 1;
            if left >= self.heap.len() { break; }
            let right = left + 1;
            let child = if right < self.heap.len() && self.lt(self.heap[right], self.heap[left]) {
                right
            } else {
                left
            };
            if !self.lt(self.heap[child], x) { break; }
            self.heap[i] = self.heap[child];
            self.indices[self.heap[i] as usize] = i as i32;
            i = child;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as i32;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_heap() {
        let mut h = VarHeap::new(5);
        h.activity = vec![0.0, 3.0, 1.0, 5.0, 2.0, 4.0];
        for v in 1..=5 { h.insert(v); }
        assert_eq!(h.remove_min(), Some(3)); // activity 5.0
        assert_eq!(h.remove_min(), Some(5)); // activity 4.0
        assert_eq!(h.remove_min(), Some(1)); // activity 3.0
        assert_eq!(h.remove_min(), Some(4)); // activity 2.0
        assert_eq!(h.remove_min(), Some(2)); // activity 1.0
        assert!(h.remove_min().is_none());
    }

    #[test]
    fn test_update_activity() {
        let mut h = VarHeap::new(3);
        h.activity = vec![0.0, 1.0, 2.0, 3.0];
        for v in 1..=3 { h.insert(v); }
        // Var 3 has highest, should come out first
        assert_eq!(h.remove_min(), Some(3));
        // Re-insert var 3 with low activity
        h.activity[3] = 0.5;
        h.insert(3);
        assert_eq!(h.remove_min(), Some(2)); // activity 2.0
        assert_eq!(h.remove_min(), Some(1)); // activity 1.0
        assert_eq!(h.remove_min(), Some(3)); // activity 0.5
    }

    #[test]
    fn test_in_heap() {
        let mut h = VarHeap::new(3);
        h.activity = vec![0.0, 1.0, 2.0, 3.0];
        assert!(!h.in_heap(1));
        h.insert(1);
        assert!(h.in_heap(1));
        h.remove_min();
        assert!(!h.in_heap(1));
    }

    #[test]
    fn test_decrease_promotes_variable() {
        let mut h = VarHeap::new(3);
        h.activity = vec![0.0, 1.0, 2.0, 3.0];
        for v in 1..=3 { h.insert(v); }
        // Boost var 1's activity above var 3
        h.activity[1] = 10.0;
        h.decrease(1);
        assert_eq!(h.remove_min(), Some(1)); // now highest
    }

    #[test]
    fn test_insert_idempotent() {
        let mut h = VarHeap::new(3);
        h.activity = vec![0.0, 1.0, 2.0, 3.0];
        h.insert(2);
        h.insert(2); // duplicate insert should be no-op
        assert!(h.in_heap(2));
        assert_eq!(h.remove_min(), Some(2));
        assert!(h.remove_min().is_none());
    }

    #[test]
    fn test_empty_heap() {
        let h = VarHeap::new(0);
        assert!(h.is_empty());
    }

    #[test]
    fn test_sync_activity_rebuilds_order() {
        let mut h = VarHeap::new(4);
        h.activity = vec![0.0, 4.0, 3.0, 2.0, 1.0];
        for v in 1..=4 { h.insert(v); }
        // Reverse all activities
        h.sync_activity(&[0.0, 1.0, 2.0, 3.0, 4.0]);
        assert_eq!(h.remove_min(), Some(4)); // now highest (4.0)
        assert_eq!(h.remove_min(), Some(3)); // 3.0
    }

    #[test]
    fn test_large_heap() {
        let n = 1000;
        let mut h = VarHeap::new(n);
        let mut act = vec![0.0; n + 1];
        for (i, val) in act.iter_mut().enumerate().take(n + 1).skip(1) { *val = i as f64; }
        h.activity = act;
        for v in 1..=n { h.insert(v as i32); }
        // Should come out in descending order
        let mut prev = f64::MAX;
        for _ in 0..n {
            let v = h.remove_min().unwrap();
            let a = v as f64;
            // a should equal n, n-1, n-2, ...
            assert!(a <= prev);
            prev = a;
        }
    }
}
