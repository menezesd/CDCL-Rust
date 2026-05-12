use super::*;

impl CDCLSolver {
    #[cfg(feature = "stats")]
    pub(super) fn print_stats(&self, start_time: std::time::Instant) {
        let elapsed = start_time.elapsed().as_secs_f64();
        eprintln!("c");
        eprintln!("c ============================[ Solver Statistics ]============================");
        eprintln!("c Conflicts:      {:>12}  ({:.0}/sec)", self.conflicts, self.conflicts as f64 / elapsed);
        eprintln!("c Decisions:      {:>12}  ({:.0}/sec)", self.decisions, self.decisions as f64 / elapsed);
        eprintln!("c Propagations:   {:>12}  ({:.0}/sec)", self.propagations, self.propagations as f64 / elapsed);
        eprintln!("c Restarts:       {:>12}", self.restarts);
        eprintln!("c DB reductions:  {:>12}", self.reductions);
        eprintln!("c Learned alive:  {:>12}", self.num_learned_alive);
        eprintln!("c Time:           {:>11.2}s", elapsed);
        eprintln!("c ===========================================================================");
    }
}
