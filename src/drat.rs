//! DRAT (Deletion Resolution Asymmetric Tautology) proof logging.
//!
//! When enabled, the solver logs every learned clause addition and deletion
//! to a proof file. An external checker like `drat-trim` can then verify
//! that an UNSAT result is correct.
//!
//! # Format
//!
//! The DRAT proof format uses one line per operation:
//! - Addition: `lit1 lit2 ... 0`
//! - Deletion: `d lit1 lit2 ... 0`
//!
//! Literals use DIMACS sign convention (positive = true, negative = negated).
//!
//! # Usage
//!
//! ```no_run
//! use cdcl_sat::drat::DratLogger;
//!
//! let mut logger = DratLogger::new("proof.drat").unwrap();
//! logger.add_clause(&[1, -2, 3]);   // learned clause
//! logger.delete_clause(&[-1, 4]);    // deleted during reduction
//! logger.flush();
//! ```

use std::io::{self, BufWriter, Write};
use std::fs::File;

/// A DRAT proof logger that writes to a file or a byte buffer.
pub struct DratLogger {
    writer: Box<dyn Write>,
    enabled: bool,
    additions: u64,
    deletions: u64,
}

impl DratLogger {
    /// Creates a logger that writes to the given file path.
    pub fn new(path: &str) -> io::Result<Self> {
        let file = File::create(path)?;
        Ok(DratLogger {
            writer: Box::new(BufWriter::new(file)),
            enabled: true,
            additions: 0,
            deletions: 0,
        })
    }

    /// Creates a logger that writes to an in-memory buffer (for testing).
    pub fn in_memory() -> Self {
        DratLogger {
            writer: Box::new(Vec::<u8>::new()),
            enabled: true,
            additions: 0,
            deletions: 0,
        }
    }

    /// Creates a disabled (no-op) logger.
    pub fn disabled() -> Self {
        DratLogger {
            writer: Box::new(io::sink()),
            enabled: false,
            additions: 0,
            deletions: 0,
        }
    }

    /// Returns true if this logger is actually writing proof output.
    #[inline]
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Logs a clause addition (learned clause).
    #[inline]
    pub fn add_clause(&mut self, lits: &[i32]) {
        if !self.enabled { return; }
        self.additions += 1;
        self.write_clause(lits);
    }

    /// Logs a clause deletion (during clause database reduction).
    #[inline]
    pub fn delete_clause(&mut self, lits: &[i32]) {
        if !self.enabled { return; }
        self.deletions += 1;
        let _ = self.writer.write_all(b"d ");
        self.write_clause(lits);
    }

    /// Flushes the proof output buffer.
    pub fn flush(&mut self) {
        let _ = self.writer.flush();
    }

    /// Returns the number of clause additions logged.
    pub fn num_additions(&self) -> u64 { self.additions }

    /// Returns the number of clause deletions logged.
    pub fn num_deletions(&self) -> u64 { self.deletions }

    fn write_clause(&mut self, lits: &[i32]) {
        // Write each literal followed by space, then "0\n"
        let mut buf = Vec::with_capacity(lits.len() * 5 + 3);
        for &lit in lits {
            let s = lit.to_string();
            buf.extend_from_slice(s.as_bytes());
            buf.push(b' ');
        }
        buf.extend_from_slice(b"0\n");
        let _ = self.writer.write_all(&buf);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disabled_logger() {
        let mut logger = DratLogger::disabled();
        assert!(!logger.is_enabled());
        logger.add_clause(&[1, -2, 3]);
        logger.delete_clause(&[4, 5]);
        assert_eq!(logger.num_additions(), 0);
        assert_eq!(logger.num_deletions(), 0);
    }

    #[test]
    fn test_in_memory_logging() {
        let mut logger = DratLogger::in_memory();
        assert!(logger.is_enabled());
        logger.add_clause(&[1, -2, 3]);
        logger.add_clause(&[-4, 5]);
        logger.delete_clause(&[1, -2, 3]);
        assert_eq!(logger.num_additions(), 2);
        assert_eq!(logger.num_deletions(), 1);
    }

    #[test]
    fn test_file_logging() {
        let path = "/tmp/test_drat_proof.drat";
        {
            let mut logger = DratLogger::new(path).unwrap();
            logger.add_clause(&[1, -2, 3]);
            logger.add_clause(&[-4]);
            logger.delete_clause(&[1, -2, 3]);
            logger.flush();
        }
        let content = std::fs::read_to_string(path).unwrap();
        let lines: Vec<&str> = content.lines().collect();
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0], "1 -2 3 0");
        assert_eq!(lines[1], "-4 0");
        assert_eq!(lines[2], "d 1 -2 3 0");
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_empty_clause() {
        let mut logger = DratLogger::in_memory();
        logger.add_clause(&[]);
        assert_eq!(logger.num_additions(), 1);
    }

    #[test]
    fn test_unit_clause() {
        let path = "/tmp/test_drat_unit.drat";
        {
            let mut logger = DratLogger::new(path).unwrap();
            logger.add_clause(&[42]);
            logger.flush();
        }
        let content = std::fs::read_to_string(path).unwrap();
        assert_eq!(content.trim(), "42 0");
        std::fs::remove_file(path).ok();
    }
}
