//! Memory tracking utilities for the Ligature evaluation engine.
//!
//! This module provides cross-platform memory usage tracking for
//! performance benchmarking and optimization.

use std::process;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MemoryError {
    #[error("Failed to get process memory information: {0}")]
    ProcessError(String),
    #[error("Unsupported platform for memory tracking")]
    UnsupportedPlatform,
}

/// Memory usage statistics for a process.
#[derive(Debug, Clone)]
pub struct MemoryStats {
    /// Resident Set Size (RSS) in bytes - physical memory used
    pub rss: usize,
    /// Virtual Memory Size (VMS) in bytes - total virtual memory
    pub vms: usize,
    /// Peak memory usage in bytes
    pub peak: usize,
    /// Memory usage delta from baseline
    pub delta: Option<isize>,
}

/// Memory tracker for monitoring process memory usage.
pub struct MemoryTracker {
    baseline: Option<MemoryStats>,
    peak_memory: usize,
}

impl MemoryTracker {
    /// Create a new memory tracker.
    pub fn new() -> Self {
        Self {
            baseline: None,
            peak_memory: 0,
        }
    }

    /// Set the baseline memory usage for delta calculations.
    pub fn set_baseline(&mut self) -> Result<(), MemoryError> {
        self.baseline = Some(get_current_memory_stats()?);
        self.peak_memory = self.baseline.as_ref().unwrap().rss;
        Ok(())
    }

    /// Get the current memory usage and update peak tracking.
    pub fn get_current_usage(&mut self) -> Result<MemoryStats, MemoryError> {
        let current = get_current_memory_stats()?;

        // Update peak memory
        self.peak_memory = self.peak_memory.max(current.rss);

        // Calculate delta from baseline if available
        let delta = self
            .baseline
            .as_ref()
            .map(|baseline| current.rss as isize - baseline.rss as isize);

        Ok(MemoryStats {
            rss: current.rss,
            vms: current.vms,
            peak: self.peak_memory,
            delta,
        })
    }

    /// Get the peak memory usage since baseline was set.
    pub fn get_peak_usage(&self) -> Result<MemoryStats, MemoryError> {
        let current = get_current_memory_stats()?;

        let delta = self
            .baseline
            .as_ref()
            .map(|baseline| self.peak_memory as isize - baseline.rss as isize);

        Ok(MemoryStats {
            rss: current.rss,
            vms: current.vms,
            peak: self.peak_memory,
            delta,
        })
    }

    /// Reset the memory tracker.
    pub fn reset(&mut self) {
        self.baseline = None;
        self.peak_memory = 0;
    }
}
impl Default for MemoryTracker {
    fn default() -> Self {
        Self::new()
    }
}
/// Get current memory usage statistics for the current process.
pub fn get_current_memory_stats() -> Result<MemoryStats, MemoryError> {
    use sysinfo::{Pid, ProcessExt, SystemExt};

    let mut sys = sysinfo::System::new();
    sys.refresh_process(Pid::from(process::id() as usize));

    if let Some(process) = sys.process(Pid::from(process::id() as usize)) {
        let rss = process.memory() * 1024; // Convert KB to bytes
        let vms = process.virtual_memory() * 1024; // Convert KB to bytes

        Ok(MemoryStats {
            rss: rss as usize,
            vms: vms as usize,
            peak: rss as usize, // sysinfo doesn't provide peak, use current as approximation
            delta: None,
        })
    } else {
        Err(MemoryError::ProcessError(
            "Could not find current process".to_string(),
        ))
    }
}

/// Get a simple memory usage measurement in bytes.
/// This is a fallback that works on most platforms.
pub fn get_simple_memory_usage() -> Result<usize, MemoryError> {
    let stats = get_current_memory_stats()?;
    Ok(stats.rss)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_tracker_creation() {
        let tracker = MemoryTracker::new();
        assert!(tracker.baseline.is_none());
        assert_eq!(tracker.peak_memory, 0);
    }

    #[test]
    fn test_memory_tracker_baseline() {
        let mut tracker = MemoryTracker::new();
        assert!(tracker.set_baseline().is_ok());
        assert!(tracker.baseline.is_some());
    }

    #[test]
    fn test_memory_tracker_reset() {
        let mut tracker = MemoryTracker::new();
        tracker.set_baseline().unwrap();
        tracker.reset();
        assert!(tracker.baseline.is_none());
        assert_eq!(tracker.peak_memory, 0);
    }

    #[test]
    fn test_get_simple_memory_usage() {
        let result = get_simple_memory_usage();
        assert!(result.is_ok());
        assert!(result.unwrap() > 0);
    }

    #[test]
    fn test_get_current_memory_stats() {
        let result = get_current_memory_stats();
        assert!(result.is_ok());
        let stats = result.unwrap();
        assert!(stats.rss > 0);
        assert!(stats.vms > 0);
    }
}
