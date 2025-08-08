//! Core types and traits for Baton formal verification.
//!
//! This crate provides the foundational types and traits used across
//! the Baton formal verification system.

use std::collections::HashMap;
use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Request priority levels for verification operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RequestPriority {
    Low,
    Normal,
    High,
    Critical,
}

// These types are now defined in baton-protocol

/// Coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageInfo {
    pub lines_covered: usize,
    pub lines_total: usize,
    pub branches_covered: usize,
    pub branches_total: usize,
    pub functions_covered: usize,
    pub functions_total: usize,
}

/// Performance comparison data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceComparison {
    pub rust_time: Duration,
    pub lean_time: Duration,
    pub memory_usage: MemoryUsage,
    pub cpu_usage: f64,
}

/// Memory usage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryUsage {
    pub peak_memory: usize,
    pub average_memory: usize,
    pub memory_leaks: bool,
}

/// Dependency information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyInfo {
    pub name: String,
    pub version: String,
    pub path: String,
    pub dependencies: Vec<String>,
}

/// Theorem information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremInfo {
    pub name: String,
    pub statement: String,
    pub proof_status: ProofStatus,
    pub dependencies: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// Proof status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProofStatus {
    Pending,
    InProgress,
    Completed,
    Failed,
    Timeout,
}

// VerificationContext is now defined in baton-protocol

// VerificationContext implementation moved to baton-protocol

// DetailedComparison struct moved to baton-protocol

// Difference struct moved to baton-protocol

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        CoverageInfo, DependencyInfo, MemoryUsage, PerformanceComparison, ProofStatus,
        RequestPriority, TheoremInfo,
    };
}
