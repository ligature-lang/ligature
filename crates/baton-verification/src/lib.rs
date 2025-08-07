//! Verification engine for Baton formal verification.
//!
//! This crate provides the verification engine for coordinating
//! Lean verification operations.

pub mod engine;
pub mod types;

pub use types::*;

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        EngineHealthStatus, RetryConfig, VerificationConfig, VerificationEngine,
        VerificationMetrics,
    };
}
