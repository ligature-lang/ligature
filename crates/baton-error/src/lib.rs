//! Error types for Baton formal verification.
//!
//! This crate provides comprehensive error handling for the Baton
//! formal verification system.

pub mod context;
pub mod error;

pub use context::{BatonErrorWithContext, BatonResultWithContext, ErrorContext};
pub use error::{BatonError, BatonResult};

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        BatonError, BatonErrorWithContext, BatonResult, BatonResultWithContext, ErrorContext,
    };
}
