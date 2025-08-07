//! Error types for Baton formal verification.
//!
//! This crate provides comprehensive error handling for the Baton
//! formal verification system.

pub mod error;
pub mod context;

pub use error::{BatonError, BatonResult};
pub use context::{ErrorContext, BatonErrorWithContext, BatonResultWithContext};

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        BatonError, BatonErrorWithContext, BatonResult, BatonResultWithContext, ErrorContext,
    };
}
