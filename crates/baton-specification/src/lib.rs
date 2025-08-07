//! Specification management for Baton formal verification.
//!
//! This crate provides specification management for the Baton
//! formal verification system.

pub mod types;
pub mod specification;

pub use specification::Specification;
pub use types::*;

// Legacy type aliases for backward compatibility
pub type LeanSpecification = Specification;

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        BuildStatus,
        ErrorSeverity,
        // Legacy exports
        LeanSpecification,
        SpecFileInfo,
        SpecFileType,
        SpecStatistics,
        Specification,
        ValidationError,
        ValidationErrorType,
        ValidationResult,
        ValidationWarning,
        ValidationWarningType,
    };
    pub use baton_engine_plugin::prelude::*;
}
