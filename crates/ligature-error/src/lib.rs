//! Standardized error handling for Ligature crates.
//!
//! This crate provides a unified approach to error handling across all Ligature crates,
//! with consistent error types, error codes, and error reporting.

pub mod context;
pub mod error;
pub mod reporter;
pub mod result;

pub use context::ErrorContextBuilder;
pub use error::StandardError;
/// Re-export common error handling types for convenience.
pub use ligature_ast::{ErrorCode, LigatureError, LigatureResult};
pub use reporter::{ErrorReportConfig, StandardErrorReporter};
pub use result::{AnyhowResultExt, LigatureResultExt, ResultExt, StandardResult, UnifiedResult};
