//! Core error types for Baton formal verification.

use std::path::PathBuf;
use thiserror::Error;

/// Errors that can occur during Baton formal verification.
#[derive(Error, Debug, Clone)]
pub enum BatonError {
    #[error("Lean process failed to start: {0}")]
    ProcessStart(String),

    #[error("Lean process communication error: {0}")]
    Communication(String),

    #[error("Lean specification not found: {0}")]
    SpecificationNotFound(String),

    #[error("Lean verification failed: {0}")]
    VerificationFailed(String),

    #[error("Lean timeout: {0}")]
    Timeout(String),

    #[error("Lean parse error: {0}")]
    ParseError(String),

    #[error("Lean type error: {0}")]
    TypeError(String),

    #[error("Lean evaluation error: {0}")]
    EvaluationError(String),

    #[error("Lean serialization error: {0}")]
    SerializationError(String),

    #[error("Lean deserialization error: {0}")]
    DeserializationError(String),

    #[error("Lean specification compilation error: {0}")]
    CompilationError(String),

    #[error("Lean theorem proving error: {0}")]
    TheoremProvingError(String),

    #[error("Lean configuration error: {0}")]
    ConfigurationError(String),

    #[error("Lean version mismatch: expected {expected}, got {actual}")]
    VersionMismatch { expected: String, actual: String },

    #[error("Lean dependency error: {0}")]
    DependencyError(String),

    #[error("Lean file system error: {0}")]
    FileSystemError(String),

    #[error("Lean internal error: {0}")]
    InternalError(String),

    // Enhanced error types
    #[error("Lean cache error: {0}")]
    CacheError(String),

    #[error("Lean validation error: {0}")]
    ValidationError(String),

    #[error("Lean differential test error: {0}")]
    DifferentialTestError(String),

    #[error("Lean specification syntax error at {file}:{line}: {message}")]
    SpecificationSyntaxError {
        file: String,
        line: u32,
        message: String,
    },

    #[error("Lean specification type error at {file}:{line}: {message}")]
    SpecificationTypeError {
        file: String,
        line: u32,
        message: String,
    },

    #[error("Lean build system error: {0}")]
    BuildSystemError(String),

    #[error("Lean theorem proving timeout after {timeout}s: {theorem}")]
    TheoremProvingTimeout { timeout: u64, theorem: String },

    #[error("Lean specification dependency missing: {dependency}")]
    MissingDependency { dependency: String },

    #[error("Lean specification file not found: {path}")]
    SpecificationFileNotFound { path: PathBuf },

    #[error(
        "Lean specification build failed with {error_count} errors and {warning_count} warnings"
    )]
    SpecificationBuildFailed {
        error_count: usize,
        warning_count: usize,
        errors: Vec<String>,
        warnings: Vec<String>,
    },

    #[error("Lean process killed: {reason}")]
    ProcessKilled { reason: String },

    #[error("Lean protocol error: {message}")]
    ProtocolError { message: String },

    #[error("Lean verification context error: {context}")]
    VerificationContextError { context: String },
}

/// Result type for Baton operations.
pub type BatonResult<T> = Result<T, BatonError>; 