//! Type definitions for specification management.

use baton_engine_plugin::prelude::*;
use serde::{Deserialize, Serialize};

/// Specification file information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecFileInfo {
    /// File path
    pub path: String,
    /// File content hash
    pub hash: String,
    /// Last modified timestamp
    pub modified: u64,
    /// Whether file is valid
    pub valid: bool,
    /// Compilation errors if any
    pub errors: Vec<String>,
    /// Compilation warnings if any
    pub warnings: Vec<String>,
    /// File dependencies
    pub dependencies: Vec<String>,
    /// File size in bytes
    pub size: u64,
    /// File type
    pub file_type: SpecFileType,
}

/// Specification file type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpecFileType {
    /// Main specification file
    Main,
    /// Type system specification
    TypeSystem,
    /// Operational semantics specification
    OperationalSemantics,
    /// Configuration language specification
    ConfigurationLanguage,
    /// Test specification
    Test,
    /// Documentation
    Documentation,
    /// Build configuration
    BuildConfig,
    /// Other
    Other,
}

/// Build status information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildStatus {
    /// Whether build was successful
    pub success: bool,
    /// Build errors
    pub errors: Vec<String>,
    /// Build warnings
    pub warnings: Vec<String>,
    /// Build time in milliseconds
    pub build_time: u64,
    /// Dependencies
    pub dependencies: Vec<String>,
    /// Built targets
    pub built_targets: Vec<String>,
    /// Build artifacts
    pub artifacts: Vec<String>,
    /// Build configuration used
    pub build_config: BuildConfig,
}

/// Validation result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Whether validation was successful
    pub success: bool,
    /// Validation errors
    pub errors: Vec<ValidationError>,
    /// Validation warnings
    pub warnings: Vec<ValidationWarning>,
    /// Validation time in milliseconds
    pub validation_time: u64,
    /// Files validated
    pub files_validated: Vec<String>,
}

/// Validation error.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationError {
    /// Error type
    pub error_type: ValidationErrorType,
    /// File path
    pub file: String,
    /// Line number
    pub line: Option<u32>,
    /// Column number
    pub column: Option<u32>,
    /// Error message
    pub message: String,
    /// Error severity
    pub severity: ErrorSeverity,
}

/// Validation warning.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationWarning {
    /// Warning type
    pub warning_type: ValidationWarningType,
    /// File path
    pub file: String,
    /// Line number
    pub line: Option<u32>,
    /// Column number
    pub column: Option<u32>,
    /// Warning message
    pub message: String,
}

/// Validation error types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationErrorType {
    Syntax,
    Type,
    Semantics,
    Dependency,
    Build,
    Configuration,
}

/// Validation warning types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationWarningType {
    Deprecated,
    Unused,
    Performance,
    Style,
    Documentation,
}

/// Error severity levels.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// Specification statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecStatistics {
    /// Total number of files
    pub total_files: usize,
    /// Total size in bytes
    pub total_size: u64,
    /// Number of valid files
    pub valid_files: usize,
    /// Total number of errors
    pub error_count: usize,
    /// Total number of warnings
    pub warning_count: usize,
    /// File types present
    pub file_types: Vec<SpecFileType>,
}
