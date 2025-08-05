//! Error types for XDG configuration operations.

use thiserror::Error;

/// Errors that can occur during XDG configuration operations.
#[derive(Error, Debug)]
pub enum XdgError {
    /// Failed to determine XDG base directories.
    #[error("Failed to determine XDG base directories: {0}")]
    XdgBaseDirError(#[from] xdg::BaseDirectoriesError),

    /// Failed to create a directory.
    #[error("Failed to create directory '{path}': {source}")]
    CreateDirectoryError {
        path: String,
        #[source]
        source: std::io::Error,
    },

    /// Failed to read a file.
    #[error("Failed to read file '{path}': {source}")]
    ReadFileError {
        path: String,
        #[source]
        source: std::io::Error,
    },

    /// Failed to write a file.
    #[error("Failed to write file '{path}': {source}")]
    WriteFileError {
        path: String,
        #[source]
        source: std::io::Error,
    },

    /// Failed to serialize configuration.
    #[error("Failed to serialize configuration: {0}")]
    SerializationError(serde_json::Error),

    /// Failed to deserialize configuration.
    #[error("Failed to deserialize configuration: {0}")]
    DeserializationError(serde_json::Error),

    /// Configuration file not found.
    #[error("Configuration file not found: {0}")]
    ConfigNotFound(String),

    /// Invalid configuration format.
    #[error("Invalid configuration format: {0}")]
    InvalidConfig(String),

    /// Component name is invalid.
    #[error("Invalid component name '{name}': {reason}")]
    InvalidComponentName { name: String, reason: String },
}

/// Result type for XDG configuration operations.
pub type Result<T> = std::result::Result<T, XdgError>;
