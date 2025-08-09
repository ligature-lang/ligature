//! Standardized error types for Ligature crates.

use ligature_ast::{ErrorCode, LigatureError, Span};
use thiserror::Error;

/// Standardized error type for Ligature crates.
#[derive(Error, Debug)]
pub enum StandardError {
    /// Ligature-specific errors from the AST.
    #[error("{0}")]
    Ligature(#[from] LigatureError),

    /// IO errors.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// Serialization errors.
    #[error("Serialization error: {0}")]
    Serialization(String),

    /// Deserialization errors.
    #[error("Deserialization error: {0}")]
    Deserialization(String),

    /// Configuration errors.
    #[error("Configuration error: {0}")]
    Configuration(String),

    /// Validation errors.
    #[error("Validation error: {0}")]
    Validation(String),

    /// Plugin errors.
    #[error("Plugin error: {0}")]
    Plugin(String),

    /// Network errors.
    #[error("Network error: {0}")]
    Network(String),

    /// Timeout errors.
    #[error("Timeout error: {0}")]
    Timeout(String),

    /// Resource not found errors.
    #[error("Not found: {0}")]
    NotFound(String),

    /// Permission errors.
    #[error("Permission denied: {0}")]
    Permission(String),

    /// Internal errors.
    #[error("Internal error: {0}")]
    Internal(String),

    /// Unsupported operation errors.
    #[error("Unsupported operation: {0}")]
    Unsupported(String),

    /// Invalid argument errors.
    #[error("Invalid argument: {0}")]
    InvalidArgument(String),
}

impl StandardError {
    /// Create a new IO error with context.
    pub fn io_error(source: std::io::Error, context: impl Into<String>) -> Self {
        StandardError::Io(source).with_context(context)
    }

    /// Create a new serialization error.
    pub fn serialization_error(message: impl Into<String>) -> Self {
        StandardError::Serialization(message.into())
    }

    /// Create a new deserialization error.
    pub fn deserialization_error(message: impl Into<String>) -> Self {
        StandardError::Deserialization(message.into())
    }

    /// Create a new configuration error.
    pub fn configuration_error(message: impl Into<String>) -> Self {
        StandardError::Configuration(message.into())
    }

    /// Create a new validation error.
    pub fn validation_error(message: impl Into<String>) -> Self {
        StandardError::Validation(message.into())
    }

    /// Create a new plugin error.
    pub fn plugin_error(message: impl Into<String>) -> Self {
        StandardError::Plugin(message.into())
    }

    /// Create a new network error.
    pub fn network_error(message: impl Into<String>) -> Self {
        StandardError::Network(message.into())
    }

    /// Create a new timeout error.
    pub fn timeout_error(message: impl Into<String>) -> Self {
        StandardError::Timeout(message.into())
    }

    /// Create a new not found error.
    pub fn not_found_error(resource: impl Into<String>) -> Self {
        StandardError::NotFound(resource.into())
    }

    /// Create a new permission error.
    pub fn permission_error(resource: impl Into<String>) -> Self {
        StandardError::Permission(resource.into())
    }

    /// Create a new internal error.
    pub fn internal_error(message: impl Into<String>) -> Self {
        StandardError::Internal(message.into())
    }

    /// Create a new unsupported operation error.
    pub fn unsupported_error(operation: impl Into<String>) -> Self {
        StandardError::Unsupported(operation.into())
    }

    /// Create a new invalid argument error.
    pub fn invalid_argument_error(argument: impl Into<String>) -> Self {
        StandardError::InvalidArgument(argument.into())
    }

    /// Add context to this error.
    pub fn with_context(self, context: impl Into<String>) -> Self {
        match self {
            StandardError::Ligature(err) => StandardError::Ligature(err),
            StandardError::Io(err) => StandardError::Io(err),
            StandardError::Serialization(msg) => {
                StandardError::Serialization(format!("{}: {}", context.into(), msg))
            }
            StandardError::Deserialization(msg) => {
                StandardError::Deserialization(format!("{}: {}", context.into(), msg))
            }
            StandardError::Configuration(msg) => {
                StandardError::Configuration(format!("{}: {}", context.into(), msg))
            }
            StandardError::Validation(msg) => {
                StandardError::Validation(format!("{}: {}", context.into(), msg))
            }
            StandardError::Plugin(msg) => {
                StandardError::Plugin(format!("{}: {}", context.into(), msg))
            }
            StandardError::Network(msg) => {
                StandardError::Network(format!("{}: {}", context.into(), msg))
            }
            StandardError::Timeout(msg) => {
                StandardError::Timeout(format!("{}: {}", context.into(), msg))
            }
            StandardError::NotFound(resource) => {
                StandardError::NotFound(format!("{}: {}", context.into(), resource))
            }
            StandardError::Permission(resource) => {
                StandardError::Permission(format!("{}: {}", context.into(), resource))
            }
            StandardError::Internal(msg) => {
                StandardError::Internal(format!("{}: {}", context.into(), msg))
            }
            StandardError::Unsupported(operation) => {
                StandardError::Unsupported(format!("{}: {}", context.into(), operation))
            }
            StandardError::InvalidArgument(argument) => {
                StandardError::InvalidArgument(format!("{}: {}", context.into(), argument))
            }
        }
    }

    /// Get the error code if this is a Ligature error.
    pub fn error_code(&self) -> Option<ErrorCode> {
        match self {
            StandardError::Ligature(err) => Some(err.code()),
            _ => None,
        }
    }

    /// Get the span if this is a Ligature error.
    pub fn span(&self) -> Option<Span> {
        match self {
            StandardError::Ligature(err) => err.span(),
            _ => None,
        }
    }

    /// Check if this is a recoverable error.
    pub fn is_recoverable(&self) -> bool {
        match self {
            StandardError::Ligature(err) => matches!(
                err.code(),
                ErrorCode::E1001 | ErrorCode::E1002 | ErrorCode::E1003 | ErrorCode::E1004
            ),
            StandardError::Validation(_) | StandardError::Configuration(_) => true,
            StandardError::NotFound(_) | StandardError::Permission(_) => false,
            _ => false,
        }
    }

    /// Get user-friendly suggestions for fixing this error.
    pub fn get_suggestions(&self) -> Vec<String> {
        match self {
            StandardError::Ligature(err) => err.get_suggestions(),
            StandardError::Io(_) => vec![
                "Check if the file exists and is accessible".to_string(),
                "Verify you have the necessary permissions".to_string(),
                "Ensure the file path is correct".to_string(),
            ],
            StandardError::Serialization(_) => vec![
                "Check the data format".to_string(),
                "Verify all required fields are present".to_string(),
                "Ensure the data is valid".to_string(),
            ],
            StandardError::Deserialization(_) => vec![
                "Check the input format".to_string(),
                "Verify the data is well-formed".to_string(),
                "Ensure all required fields are present".to_string(),
            ],
            StandardError::Configuration(_) => vec![
                "Check the configuration file format".to_string(),
                "Verify all required settings are present".to_string(),
                "Ensure configuration values are valid".to_string(),
            ],
            StandardError::Validation(_) => vec![
                "Check the input data".to_string(),
                "Verify all constraints are satisfied".to_string(),
                "Ensure the data meets the requirements".to_string(),
            ],
            StandardError::Plugin(_) => vec![
                "Check if the plugin is installed".to_string(),
                "Verify the plugin version is compatible".to_string(),
                "Ensure the plugin configuration is correct".to_string(),
            ],
            StandardError::Network(_) => vec![
                "Check your internet connection".to_string(),
                "Verify the server is accessible".to_string(),
                "Ensure the URL is correct".to_string(),
            ],
            StandardError::Timeout(_) => vec![
                "Try again later".to_string(),
                "Check if the service is overloaded".to_string(),
                "Consider increasing timeout settings".to_string(),
            ],
            StandardError::NotFound(_) => vec![
                "Check if the resource exists".to_string(),
                "Verify the path or identifier is correct".to_string(),
                "Ensure the resource is accessible".to_string(),
            ],
            StandardError::Permission(_) => vec![
                "Check your permissions".to_string(),
                "Verify you have the necessary access rights".to_string(),
                "Contact your administrator if needed".to_string(),
            ],
            StandardError::Internal(_) => vec![
                "This is an internal error".to_string(),
                "Please report this issue".to_string(),
                "Check the logs for more details".to_string(),
            ],
            StandardError::Unsupported(_) => vec![
                "Check if this feature is available".to_string(),
                "Verify your version supports this operation".to_string(),
                "Consider upgrading if needed".to_string(),
            ],
            StandardError::InvalidArgument(_) => vec![
                "Check the argument values".to_string(),
                "Verify the argument types are correct".to_string(),
                "Ensure all required arguments are provided".to_string(),
            ],
        }
    }
}

impl From<anyhow::Error> for StandardError {
    fn from(err: anyhow::Error) -> Self {
        StandardError::Internal(err.to_string())
    }
}

impl From<serde_json::Error> for StandardError {
    fn from(err: serde_json::Error) -> Self {
        StandardError::Deserialization(err.to_string())
    }
}

impl From<toml::de::Error> for StandardError {
    fn from(err: toml::de::Error) -> Self {
        StandardError::Deserialization(err.to_string())
    }
}

impl From<toml::ser::Error> for StandardError {
    fn from(err: toml::ser::Error) -> Self {
        StandardError::Serialization(err.to_string())
    }
}
