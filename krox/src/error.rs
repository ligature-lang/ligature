//! Error types for the Krox library.

use ligature_error::StandardError;
use ligature_eval::error::EvaluationError as EvalError;
use thiserror::Error;

/// Errors that can occur when using Krox.
#[derive(Error, Debug)]
pub enum Error {
    /// Error parsing a Ligature program.
    #[error("Parse error: {0}")]
    Parse(#[from] StandardError),

    /// Error evaluating a Ligature program.
    #[error("Evaluation error: {0}")]
    Evaluation(#[from] EvalError),

    /// Error executing a Ligature program via CLI.
    #[error("CLI execution error: {message}")]
    CliExecution {
        message: String,
        exit_code: Option<i32>,
        stderr: String,
    },

    /// Error making HTTP requests.
    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),

    /// Error serializing or deserializing JSON data.
    #[error("JSON serialization error: {0}")]
    JsonSerialization(#[from] serde_json::Error),

    /// Error serializing or deserializing YAML data.
    #[error("YAML serialization error: {0}")]
    YamlSerialization(#[from] serde_yaml::Error),

    /// Error reading or writing files.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// Error with file system operations.
    #[error("File system error: {message}")]
    FileSystem {
        message: String,
        path: Option<String>,
    },

    /// Error with caching operations.
    #[error("Cache error: {message}")]
    Cache {
        message: String,
        key: Option<String>,
    },

    /// Error with configuration.
    #[error("Configuration error: {message}")]
    Configuration {
        message: String,
        field: Option<String>,
    },

    /// Error with process execution.
    #[error("Process execution error: {message}")]
    ProcessExecution {
        message: String,
        command: Option<String>,
        exit_code: Option<i32>,
    },

    /// Error with ligature-cli binary.
    #[error("Ligature CLI error: {message}")]
    LigatureCli {
        message: String,
        path: Option<String>,
    },

    /// Error with HTTP server response.
    #[error("HTTP server error: {status} - {message}")]
    HttpServer {
        status: u16,
        message: String,
        body: Option<String>,
    },

    /// Error with timeout.
    #[error("Timeout error: {message}")]
    Timeout {
        message: String,
        duration: std::time::Duration,
    },

    /// Error with unsupported operation.
    #[error("Unsupported operation: {message}")]
    Unsupported { message: String, operation: String },

    /// Error with validation.
    #[error("Validation error: {message}")]
    Validation {
        message: String,
        field: Option<String>,
    },

    /// Generic error with a message.
    #[error("{message}")]
    Generic { message: String },
}

impl Error {
    /// Create a CLI execution error.
    pub fn cli_execution(message: String, exit_code: Option<i32>, stderr: String) -> Self {
        Self::CliExecution {
            message,
            exit_code,
            stderr,
        }
    }

    /// Create a file system error.
    pub fn file_system(message: String, path: Option<String>) -> Self {
        Self::FileSystem { message, path }
    }

    /// Create a cache error.
    pub fn cache(message: String, key: Option<String>) -> Self {
        Self::Cache { message, key }
    }

    /// Create a configuration error.
    pub fn configuration(message: String, field: Option<String>) -> Self {
        Self::Configuration { message, field }
    }

    /// Create a process execution error.
    pub fn process_execution(
        message: String,
        command: Option<String>,
        exit_code: Option<i32>,
    ) -> Self {
        Self::ProcessExecution {
            message,
            command,
            exit_code,
        }
    }

    /// Create a ligature CLI error.
    pub fn ligature_cli(message: String, path: Option<String>) -> Self {
        Self::LigatureCli { message, path }
    }

    /// Create an HTTP server error.
    pub fn http_server(status: u16, message: String, body: Option<String>) -> Self {
        Self::HttpServer {
            status,
            message,
            body,
        }
    }

    /// Create a timeout error.
    pub fn timeout(message: String, duration: std::time::Duration) -> Self {
        Self::Timeout { message, duration }
    }

    /// Create an unsupported operation error.
    pub fn unsupported(message: String, operation: String) -> Self {
        Self::Unsupported { message, operation }
    }

    /// Create a validation error.
    pub fn validation(message: String, field: Option<String>) -> Self {
        Self::Validation { message, field }
    }

    /// Create a generic error.
    pub fn generic(message: String) -> Self {
        Self::Generic { message }
    }
}

/// Result type for Krox operations.
pub type Result<T> = std::result::Result<T, Error>;
