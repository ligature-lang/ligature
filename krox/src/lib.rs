//! Krox - Client SDKs for invoking Ligature programs as side effects
//!
//! Krox provides a comprehensive set of client SDKs that allow you to invoke
//! Ligature programs from various languages and platforms, treating them as
//! side effects in your applications.
//!
//! ## Features
//!
//! - **Native Execution**: Execute Ligature programs directly using the ligature-cli
//! - **HTTP Execution**: Execute programs via HTTP endpoints
//! - **Multiple Language SDKs**: Rust, Python, Node.js, Java, and Go bindings
//! - **Caching**: Intelligent caching of program results
//! - **Error Handling**: Comprehensive error handling and reporting
//! - **Async Support**: Full async/await support for all operations
//!
//! ## Quick Start
//!
//! ```no_run
//! use krox::{Client, ExecutionMode};
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Create a client
//!     let mut client = Client::new(ExecutionMode::Native).await?;
//!
//!     // Execute a Ligature program
//!     let result = client.execute_file("config.lig").await?;
//!
//!     // Access the result
//!     println!("Result: {:?}", result);
//!
//!     Ok(())
//! }
//! ```

pub mod cache;
pub mod client;
pub mod config;
pub mod error;
pub mod executor;
pub mod sdk;

#[cfg(feature = "cli")]
pub mod cli;

pub use cache::*;
pub use client::*;
pub use config::*;
pub use error::*;
pub use executor::*;
use ligature_eval::Value;
pub use sdk::*;
use serde::{Deserialize, Serialize};

/// The result of executing a Ligature program.
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// The evaluated value from the program.
    pub value: Value,
    /// Execution metadata.
    pub metadata: ExecutionMetadata,
}

/// Metadata about program execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionMetadata {
    /// How long the execution took.
    pub duration: std::time::Duration,
    /// Whether the result was cached.
    pub cached: bool,
    /// The execution mode used.
    pub mode: ExecutionMode,
    /// Any warnings that occurred during execution.
    pub warnings: Vec<String>,
}

/// The mode of execution for Ligature programs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, clap::ValueEnum)]
pub enum ExecutionMode {
    /// Execute using the native ligature-cli binary.
    Native,
    /// Execute via HTTP endpoint.
    Http,
    /// Execute in-process (future feature).
    InProcess,
}

impl std::fmt::Display for ExecutionMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecutionMode::Native => write!(f, "native"),
            ExecutionMode::Http => write!(f, "http"),
            ExecutionMode::InProcess => write!(f, "in-process"),
        }
    }
}

/// Configuration for the Krox client.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientConfig {
    /// The execution mode to use.
    pub execution_mode: ExecutionMode,
    /// Whether to enable caching.
    pub enable_cache: bool,
    /// Cache directory path.
    pub cache_dir: Option<String>,
    /// HTTP endpoint for remote execution.
    pub http_endpoint: Option<String>,
    /// Timeout for HTTP requests.
    pub http_timeout: Option<std::time::Duration>,
    /// Path to ligature-cli binary (for native mode).
    pub ligature_cli_path: Option<String>,
    /// Whether to enable verbose logging.
    pub verbose: bool,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            execution_mode: ExecutionMode::Native,
            enable_cache: true,
            cache_dir: None,
            http_endpoint: None,
            http_timeout: Some(std::time::Duration::from_secs(30)),
            ligature_cli_path: None,
            verbose: false,
        }
    }
}

/// A builder for creating Krox clients with custom configuration.
#[derive(Debug)]
pub struct ClientBuilder {
    config: ClientConfig,
}

impl ClientBuilder {
    /// Create a new client builder with default configuration.
    pub fn new() -> Self {
        Self {
            config: ClientConfig::default(),
        }
    }

    /// Set the execution mode.
    pub fn execution_mode(mut self, mode: ExecutionMode) -> Self {
        self.config.execution_mode = mode;
        self
    }

    /// Enable or disable caching.
    pub fn enable_cache(mut self, enable: bool) -> Self {
        self.config.enable_cache = enable;
        self
    }

    /// Set the cache directory.
    pub fn cache_dir(mut self, dir: String) -> Self {
        self.config.cache_dir = Some(dir);
        self
    }

    /// Set the HTTP endpoint for remote execution.
    pub fn http_endpoint(mut self, endpoint: String) -> Self {
        self.config.http_endpoint = Some(endpoint);
        self
    }

    /// Set the HTTP timeout.
    pub fn http_timeout(mut self, timeout: std::time::Duration) -> Self {
        self.config.http_timeout = Some(timeout);
        self
    }

    /// Set the path to the ligature-cli binary.
    pub fn ligature_cli_path(mut self, path: String) -> Self {
        self.config.ligature_cli_path = Some(path);
        self
    }

    /// Enable verbose logging.
    pub fn verbose(mut self, verbose: bool) -> Self {
        self.config.verbose = verbose;
        self
    }

    /// Build the client.
    pub async fn build(self) -> Result<Client> {
        Client::with_config(self.config).await
    }
}

impl Default for ClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}
