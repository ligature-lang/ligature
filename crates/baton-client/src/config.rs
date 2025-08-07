//! Configuration types for Baton client.

use serde_json;
use std::time::Duration;

/// Configuration for engine client.
#[derive(Debug, Clone)]
pub struct EngineClientConfig {
    /// Path to engine executable
    pub engine_path: String,
    /// Path to specification directory
    pub spec_path: String,
    /// Process timeout
    pub timeout: Duration,
    /// Whether to use verbose output
    pub verbose: bool,
    /// Maximum number of concurrent processes
    pub max_processes: usize,
    /// Connection pool size
    pub pool_size: usize,
    /// Retry attempts for failed operations
    pub retry_attempts: u32,
    /// Retry delay between attempts
    pub retry_delay: Duration,
    /// Whether to enable connection pooling
    pub enable_pooling: bool,
    /// Whether to enable debug logging
    pub debug_logging: bool,
    /// Engine-specific configuration
    pub engine_specific_config: serde_json::Value,
}

impl Default for EngineClientConfig {
    fn default() -> Self {
        Self {
            engine_path: String::new(),
            spec_path: String::new(),
            timeout: Duration::from_secs(30),
            verbose: false,
            max_processes: 4,
            pool_size: 2,
            retry_attempts: 3,
            retry_delay: Duration::from_millis(100),
            enable_pooling: true,
            debug_logging: false,
            engine_specific_config: serde_json::Value::Null,
        }
    }
}

// Legacy type alias for backward compatibility
pub type LeanClientConfig = EngineClientConfig;
