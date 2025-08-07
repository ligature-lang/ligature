//! Engine-related types and structures.

use serde::{Deserialize, Serialize};

/// Information about a verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineInfo {
    /// Engine name
    pub name: String,
    /// Engine version
    pub version: String,
    /// Engine description
    pub description: String,
    /// Engine vendor
    pub vendor: String,
    /// Engine homepage URL
    pub homepage: Option<String>,
    /// Engine documentation URL
    pub documentation: Option<String>,
    /// Engine license
    pub license: Option<String>,
    /// Supported languages
    pub supported_languages: Vec<String>,
    /// Supported features
    pub supported_features: Vec<String>,
    /// Engine configuration schema
    pub config_schema: Option<serde_json::Value>,
}

/// Capabilities of a verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineCapabilities {
    /// Whether the engine supports expression evaluation verification
    pub supports_evaluation: bool,
    /// Whether the engine supports type checking verification
    pub supports_type_checking: bool,
    /// Whether the engine supports operational semantics verification
    pub supports_operational_semantics: bool,
    /// Whether the engine supports type safety verification
    pub supports_type_safety: bool,
    /// Whether the engine supports termination verification
    pub supports_termination: bool,
    /// Whether the engine supports determinism verification
    pub supports_determinism: bool,
    /// Whether the engine supports theorem verification
    pub supports_theorem_verification: bool,
    /// Whether the engine supports lemma verification
    pub supports_lemma_verification: bool,
    /// Whether the engine supports invariant verification
    pub supports_invariant_verification: bool,
    /// Whether the engine supports refinement verification
    pub supports_refinement_verification: bool,
    /// Whether the engine supports differential testing
    pub supports_differential_testing: bool,
    /// Whether the engine supports test case extraction
    pub supports_test_extraction: bool,
    /// Whether the engine supports specification checking
    pub supports_specification_checking: bool,
    /// Whether the engine supports consistency checking
    pub supports_consistency_checking: bool,
    /// Whether the engine supports counterexample generation
    pub supports_counterexample_generation: bool,
    /// Whether the engine supports result comparison
    pub supports_result_comparison: bool,
    /// Maximum timeout in seconds
    pub max_timeout: Option<u64>,
    /// Maximum expression size
    pub max_expression_size: Option<usize>,
    /// Maximum theorem complexity
    pub max_theorem_complexity: Option<String>,
    /// Supported input formats
    pub supported_input_formats: Vec<String>,
    /// Supported output formats
    pub supported_output_formats: Vec<String>,
    /// Performance characteristics
    pub performance_characteristics: PerformanceCharacteristics,
}

impl Default for EngineCapabilities {
    fn default() -> Self {
        Self {
            supports_evaluation: true,
            supports_type_checking: true,
            supports_operational_semantics: false,
            supports_type_safety: true,
            supports_termination: false,
            supports_determinism: false,
            supports_theorem_verification: true,
            supports_lemma_verification: true,
            supports_invariant_verification: false,
            supports_refinement_verification: false,
            supports_differential_testing: true,
            supports_test_extraction: false,
            supports_specification_checking: true,
            supports_consistency_checking: false,
            supports_counterexample_generation: false,
            supports_result_comparison: true,
            max_timeout: Some(300), // 5 minutes
            max_expression_size: Some(10000),
            max_theorem_complexity: Some("medium".to_string()),
            supported_input_formats: vec!["text".to_string()],
            supported_output_formats: vec!["json".to_string()],
            performance_characteristics: PerformanceCharacteristics::default(),
        }
    }
}

/// Performance characteristics of an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceCharacteristics {
    /// Average verification time in milliseconds
    pub average_verification_time_ms: u64,
    /// Memory usage in MB
    pub memory_usage_mb: u64,
    /// CPU usage percentage
    pub cpu_usage_percent: f64,
    /// Throughput (verifications per second)
    pub throughput_per_second: f64,
    /// Scalability factor
    pub scalability_factor: f64,
    /// Cache efficiency
    pub cache_efficiency: f64,
}

impl Default for PerformanceCharacteristics {
    fn default() -> Self {
        Self {
            average_verification_time_ms: 1000,
            memory_usage_mb: 100,
            cpu_usage_percent: 50.0,
            throughput_per_second: 1.0,
            scalability_factor: 1.0,
            cache_efficiency: 0.8,
        }
    }
}

/// Status of a verification engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EngineStatus {
    /// Engine is not initialized
    Uninitialized,
    /// Engine is initializing
    Initializing,
    /// Engine is ready to accept requests
    Ready,
    /// Engine is busy processing requests
    Busy,
    /// Engine is shutting down
    ShuttingDown,
    /// Engine has encountered an error
    Error,
    /// Engine is offline
    Offline,
}

impl std::fmt::Display for EngineStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineStatus::Uninitialized => write!(f, "uninitialized"),
            EngineStatus::Initializing => write!(f, "initializing"),
            EngineStatus::Ready => write!(f, "ready"),
            EngineStatus::Busy => write!(f, "busy"),
            EngineStatus::ShuttingDown => write!(f, "shutting_down"),
            EngineStatus::Error => write!(f, "error"),
            EngineStatus::Offline => write!(f, "offline"),
        }
    }
}

/// Configuration for an engine plugin.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfig {
    /// Engine-specific configuration
    pub engine_config: serde_json::Value,
    /// Timeout configuration
    pub timeout_config: TimeoutConfig,
    /// Performance configuration
    pub performance_config: PerformanceConfig,
    /// Logging configuration
    pub logging_config: LoggingConfig,
    /// Cache configuration
    pub cache_config: CacheConfig,
}

/// Timeout configuration for an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    /// Default timeout in seconds
    pub default_timeout: u64,
    /// Maximum timeout in seconds
    pub max_timeout: u64,
    /// Timeout for evaluation operations
    pub evaluation_timeout: u64,
    /// Timeout for type checking operations
    pub type_check_timeout: u64,
    /// Timeout for theorem verification
    pub theorem_timeout: u64,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            default_timeout: 30,
            max_timeout: 300,
            evaluation_timeout: 10,
            type_check_timeout: 15,
            theorem_timeout: 60,
        }
    }
}

/// Performance configuration for an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Maximum concurrent requests
    pub max_concurrent_requests: usize,
    /// Memory limit in MB
    pub memory_limit_mb: u64,
    /// CPU limit percentage
    pub cpu_limit_percent: f64,
    /// Enable performance monitoring
    pub enable_monitoring: bool,
    /// Performance sampling rate
    pub sampling_rate: f64,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            max_concurrent_requests: 10,
            memory_limit_mb: 1024,
            cpu_limit_percent: 80.0,
            enable_monitoring: true,
            sampling_rate: 0.1,
        }
    }
}

/// Logging configuration for an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    /// Log level
    pub log_level: String,
    /// Enable structured logging
    pub structured_logging: bool,
    /// Log file path
    pub log_file: Option<String>,
    /// Enable request/response logging
    pub enable_request_logging: bool,
    /// Enable performance logging
    pub enable_performance_logging: bool,
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            log_level: "info".to_string(),
            structured_logging: true,
            log_file: None,
            enable_request_logging: false,
            enable_performance_logging: true,
        }
    }
}

/// Cache configuration for an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    /// Enable caching
    pub enable_cache: bool,
    /// Cache TTL in seconds
    pub cache_ttl: u64,
    /// Maximum cache size in MB
    pub max_cache_size_mb: u64,
    /// Cache eviction policy
    pub eviction_policy: String,
    /// Enable cache statistics
    pub enable_statistics: bool,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enable_cache: true,
            cache_ttl: 3600,
            max_cache_size_mb: 100,
            eviction_policy: "lru".to_string(),
            enable_statistics: true,
        }
    }
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            engine_config: serde_json::Value::Null,
            timeout_config: TimeoutConfig::default(),
            performance_config: PerformanceConfig::default(),
            logging_config: LoggingConfig::default(),
            cache_config: CacheConfig::default(),
        }
    }
}
