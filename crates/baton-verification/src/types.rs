//! Type definitions for verification engine.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use baton_client::{ClientStats, LeanClient, LeanClientConfig};
use baton_engine_plugin::BuildConfig;
use baton_error::BatonError;
use baton_protocol::{VerificationRequest, VerificationResponse};
use baton_specification::LeanSpecification;
use tokio::sync::Mutex;

/// Verification engine for coordinating Lean verification operations.
pub struct VerificationEngine {
    /// Lean client for communication
    pub client: Arc<LeanClient>,
    /// Specification manager
    pub specification: Arc<LeanSpecification>,
    /// Cache for verification results
    #[allow(clippy::type_complexity)]
    pub cache: Arc<Mutex<HashMap<String, CachedResult>>>,
    /// Configuration options
    pub config: VerificationConfig,
    /// Performance metrics
    pub metrics: Arc<Mutex<VerificationMetrics>>,
    /// Active verification tasks
    #[allow(clippy::type_complexity)]
    pub active_tasks: Arc<Mutex<HashMap<String, VerificationTask>>>,
}

/// Cached verification result.
#[derive(Debug, Clone)]
pub struct CachedResult {
    /// The verification response
    pub response: VerificationResponse,
    /// When the result was cached
    pub cached_at: Instant,
    /// Cache TTL
    pub ttl: Duration,
}

/// Verification task information.
#[derive(Debug, Clone)]
pub struct VerificationTask {
    /// Task ID
    pub task_id: String,
    /// Request being processed
    pub request: VerificationRequest,
    /// Start time
    pub start_time: Instant,
    /// Status
    pub status: TaskStatus,
    /// Progress information
    pub progress: Option<String>,
}

/// Task status.
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum TaskStatus {
    Pending,
    Running,
    Completed(VerificationResponse),
    Failed(BatonError),
    Cancelled,
}

/// Configuration for verification operations.
#[derive(Debug, Clone)]
pub struct VerificationConfig {
    /// Whether to enable caching
    pub enable_cache: bool,
    /// Cache TTL in seconds
    pub cache_ttl: u64,
    /// Default timeout for operations
    pub default_timeout: u64,
    /// Whether to run differential tests
    pub run_differential_tests: bool,
    /// Whether to verify type safety
    pub verify_type_safety: bool,
    /// Whether to verify termination
    pub verify_termination: bool,
    /// Whether to verify determinism
    pub verify_determinism: bool,
    /// Maximum concurrent tasks
    pub max_concurrent_tasks: usize,
    /// Whether to enable performance monitoring
    pub enable_performance_monitoring: bool,
    /// Whether to enable detailed logging
    pub enable_detailed_logging: bool,
    /// Retry configuration
    pub retry_config: RetryConfig,
    /// Client configuration
    pub client_config: LeanClientConfig,
    /// Build configuration
    pub build_config: BuildConfig,
}

impl Default for VerificationConfig {
    fn default() -> Self {
        Self {
            enable_cache: true,
            cache_ttl: 3600,
            default_timeout: 30,
            run_differential_tests: true,
            verify_type_safety: true,
            verify_termination: false,
            verify_determinism: false,
            max_concurrent_tasks: 10,
            enable_performance_monitoring: true,
            enable_detailed_logging: false,
            retry_config: RetryConfig::default(),
            client_config: LeanClientConfig::default(),
            build_config: BuildConfig::default(),
        }
    }
}

/// Retry configuration for verification operations.
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// Maximum retry attempts
    pub max_attempts: u32,
    /// Base delay between retries
    pub base_delay: Duration,
    /// Maximum delay between retries
    pub max_delay: Duration,
    /// Whether to use exponential backoff
    pub exponential_backoff: bool,
    /// Retryable error types
    pub retryable_errors: Vec<String>,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            exponential_backoff: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_error".to_string(),
                "temporary_error".to_string(),
            ],
        }
    }
}

/// Performance metrics for verification operations.
#[derive(Debug, Clone)]
pub struct VerificationMetrics {
    /// Total verifications performed
    pub total_verifications: u64,
    /// Successful verifications
    pub successful_verifications: u64,
    /// Failed verifications
    pub failed_verifications: u64,
    /// Average verification time
    pub average_verification_time: Duration,
    /// Cache hit rate
    pub cache_hit_rate: f64,
    /// Total cache hits
    pub cache_hits: u64,
    /// Total cache misses
    pub cache_misses: u64,
    /// Performance breakdown by operation type
    pub operation_times: HashMap<String, Duration>,
    /// Error breakdown
    pub error_counts: HashMap<String, u64>,
    /// Last verification time
    pub last_verification_time: Option<Instant>,
}

/// Engine health status.
#[derive(Debug, Clone)]
pub struct EngineHealthStatus {
    /// Whether Lean is available
    pub lean_available: bool,
    /// Client statistics
    pub client_stats: ClientStats,
    /// Verification metrics
    pub metrics: VerificationMetrics,
    /// Number of active tasks
    pub active_task_count: usize,
    /// Cache size
    pub cache_size: usize,
    /// Engine uptime
    pub uptime: Duration,
}
