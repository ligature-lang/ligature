//! Generic engine abstractions for engine-agnostic verification.

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

use crate::engine::{EngineCapabilities, EngineInfo};
use baton_error::prelude::*;

/// Generic engine configuration that can be implemented by any verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfig {
    /// Engine-specific configuration as JSON
    pub engine_config: serde_json::Value,
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
    /// Build configuration
    pub build_config: BuildConfig,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            engine_config: serde_json::Value::Null,
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
            build_config: BuildConfig::default(),
        }
    }
}

/// Retry configuration for engine operations.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
            base_delay: Duration::from_secs(1),
            max_delay: Duration::from_secs(30),
            exponential_backoff: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_error".to_string(),
                "temporary_failure".to_string(),
            ],
        }
    }
}

/// Build configuration for engine specifications.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildConfig {
    /// Whether to enable incremental builds
    pub incremental: bool,
    /// Whether to enable parallel builds
    pub parallel: bool,
    /// Build timeout in seconds
    pub timeout: u64,
    /// Whether to enable verbose output
    pub verbose: bool,
    /// Additional build flags
    pub build_flags: Vec<String>,
    /// Target libraries to build
    pub targets: Vec<String>,
}

impl Default for BuildConfig {
    fn default() -> Self {
        Self {
            incremental: true,
            parallel: false,
            timeout: 300,
            verbose: false,
            build_flags: vec![],
            targets: vec![],
        }
    }
}

/// Generic engine client trait that any verification engine must implement.
#[async_trait]
pub trait EngineClient: Send + Sync {
    /// Get the engine name.
    fn name(&self) -> &str;

    /// Get the engine version.
    async fn get_version(&self) -> BatonResult<String>;

    /// Ping the engine to check if it's available.
    async fn ping(&self) -> BatonResult<bool>;

    /// Execute a verification request.
    async fn execute(&self, request: EngineRequest) -> BatonResult<EngineResponse>;

    /// Get client statistics.
    fn get_stats(&self) -> ClientStats;

    /// Clear any caches.
    async fn clear_cache(&self);

    /// Get cache statistics.
    async fn get_cache_stats(&self) -> (usize, usize);
}

/// Generic engine request that can be sent to any verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineRequest {
    /// The request type
    pub request_type: EngineRequestType,
    /// Timeout in seconds
    pub timeout: Option<u64>,
    /// Additional context
    pub context: Option<serde_json::Value>,
    /// Request ID for tracking
    pub request_id: Option<String>,
    /// Priority level
    pub priority: Option<RequestPriority>,
}

/// Types of requests that can be sent to an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EngineRequestType {
    /// Verify expression evaluation
    VerifyEvaluation {
        expression: String,
        expected_value: String,
        context: Option<VerificationContext>,
    },
    /// Verify type checking
    VerifyTypeCheck {
        expression: String,
        expected_type: String,
        context: Option<VerificationContext>,
    },
    /// Verify operational semantics
    VerifyOperationalSemantics {
        expression: String,
        expected_steps: Vec<String>,
        context: Option<VerificationContext>,
    },
    /// Verify type safety
    VerifyTypeSafety {
        expression: String,
        context: Option<VerificationContext>,
    },
    /// Verify termination
    VerifyTermination {
        expression: String,
        context: Option<VerificationContext>,
    },
    /// Verify determinism
    VerifyDeterminism {
        expression: String,
        context: Option<VerificationContext>,
    },
    /// Verify theorem
    VerifyTheorem {
        theorem: String,
        proof: Option<String>,
        timeout: Option<u64>,
        context: Option<VerificationContext>,
    },
    /// Verify lemma
    VerifyLemma {
        lemma: String,
        proof: Option<String>,
        dependencies: Vec<String>,
        context: Option<VerificationContext>,
    },
    /// Verify invariant
    VerifyInvariant {
        invariant: String,
        expression: String,
        context: Option<VerificationContext>,
    },
    /// Verify refinement
    VerifyRefinement {
        abstract_spec: String,
        concrete_spec: String,
        refinement_relation: String,
        context: Option<VerificationContext>,
    },
    /// Run differential test
    RunDifferentialTest {
        test_case: String,
        test_type: DifferentialTestType,
        context: Option<VerificationContext>,
    },
    /// Extract test cases
    ExtractTestCases {
        specification_file: String,
        test_type: Option<TestType>,
    },
    /// Check specification
    CheckSpecification {
        specification_file: String,
        check_type: SpecificationCheckType,
    },
    /// Check consistency
    CheckConsistency {
        specification_files: Vec<String>,
        check_type: ConsistencyCheckType,
    },
    /// Generate counterexample
    GenerateCounterexample {
        property: String,
        context: Option<VerificationContext>,
    },
    /// Compare results
    CompareResults {
        result_a: String,
        result_b: String,
        comparison_type: ComparisonType,
    },
    /// Get version
    GetVersion,
    /// Ping
    Ping,
}

/// Generic engine response that can be returned by any verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineResponse {
    /// The response from the engine
    pub response: EngineResponseType,
    /// Execution time in milliseconds
    pub execution_time: u64,
    /// Additional metadata
    pub metadata: Option<serde_json::Value>,
    /// Request ID for tracking
    pub request_id: Option<String>,
    /// Response timestamp
    pub timestamp: Option<u64>,
}

impl EngineResponse {
    /// Create a new engine response.
    pub fn new(response: EngineResponseType, execution_time: u64) -> Self {
        Self {
            response,
            execution_time,
            metadata: None,
            request_id: None,
            timestamp: Some(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs(),
            ),
        }
    }

    /// Check if the response indicates success.
    pub fn is_success(&self) -> bool {
        match &self.response {
            EngineResponseType::VerificationSuccess { .. } => true,
            EngineResponseType::TestCasesExtracted { .. } => true,
            EngineResponseType::ResultsComparison { match_result, .. } => *match_result,
            EngineResponseType::DifferentialTestResult { success, .. } => *success,
            EngineResponseType::SpecificationCheckResult { success, .. } => *success,
            EngineResponseType::Version { .. } => true,
            EngineResponseType::Pong => true,
            EngineResponseType::TheoremVerificationResult { success, .. } => *success,
            EngineResponseType::ConsistencyCheckResult { consistent, .. } => *consistent,
            EngineResponseType::CounterexampleResult { found, .. } => *found,
            EngineResponseType::InvariantVerificationResult { holds, .. } => *holds,
            EngineResponseType::RefinementVerificationResult { valid, .. } => *valid,
            _ => false,
        }
    }

    /// Get the error message if the response indicates failure.
    pub fn error_message(&self) -> Option<&str> {
        match &self.response {
            EngineResponseType::VerificationFailure { error, .. } => Some(error),
            EngineResponseType::Error { error, .. } => Some(error),
            _ => None,
        }
    }

    /// Get the execution time in milliseconds.
    pub fn execution_time_ms(&self) -> u64 {
        self.execution_time
    }

    /// Get the execution time in seconds.
    pub fn execution_time_s(&self) -> f64 {
        self.execution_time as f64 / 1000.0
    }
}

/// Types of responses that can be returned by an engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EngineResponseType {
    /// Verification successful
    VerificationSuccess {
        result: String,
        proof: Option<String>,
        proof_steps: Option<Vec<String>>,
        execution_time: Option<u64>,
    },
    /// Verification failed
    VerificationFailure {
        error: String,
        details: Option<String>,
        error_type: Option<ErrorType>,
        suggestions: Option<Vec<String>>,
    },
    /// Test cases extracted
    TestCasesExtracted {
        test_cases: Vec<String>,
        test_count: usize,
        coverage_info: Option<CoverageInfo>,
    },
    /// Results comparison
    ResultsComparison {
        match_result: bool,
        differences: Vec<String>,
        similarity_score: Option<f64>,
        detailed_comparison: Option<DetailedComparison>,
    },
    /// Differential test result
    DifferentialTestResult {
        success: bool,
        result_a: String,
        result_b: String,
        match_result: bool,
        performance_comparison: Option<PerformanceComparison>,
    },
    /// Specification check result
    SpecificationCheckResult {
        success: bool,
        errors: Vec<String>,
        warnings: Vec<String>,
        info: Vec<String>,
        build_time: Option<u64>,
        dependency_info: Option<DependencyInfo>,
    },
    /// Version information
    Version {
        version: String,
        commit: String,
        build_date: Option<String>,
        features: Option<Vec<String>>,
    },
    /// Pong response
    Pong,
    /// Error response
    Error {
        error: String,
        details: Option<String>,
        error_type: Option<ErrorType>,
        recovery_suggestions: Option<Vec<String>>,
    },
    /// Theorem verification result
    TheoremVerificationResult {
        success: bool,
        proof: Option<String>,
        proof_steps: Option<Vec<String>>,
        execution_time: u64,
        theorem_info: Option<TheoremInfo>,
    },
    /// Consistency check result
    ConsistencyCheckResult {
        consistent: bool,
        inconsistencies: Vec<String>,
        suggestions: Vec<String>,
        check_time: u64,
    },
    /// Counterexample result
    CounterexampleResult {
        found: bool,
        counterexample: Option<String>,
        explanation: Option<String>,
        generation_time: u64,
    },
    /// Invariant verification result
    InvariantVerificationResult {
        holds: bool,
        violation_point: Option<String>,
        verification_time: u64,
    },
    /// Refinement verification result
    RefinementVerificationResult {
        valid: bool,
        refinement_proof: Option<String>,
        abstraction_mapping: Option<String>,
        verification_time: u64,
    },
}

/// Verification context for engine requests.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationContext {
    pub environment: Option<HashMap<String, String>>,
    pub assumptions: Vec<String>,
    pub constraints: Vec<String>,
    pub metadata: Option<HashMap<String, serde_json::Value>>,
    pub timeout: Option<u64>,
    pub verbose: Option<bool>,
}

/// Test types for differential testing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TestType {
    Unit,
    Integration,
    Property,
    Regression,
    Performance,
    All,
}

/// Comparison types for result comparison.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComparisonType {
    Exact,
    Structural,
    Semantic,
    Performance,
    All,
}

/// Differential test types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DifferentialTestType {
    Evaluation,
    TypeCheck,
    OperationalSemantics,
    ConfigurationValidation,
    Performance,
    MemoryUsage,
    All,
}

/// Specification check types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpecificationCheckType {
    Syntax,
    Type,
    Semantics,
    Consistency,
    Completeness,
    All,
}

/// Consistency check types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConsistencyCheckType {
    Type,
    Semantics,
    Axioms,
    Theorems,
    All,
}

/// Error types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorType {
    Syntax,
    Type,
    Semantics,
    Logic,
    Timeout,
    Resource,
    System,
    Unknown,
}

/// Request priority levels.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RequestPriority {
    Low,
    Normal,
    High,
    Critical,
}

/// Coverage information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageInfo {
    pub line_coverage: f64,
    pub branch_coverage: f64,
    pub function_coverage: f64,
    pub uncovered_lines: Vec<u32>,
    pub uncovered_branches: Vec<String>,
}

/// Detailed comparison information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetailedComparison {
    pub structural_match: bool,
    pub semantic_match: bool,
    pub performance_match: bool,
    pub differences: Vec<Difference>,
}

/// Difference information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Difference {
    pub field: String,
    pub expected: String,
    pub actual: String,
    pub severity: DifferenceSeverity,
}

/// Difference severity levels.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DifferenceSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// Performance comparison information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceComparison {
    pub time_a: u64,
    pub time_b: u64,
    pub speedup: f64,
    pub memory_usage: Option<MemoryUsage>,
}

/// Memory usage information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryUsage {
    pub memory_a: u64,
    pub memory_b: u64,
    pub memory_ratio: f64,
}

/// Dependency information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyInfo {
    pub direct_dependencies: Vec<String>,
    pub transitive_dependencies: Vec<String>,
    #[allow(clippy::type_complexity)]
    pub dependency_tree: Option<HashMap<String, Vec<String>>>,
}

/// Theorem information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremInfo {
    pub name: String,
    pub statement: String,
    pub proof_length: Option<usize>,
    pub complexity: Option<String>,
    pub dependencies: Vec<String>,
}

/// Client statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientStats {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: Duration,
    pub total_uptime: Duration,
    pub last_request_time: Option<u64>, // Unix timestamp in seconds
}

impl Default for ClientStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            average_response_time: Duration::ZERO,
            total_uptime: Duration::ZERO,
            last_request_time: None,
        }
    }
}

impl ClientStats {
    /// Update the last request time to now.
    pub fn update_last_request_time(&mut self) {
        self.last_request_time = Some(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        );
    }

    /// Get the last request time as a SystemTime if available.
    pub fn last_request_system_time(&self) -> Option<std::time::SystemTime> {
        self.last_request_time
            .map(|timestamp| std::time::UNIX_EPOCH + std::time::Duration::from_secs(timestamp))
    }
}

/// Generic engine factory trait for creating engine clients.
#[async_trait]
pub trait EngineClientFactory: Send + Sync {
    /// Create a new engine client with default configuration.
    async fn create_client(&self) -> BatonResult<Box<dyn EngineClient>>;

    /// Create a new engine client with custom configuration.
    async fn create_client_with_config(
        &self,
        config: EngineConfig,
    ) -> BatonResult<Box<dyn EngineClient>>;

    /// Get the engine name.
    fn engine_name(&self) -> &str;

    /// Get the engine info.
    fn engine_info(&self) -> EngineInfo;

    /// Get the engine capabilities.
    fn engine_capabilities(&self) -> EngineCapabilities;
}
