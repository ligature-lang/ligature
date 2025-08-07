//! Core traits for Baton verification engine plugins.

use async_trait::async_trait;
use baton_error::prelude::*;
use baton_protocol::prelude::*;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::engine::{EngineCapabilities, EngineInfo, EngineStatus};

/// Plugin trait for verification engines.
#[async_trait]
pub trait EnginePlugin: Send + Sync {
    /// Get the name of the engine plugin.
    fn name(&self) -> &str;

    /// Get the version of the engine plugin.
    fn version(&self) -> &str;

    /// Get the description of the engine plugin.
    fn description(&self) -> &str;

    /// Get information about the engine.
    fn engine_info(&self) -> EngineInfo;

    /// Get the capabilities of this engine.
    fn capabilities(&self) -> EngineCapabilities;

    /// Initialize the engine plugin.
    async fn initialize(&mut self, config: &Value) -> BatonResult<()>;

    /// Shutdown the engine plugin.
    async fn shutdown(&mut self) -> BatonResult<()>;

    /// Get the status of the engine.
    async fn status(&self) -> BatonResult<EngineStatus>;

    /// Configure the engine with new settings.
    async fn configure(&mut self, config: &Value) -> BatonResult<()>;

    /// Get the verification engine instance.
    fn get_engine(&self) -> BatonResult<Box<dyn VerificationEngine>>;
}

/// Trait for verification engines that can perform various verification tasks.
#[async_trait]
pub trait VerificationEngine: Send + Sync {
    /// Verify expression evaluation.
    async fn verify_evaluation(
        &self,
        expression: &str,
        expected_value: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify type checking.
    async fn verify_type_check(
        &self,
        expression: &str,
        expected_type: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify operational semantics.
    async fn verify_operational_semantics(
        &self,
        expression: &str,
        expected_steps: &[String],
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify type safety.
    async fn verify_type_safety(
        &self,
        expression: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify termination.
    async fn verify_termination(
        &self,
        expression: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify determinism.
    async fn verify_determinism(
        &self,
        expression: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify theorem.
    async fn verify_theorem(
        &self,
        theorem: &str,
        proof: Option<&str>,
        timeout: Option<u64>,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify lemma.
    async fn verify_lemma(
        &self,
        lemma: &str,
        proof: Option<&str>,
        dependencies: &[String],
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify invariant.
    async fn verify_invariant(
        &self,
        invariant: &str,
        expression: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Verify refinement.
    async fn verify_refinement(
        &self,
        abstract_spec: &str,
        concrete_spec: &str,
        refinement_relation: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Run differential test.
    async fn run_differential_test(
        &self,
        test_case: &str,
        test_type: DifferentialTestType,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Extract test cases from specification.
    async fn extract_test_cases(
        &self,
        specification_file: &str,
        test_type: Option<TestType>,
    ) -> BatonResult<Vec<String>>;

    /// Check specification.
    async fn check_specification(
        &self,
        specification_file: &str,
        check_type: SpecificationCheckType,
    ) -> BatonResult<VerificationResponse>;

    /// Check consistency.
    async fn check_consistency(
        &self,
        specification_files: &[String],
        check_type: ConsistencyCheckType,
    ) -> BatonResult<VerificationResponse>;

    /// Generate counterexample.
    async fn generate_counterexample(
        &self,
        property: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse>;

    /// Compare results.
    async fn compare_results(
        &self,
        rust_result: &str,
        lean_result: &str,
        comparison_type: ComparisonType,
    ) -> BatonResult<VerificationResponse>;

    /// Get version information.
    async fn get_version(&self) -> BatonResult<String>;

    /// Ping the engine.
    async fn ping(&self) -> BatonResult<bool>;

    /// Get engine statistics.
    fn get_stats(&self) -> EngineStats;

    /// Get engine health status.
    async fn get_health_status(&self) -> BatonResult<EngineHealthStatus>;
}

/// Statistics for a verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineStats {
    /// Total requests processed
    pub total_requests: u64,
    /// Successful requests
    pub successful_requests: u64,
    /// Failed requests
    pub failed_requests: u64,
    /// Average response time in milliseconds
    pub average_response_time: u64,
    /// Total uptime in seconds
    pub uptime_seconds: u64,
    /// Memory usage in bytes
    pub memory_usage_bytes: u64,
    /// CPU usage percentage
    pub cpu_usage_percent: f64,
    /// Cache hit rate
    pub cache_hit_rate: f64,
    /// Active connections
    pub active_connections: u32,
}

impl Default for EngineStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            average_response_time: 0,
            uptime_seconds: 0,
            memory_usage_bytes: 0,
            cpu_usage_percent: 0.0,
            cache_hit_rate: 0.0,
            active_connections: 0,
        }
    }
}

/// Health status for a verification engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineHealthStatus {
    /// Whether the engine is healthy
    pub healthy: bool,
    /// Engine status
    pub status: EngineStatus,
    /// Error message if unhealthy
    pub error_message: Option<String>,
    /// Engine statistics
    pub stats: EngineStats,
    /// Last health check timestamp
    pub last_check: u64,
}

impl Default for EngineHealthStatus {
    fn default() -> Self {
        Self {
            healthy: true,
            status: EngineStatus::Ready,
            error_message: None,
            stats: EngineStats::default(),
            last_check: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        }
    }
}
