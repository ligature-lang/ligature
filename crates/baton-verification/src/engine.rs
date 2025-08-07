//! Core verification engine implementation.

use crate::types::{CachedResult, EngineHealthStatus, TaskStatus, VerificationConfig, VerificationEngine, VerificationMetrics, VerificationTask};
use baton_client::prelude::*;
use baton_engine_plugin::{BuildConfig, EngineConfig};
use baton_protocol::{LeanRequest, LeanResponse, VerificationRequest, VerificationResponse};
use baton_specification::{LeanSpecification, ValidationResult, BuildStatus};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

impl VerificationEngine {
    /// Create a new verification engine with default configuration.
    pub fn new() -> BatonResult<Self> {
        let retry_config = crate::types::RetryConfig {
            max_attempts: 3,
            base_delay: Duration::from_secs(1),
            max_delay: Duration::from_secs(30),
            exponential_backoff: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection".to_string(),
                "temporary".to_string(),
            ],
        };
        
        let config = VerificationConfig {
            enable_cache: true,
            cache_ttl: 3600, // 1 hour
            default_timeout: 60,
            run_differential_tests: false,
            verify_type_safety: true,
            verify_termination: false,
            verify_determinism: false,
            max_concurrent_tasks: 10,
            enable_performance_monitoring: true,
            enable_detailed_logging: false,
            retry_config,
            client_config: LeanClientConfig::default(),
            build_config: BuildConfig::default(),
        };
        
        Self::with_config(config)
    }

    /// Create a new verification engine with custom configuration.
    pub fn with_config(config: VerificationConfig) -> BatonResult<Self> {
        let client = Arc::new(LeanClient::with_config(
            "lean".to_string(),
            config.client_config.clone(),
        )?);
        let engine_config = EngineConfig::default();
        let specification = Arc::new(LeanSpecification::new_default(
            "lean".to_string(),
            engine_config,
        )?);

        let metrics = VerificationMetrics {
            total_verifications: 0,
            successful_verifications: 0,
            failed_verifications: 0,
            average_verification_time: Duration::ZERO,
            cache_hit_rate: 0.0,
            cache_hits: 0,
            cache_misses: 0,
            operation_times: HashMap::new(),
            error_counts: HashMap::new(),
            last_verification_time: None,
        };

        Ok(Self {
            client,
            specification,
            cache: Arc::new(Mutex::new(HashMap::new())),
            config,
            metrics: Arc::new(Mutex::new(metrics)),
            active_tasks: Arc::new(Mutex::new(HashMap::new())),
        })
    }

    /// Verify expression evaluation.
    pub async fn verify_evaluation(
        &self,
        expression: &str,
        expected_value: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyEvaluation {
            expression: expression.to_string(),
            expected_value: expected_value.to_string(),
            context,
        });

        let cache_key = format!("eval:{expression}:{expected_value}");
        self.execute_verification(request, &cache_key, "evaluation")
            .await
    }

    /// Verify type checking.
    pub async fn verify_type_check(
        &self,
        expression: &str,
        expected_type: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyTypeCheck {
            expression: expression.to_string(),
            expected_type: expected_type.to_string(),
            context,
        });

        let cache_key = format!("typecheck:{expression}:{expected_type}");
        self.execute_verification(request, &cache_key, "type_check")
            .await
    }

    /// Run differential test.
    pub async fn run_differential_test(
        &self,
        test_case: &str,
        test_type: baton_protocol::DifferentialTestType,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::RunDifferentialTest {
            test_case: test_case.to_string(),
            test_type: test_type.clone(),
            context,
        });

        let cache_key = format!("diff:{test_case}:{test_type:?}");
        self.execute_verification(request, &cache_key, "differential_test")
            .await
    }

    /// Verify type safety.
    pub async fn verify_type_safety(
        &self,
        expression: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyTypeSafety {
            expression: expression.to_string(),
            context,
        });

        let cache_key = format!("safety:{expression}");
        self.execute_verification(request, &cache_key, "type_safety")
            .await
    }

    /// Verify termination.
    pub async fn verify_termination(
        &self,
        expression: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyTermination {
            expression: expression.to_string(),
            context,
        });

        let cache_key = format!("termination:{expression}");
        self.execute_verification(request, &cache_key, "termination")
            .await
    }

    /// Verify determinism.
    pub async fn verify_determinism(
        &self,
        expression: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyDeterminism {
            expression: expression.to_string(),
            context,
        });

        let cache_key = format!("determinism:{expression}");
        self.execute_verification(request, &cache_key, "determinism")
            .await
    }

    /// Verify theorem.
    pub async fn verify_theorem(
        &self,
        theorem: &str,
        proof: Option<&str>,
        timeout: Option<u64>,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyTheorem {
            theorem: theorem.to_string(),
            proof: proof.map(|p| p.to_string()),
            timeout,
            context,
        });

        let cache_key = format!("theorem:{theorem}");
        self.execute_verification(request, &cache_key, "theorem")
            .await
    }

    /// Verify invariant.
    pub async fn verify_invariant(
        &self,
        invariant: &str,
        expression: &str,
        context: Option<baton_protocol::VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        let request = VerificationRequest::new(LeanRequest::VerifyInvariant {
            invariant: invariant.to_string(),
            expression: expression.to_string(),
            context,
        });

        let cache_key = format!("invariant:{invariant}:{expression}");
        self.execute_verification(request, &cache_key, "invariant")
            .await
    }

    /// Extract test cases from specification.
    pub async fn extract_test_cases(&self, specification_file: &str) -> BatonResult<Vec<String>> {
        let request = VerificationRequest::new(LeanRequest::ExtractTestCases {
            specification_file: specification_file.to_string(),
            test_type: None,
        });

        let response = self.execute_with_retry(request, "extract_test_cases").await?;

        match response.response {
            LeanResponse::TestCasesExtracted { test_cases, .. } => Ok(test_cases),
            _ => Err(BatonError::InternalError(
                "Unexpected response type for test case extraction".to_string(),
            )),
        }
    }

    /// Check specification compilation.
    pub async fn check_specification(&self, specification_file: &str) -> BatonResult<bool> {
        let request = VerificationRequest::new(LeanRequest::CheckSpecification {
            specification_file: specification_file.to_string(),
            check_type: baton_protocol::SpecificationCheckType::All,
        });

        let response = self.execute_with_retry(request, "check_specification").await?;

        match response.response {
            LeanResponse::SpecificationCheckResult { success, .. } => Ok(success),
            _ => Err(BatonError::InternalError(
                "Unexpected response type for specification check".to_string(),
            )),
        }
    }

    /// Validate specification.
    pub async fn validate_specification(&self) -> BatonResult<ValidationResult> {
        self.specification.validate().await
    }

    /// Build specification.
    pub async fn build_specification(&self) -> BatonResult<BuildStatus> {
        let engine_config = EngineConfig::default();
        let mut spec = LeanSpecification::new_default("lean".to_string(), engine_config)?;
        spec.set_build_config(self.config.build_config.clone());
        spec.build().await
    }

    /// Get Lean version.
    pub async fn get_lean_version(&self) -> BatonResult<String> {
        self.client.get_version().await
    }

    /// Ping Lean process.
    pub async fn ping(&self) -> BatonResult<bool> {
        self.client.ping().await
    }

    /// Get client statistics.
    pub fn get_client_stats(&self) -> ClientStats {
        self.client.get_stats()
    }

    /// Get verification metrics.
    pub async fn get_metrics(&self) -> VerificationMetrics {
        let metrics = self.metrics.lock().await;
        metrics.clone()
    }

    /// Clear cache.
    pub async fn clear_cache(&self) {
        let mut cache = self.cache.lock().await;
        cache.clear();

        // Update metrics
        let mut metrics = self.metrics.lock().await;
        metrics.cache_hits = 0;
        metrics.cache_misses = 0;
        metrics.cache_hit_rate = 0.0;
    }

    /// Get cache statistics.
    pub async fn get_cache_stats(&self) -> (usize, usize) {
        let cache = self.cache.lock().await;
        let metrics = self.metrics.lock().await;
        (cache.len(), (metrics.cache_hits + metrics.cache_misses) as usize)
    }

    /// Execute verification with caching and retry logic.
    async fn execute_verification(
        &self,
        request: VerificationRequest,
        cache_key: &str,
        operation_type: &str,
    ) -> BatonResult<VerificationResponse> {
        let start_time = Instant::now();

        // Check cache first
        if self.config.enable_cache {
            if let Some(cached_response) = self.get_cached_result(cache_key).await {
                self.update_metrics(operation_type, start_time.elapsed(), true, None)
                    .await;
                return Ok(cached_response);
            }
        }

        // Execute with retry
        let result = self.execute_with_retry(request, operation_type).await;

        let duration = start_time.elapsed();
        let error = result.as_ref().err();
        self.update_metrics(operation_type, duration, false, error)
            .await;

        // Cache successful results
        if let Ok(ref response) = result {
            if self.config.enable_cache {
                self.cache_result(cache_key, response.clone()).await;
            }
        }

        result
    }

    /// Execute verification with retry logic.
    async fn execute_with_retry(
        &self,
        request: VerificationRequest,
        _operation_type: &str,
    ) -> BatonResult<VerificationResponse> {
        let mut last_error = None;

        for attempt in 0..self.config.retry_config.max_attempts {
            match self.client.verify(request.clone()).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    last_error = Some(e.clone());

                    if attempt < self.config.retry_config.max_attempts
                        && self.is_retryable_error(&e)
                    {
                        let delay = if self.config.retry_config.exponential_backoff {
                            self.config.retry_config.base_delay * (2_u32.pow(attempt))
                        } else {
                            self.config.retry_config.base_delay
                        };

                        let delay = std::cmp::min(delay, self.config.retry_config.max_delay);
                        tokio::time::sleep(delay).await;
                        continue;
                    } else {
                        break;
                    }
                }
            }
        }

        Err(last_error
            .unwrap_or_else(|| BatonError::InternalError("Unknown error during retry".to_string())))
    }

    /// Check if error is retryable.
    fn is_retryable_error(&self, error: &BatonError) -> bool {
        let error_str = format!("{error:?}").to_lowercase();
        self.config
            .retry_config
            .retryable_errors
            .iter()
            .any(|retryable| error_str.contains(retryable))
    }

    /// Get cached result.
    async fn get_cached_result(&self, cache_key: &str) -> Option<VerificationResponse> {
        let mut cache = self.cache.lock().await;

        if let Some(cached) = cache.get(cache_key) {
            if cached.cached_at.elapsed() < cached.ttl {
                // Update metrics
                let mut metrics = self.metrics.lock().await;
                metrics.cache_hits += 1;
                metrics.cache_hit_rate =
                    metrics.cache_hits as f64 / (metrics.cache_hits + metrics.cache_misses) as f64;

                return Some(cached.response.clone());
            } else {
                // Remove expired cache entry
                cache.remove(cache_key);
            }
        }

        // Update cache miss metrics
        let mut metrics = self.metrics.lock().await;
        metrics.cache_misses += 1;
        metrics.cache_hit_rate =
            metrics.cache_hits as f64 / (metrics.cache_hits + metrics.cache_misses) as f64;

        None
    }

    /// Cache result.
    async fn cache_result(&self, cache_key: &str, response: VerificationResponse) {
        let mut cache = self.cache.lock().await;
        let ttl = Duration::from_secs(self.config.cache_ttl);

        cache.insert(
            cache_key.to_string(),
            CachedResult {
                response,
                cached_at: Instant::now(),
                ttl,
            },
        );
    }

    /// Update metrics.
    async fn update_metrics(
        &self,
        operation_type: &str,
        duration: Duration,
        _cache_hit: bool,
        error: Option<&BatonError>,
    ) {
        let mut metrics = self.metrics.lock().await;

        metrics.total_verifications += 1;
        metrics.last_verification_time = Some(Instant::now());

        if error.is_none() {
            metrics.successful_verifications += 1;
        } else {
            metrics.failed_verifications += 1;
        }

        // Update average verification time
        if metrics.total_verifications > 0 {
            let total_time = metrics.average_verification_time.as_millis() as u64
                * (metrics.total_verifications - 1)
                + duration.as_millis() as u64;
            metrics.average_verification_time =
                Duration::from_millis(total_time / metrics.total_verifications);
        }

        // Update operation-specific times
        let entry = metrics
            .operation_times
            .entry(operation_type.to_string())
            .or_insert(Duration::ZERO);
        *entry = (*entry + duration) / 2;

        // Update error counts
        if let Some(error) = error {
            let error_type = format!("{error:?}");
            *metrics.error_counts.entry(error_type).or_insert(0) += 1;
        }
    }

    /// Get active tasks.
    pub async fn get_active_tasks(&self) -> Vec<VerificationTask> {
        let tasks = self.active_tasks.lock().await;
        tasks.values().cloned().collect()
    }

    /// Cancel task.
    pub async fn cancel_task(&self, task_id: &str) -> bool {
        let mut tasks = self.active_tasks.lock().await;
        if let Some(task) = tasks.get_mut(task_id) {
            task.status = TaskStatus::Cancelled;
            true
        } else {
            false
        }
    }

    /// Cancel all tasks.
    pub async fn cancel_all_tasks(&self) {
        let mut tasks = self.active_tasks.lock().await;
        for task in tasks.values_mut() {
            task.status = TaskStatus::Cancelled;
        }
    }

    /// Get engine health status.
    pub async fn get_health_status(&self) -> EngineHealthStatus {
        let lean_available = self.ping().await.unwrap_or(false);
        let client_stats = self.get_client_stats();
        let metrics = self.get_metrics().await;
        let active_tasks = self.get_active_tasks().await;
        let (cache_size, _) = self.get_cache_stats().await;
        let uptime = Instant::now().duration_since(Instant::now()); // Placeholder

        EngineHealthStatus {
            lean_available,
            client_stats,
            metrics,
            active_task_count: active_tasks.len(),
            cache_size,
            uptime,
        }
    }
} 