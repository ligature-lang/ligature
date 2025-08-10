//! Async evaluation service for the Ligature LSP server.
//!
//! This module provides asynchronous evaluation capabilities for the LSP server,
//! enabling efficient evaluation of large configurations and real-time feedback.

use std::sync::Arc;
use std::time::Duration;

use ligature_ast::Program;
use ligature_eval::enhanced_async_evaluator::{
    EnhancedAsyncEvaluator, EnhancedAsyncEvaluatorConfig, PerformanceMetrics,
};
use ligature_eval::value::Value;
use tokio::sync::RwLock;
use tower_lsp::lsp_types::ProgressToken;

use crate::server::ServerError;

/// Type alias for the evaluation cache
type EvaluationCache = Arc<RwLock<std::collections::HashMap<String, AsyncEvaluationResult>>>;

/// Configuration for the async evaluation service.
#[derive(Debug, Clone)]
pub struct AsyncEvaluationConfig {
    /// Whether to enable async evaluation.
    pub enable_async_evaluation: bool,
    /// Maximum evaluation time for a single expression.
    pub max_evaluation_time: Duration,
    /// Whether to show progress for long-running evaluations.
    pub show_progress: bool,
    /// Whether to cache evaluation results.
    pub enable_caching: bool,
    /// Maximum cache size.
    pub max_cache_size: usize,
}

impl Default for AsyncEvaluationConfig {
    fn default() -> Self {
        Self {
            enable_async_evaluation: true,
            max_evaluation_time: Duration::from_secs(30),
            show_progress: true,
            enable_caching: true,
            max_cache_size: 1000,
        }
    }
}

/// Result of an async evaluation.
#[derive(Debug, Clone)]
pub struct AsyncEvaluationResult {
    /// The evaluated values.
    pub values: Vec<Value>,
    /// Performance metrics.
    pub metrics: PerformanceMetrics,
    /// Whether the evaluation was successful.
    pub success: bool,
    /// Error message if evaluation failed.
    pub error: Option<String>,
    /// Evaluation time.
    pub evaluation_time: Duration,
}

/// Service for handling async evaluation in the LSP server.
#[derive(Clone)]
pub struct AsyncEvaluationService {
    /// The async evaluator.
    evaluator: Option<Arc<EnhancedAsyncEvaluator>>,
    /// Configuration.
    config: AsyncEvaluationConfig,
    /// Cache for evaluation results.
    cache: EvaluationCache,
    /// Progress token for reporting progress.
    progress_token: Option<ProgressToken>,
}

impl AsyncEvaluationService {
    /// Create a new async evaluation service.
    pub fn new(config: AsyncEvaluationConfig) -> std::result::Result<Self, ServerError> {
        let evaluator = if config.enable_async_evaluation {
            let eval_config = EnhancedAsyncEvaluatorConfig {
                num_workers: num_cpus::get(),
                expression_cache_size: config.max_cache_size,
                value_cache_size: config.max_cache_size / 2,
                max_cache_memory: 1000000,
                task_timeout: config.max_evaluation_time,
                enable_concurrent_type_checking: true,
                enable_expression_caching: config.enable_caching,
                enable_value_caching: config.enable_caching,
                enable_performance_monitoring: true,
            };

            match EnhancedAsyncEvaluator::new(eval_config) {
                Ok(evaluator) => Some(Arc::new(evaluator)),
                Err(e) => {
                    return Err(ServerError::Configuration(format!(
                        "Failed to create async evaluator: {e}"
                    )));
                }
            }
        } else {
            None
        };

        Ok(Self {
            evaluator,
            config,
            cache: Arc::new(RwLock::new(std::collections::HashMap::new())),
            progress_token: None,
        })
    }

    /// Set the progress token for reporting progress.
    pub fn set_progress_token(&mut self, token: ProgressToken) {
        self.progress_token = Some(token);
    }

    /// Evaluate a program asynchronously.
    pub async fn evaluate_program(
        &self,
        program: &Program,
        cache_key: Option<&str>,
    ) -> std::result::Result<AsyncEvaluationResult, ServerError> {
        let start_time = std::time::Instant::now();

        // Check cache first
        if let Some(key) = cache_key {
            if let Some(cached_result) = self.cache.read().await.get(key) {
                return Ok(cached_result.clone());
            }
        }

        // Report progress if enabled
        if self.config.show_progress {
            self.report_progress("Evaluating program...".to_string())
                .await;
        }

        // Evaluate the program
        let evaluator = self.evaluator.as_ref().ok_or_else(|| {
            ServerError::Configuration("Async evaluation is disabled".to_string())
        })?;

        let evaluation_result = match evaluator.evaluate_program(program).await {
            Ok(values) => {
                let metrics = evaluator.performance_metrics().await;
                AsyncEvaluationResult {
                    values,
                    metrics,
                    success: true,
                    error: None,
                    evaluation_time: start_time.elapsed(),
                }
            }
            Err(e) => {
                let metrics = evaluator.performance_metrics().await;
                AsyncEvaluationResult {
                    values: Vec::new(),
                    metrics,
                    success: false,
                    error: Some(format!("Evaluation error: {e}")),
                    evaluation_time: start_time.elapsed(),
                }
            }
        };

        // Cache the result if caching is enabled
        if self.config.enable_caching {
            if let Some(key) = cache_key {
                self.cache
                    .write()
                    .await
                    .insert(key.to_string(), evaluation_result.clone());
            }
        }

        // Report completion
        if self.config.show_progress {
            self.report_progress_complete().await;
        }

        Ok(evaluation_result)
    }

    /// Evaluate an expression asynchronously.
    pub async fn evaluate_expression(
        &self,
        expression: &ligature_ast::Expr,
        cache_key: Option<&str>,
    ) -> std::result::Result<AsyncEvaluationResult, ServerError> {
        let start_time = std::time::Instant::now();

        // Check cache first
        if let Some(key) = cache_key {
            if let Some(cached_result) = self.cache.read().await.get(key) {
                return Ok(cached_result.clone());
            }
        }

        // Report progress if enabled
        if self.config.show_progress {
            self.report_progress("Evaluating expression...".to_string())
                .await;
        }

        // Evaluate the expression
        let evaluator = self.evaluator.as_ref().ok_or_else(|| {
            ServerError::Configuration("Async evaluation is disabled".to_string())
        })?;

        let evaluation_result = match evaluator
            .evaluate_expression(expression, &Default::default())
            .await
        {
            Ok(value) => {
                let metrics = evaluator.performance_metrics().await;
                AsyncEvaluationResult {
                    values: vec![value],
                    metrics,
                    success: true,
                    error: None,
                    evaluation_time: start_time.elapsed(),
                }
            }
            Err(e) => {
                let metrics = evaluator.performance_metrics().await;
                AsyncEvaluationResult {
                    values: Vec::new(),
                    metrics,
                    success: false,
                    error: Some(format!("Evaluation error: {e}")),
                    evaluation_time: start_time.elapsed(),
                }
            }
        };

        // Cache the result if caching is enabled
        if self.config.enable_caching {
            if let Some(key) = cache_key {
                self.cache
                    .write()
                    .await
                    .insert(key.to_string(), evaluation_result.clone());
            }
        }

        // Report completion
        if self.config.show_progress {
            self.report_progress_complete().await;
        }

        Ok(evaluation_result)
    }

    /// Get performance metrics.
    pub async fn get_performance_metrics(&self) -> Option<PerformanceMetrics> {
        if let Some(evaluator) = &self.evaluator {
            Some(evaluator.performance_metrics().await)
        } else {
            None
        }
    }

    /// Clear the evaluation cache.
    pub async fn clear_cache(&self) {
        self.cache.write().await.clear();
        if let Some(evaluator) = &self.evaluator {
            evaluator.clear_caches();
        }
    }

    /// Get cache statistics.
    pub async fn get_cache_stats(&self) -> std::collections::HashMap<String, usize> {
        if let Some(evaluator) = &self.evaluator {
            evaluator.stats()
        } else {
            std::collections::HashMap::new()
        }
    }

    /// Report progress to the client.
    async fn report_progress(&self, message: String) {
        if let Some(_token) = &self.progress_token {
            // Note: In a real implementation, you would send a progress notification
            // to the LSP client. For now, we'll just log it.
            tracing::info!("Progress: {}", message);
        }
    }

    /// Report progress completion.
    async fn report_progress_complete(&self) {
        if let Some(_token) = &self.progress_token {
            // Note: In a real implementation, you would send a progress complete notification
            // to the LSP client. For now, we'll just log it.
            tracing::info!("Progress complete");
        }
    }

    /// Update the configuration.
    pub fn update_config(
        &mut self,
        config: AsyncEvaluationConfig,
    ) -> std::result::Result<(), ServerError> {
        self.config = config;

        // Recreate the evaluator if needed
        if self.config.enable_async_evaluation && self.evaluator.is_none() {
            let eval_config = EnhancedAsyncEvaluatorConfig {
                num_workers: num_cpus::get(),
                expression_cache_size: self.config.max_cache_size,
                value_cache_size: self.config.max_cache_size / 2,
                max_cache_memory: 1000000,
                task_timeout: self.config.max_evaluation_time,
                enable_concurrent_type_checking: true,
                enable_expression_caching: self.config.enable_caching,
                enable_value_caching: self.config.enable_caching,
                enable_performance_monitoring: true,
            };

            match EnhancedAsyncEvaluator::new(eval_config) {
                Ok(evaluator) => {
                    self.evaluator = Some(Arc::new(evaluator));
                }
                Err(e) => {
                    return Err(ServerError::Configuration(format!(
                        "Failed to create async evaluator: {e}"
                    )));
                }
            }
        }

        Ok(())
    }
}

impl Default for AsyncEvaluationService {
    fn default() -> Self {
        Self::new(AsyncEvaluationConfig::default()).unwrap_or_else(|_| Self {
            evaluator: None,
            config: AsyncEvaluationConfig::default(),
            cache: Arc::new(RwLock::new(std::collections::HashMap::new())),
            progress_token: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use ligature_parser::parse_program;

    use super::*;

    #[tokio::test]
    async fn test_async_evaluation_service_creation() {
        let config = AsyncEvaluationConfig::default();
        let service = AsyncEvaluationService::new(config);
        assert!(service.is_ok());
    }

    #[tokio::test]
    async fn test_async_evaluation_service_disabled() {
        let config = AsyncEvaluationConfig {
            enable_async_evaluation: false,
            ..Default::default()
        };
        let service = AsyncEvaluationService::new(config);
        assert!(service.is_ok());
    }

    #[tokio::test]
    async fn test_evaluate_simple_program() {
        let config = AsyncEvaluationConfig::default();
        let service = AsyncEvaluationService::new(config).unwrap();

        let program_str = "let x = 42;";
        let program = parse_program(program_str).unwrap();

        let result = service.evaluate_program(&program, Some("test")).await;
        assert!(result.is_ok());

        let evaluation_result = result.unwrap();
        assert!(evaluation_result.success);
        assert_eq!(evaluation_result.values.len(), 1);
    }

    #[tokio::test]
    async fn test_evaluate_simple_expression() {
        let config = AsyncEvaluationConfig::default();
        let service = AsyncEvaluationService::new(config).unwrap();

        let expr_str = "let x = 2 + 3;";
        let program = parse_program(expr_str).unwrap();

        // Get the first declaration and extract the expression from it
        if let Some(decl) = program.declarations.first() {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &decl.kind {
                let result = service
                    .evaluate_expression(&value_decl.value, Some("test_expr"))
                    .await;
                assert!(result.is_ok());

                let evaluation_result = result.unwrap();
                assert!(evaluation_result.success);
                assert_eq!(evaluation_result.values.len(), 1);
            }
        }
    }

    #[tokio::test]
    async fn test_cache_functionality() {
        let config = AsyncEvaluationConfig::default();
        let service = AsyncEvaluationService::new(config).unwrap();

        let program_str = "let x = 42;";
        let program = parse_program(program_str).unwrap();

        // First evaluation
        let result1 = service.evaluate_program(&program, Some("cache_test")).await;
        assert!(result1.is_ok());

        // Second evaluation (should use cache)
        let result2 = service.evaluate_program(&program, Some("cache_test")).await;
        assert!(result2.is_ok());

        // Both should be successful
        assert!(result1.unwrap().success);
        assert!(result2.unwrap().success);
    }

    #[tokio::test]
    async fn test_clear_cache() {
        let config = AsyncEvaluationConfig::default();
        let service = AsyncEvaluationService::new(config).unwrap();

        let program_str = "let x = 42;";
        let program = parse_program(program_str).unwrap();

        // First evaluation
        let _result1 = service.evaluate_program(&program, Some("clear_test")).await;

        // Clear cache
        service.clear_cache().await;

        // Second evaluation (should not use cache)
        let result2 = service.evaluate_program(&program, Some("clear_test")).await;
        assert!(result2.is_ok());
    }
}
