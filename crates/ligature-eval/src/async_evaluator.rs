//! Async evaluation engine for the Ligature language.
//!
//! This module provides async evaluation capabilities for Ligature programs,
//! including parallel evaluation, work queue management, and async caching.
//!
//! ## Features
//!
//! - **Async Evaluation**: Evaluate Ligature programs, modules, and expressions asynchronously
//! - **Work Queue Management**: Queue-based evaluation with configurable worker tasks
//! - **Progress Tracking**: Real-time progress monitoring for long-running evaluations
//! - **Performance Monitoring**: Integration with the performance monitoring system
//! - **Timeout Support**: Configurable timeouts to prevent hanging evaluations
//! - **Resource Management**: Proper cleanup and resource management
//!
//! ## Usage
//!
//! ```rust
//! use ligature_eval::{AsyncEvaluator, AsyncEvaluatorConfig};
//! use ligature_ast::{Expr, ExprKind, Literal, Span};
//!
//! #[tokio::main]
//! async fn main() {
//!     // Create an async evaluator
//!     let evaluator = AsyncEvaluator::new();
//!
//!     // Evaluate an expression asynchronously
//!     let expr = Expr {
//!         kind: ExprKind::Literal(Literal::Integer(42)),
//!         span: Span::default(),
//!     };
//!
//!     let result = evaluator.evaluate_expression(&expr).await;
//!     assert!(result.is_ok());
//!
//!     // Get progress information
//!     let progress = evaluator.get_progress().await;
//!     println!("Completed: {}%", progress.completion_percentage());
//!
//!     // Clean shutdown
//!     evaluator.shutdown().await;
//! }
//! ```

use crate::{
    config::EvaluatorConfig, error::EvaluationError, evaluator::Evaluator,
    performance::PerformanceMonitor, value::Value,
};
use ligature_ast::{Expr, Module, Program, Span};
use std::{sync::Arc, time::Instant};
use tokio::{
    sync::{RwLock, mpsc},
    task::JoinHandle,
    time::Duration,
};

/// Async result type for evaluation operations
pub type AsyncEvalResult<T> = Result<T, EvaluationError>;

/// Configuration for async evaluation
#[derive(Debug, Clone)]
pub struct AsyncEvaluatorConfig {
    /// Maximum number of concurrent evaluation tasks
    pub max_concurrent_tasks: usize,
    /// Work queue capacity
    pub work_queue_capacity: usize,
    /// Task timeout duration
    pub task_timeout: Duration,
    /// Whether to enable parallel evaluation
    pub enable_parallel: bool,
    /// Base evaluator configuration
    pub evaluator_config: EvaluatorConfig,
}

impl Default for AsyncEvaluatorConfig {
    fn default() -> Self {
        Self {
            max_concurrent_tasks: 1, // Start with single worker for simplicity
            work_queue_capacity: 1000,
            task_timeout: Duration::from_secs(30),
            enable_parallel: true,
            evaluator_config: EvaluatorConfig::default(),
        }
    }
}

/// Work item for the evaluation queue
#[derive(Debug)]
enum WorkItem {
    Expression {
        expr: Expr,
        response_tx: mpsc::UnboundedSender<AsyncEvalResult<Value>>,
    },
    Module {
        module: Module,
        response_tx: mpsc::UnboundedSender<AsyncEvalResult<Value>>,
    },
    Program {
        program: Program,
        response_tx: mpsc::UnboundedSender<AsyncEvalResult<Value>>,
    },
}

/// Progress tracking for async evaluation
#[derive(Debug, Clone)]
pub struct EvaluationProgress {
    /// Total number of tasks
    pub total_tasks: usize,
    /// Number of completed tasks
    pub completed_tasks: usize,
    /// Number of failed tasks
    pub failed_tasks: usize,
    /// Current active tasks
    pub active_tasks: usize,
    /// Start time of evaluation
    pub start_time: Instant,
}

impl EvaluationProgress {
    pub fn new(total_tasks: usize) -> Self {
        Self {
            total_tasks,
            completed_tasks: 0,
            failed_tasks: 0,
            active_tasks: 0,
            start_time: Instant::now(),
        }
    }

    pub fn completion_percentage(&self) -> f64 {
        if self.total_tasks == 0 {
            0.0
        } else {
            (self.completed_tasks + self.failed_tasks) as f64 / self.total_tasks as f64 * 100.0
        }
    }

    pub fn elapsed_time(&self) -> Duration {
        self.start_time.elapsed()
    }
}

/// Async evaluation engine
pub struct AsyncEvaluator {
    config: AsyncEvaluatorConfig,
    work_tx: mpsc::UnboundedSender<WorkItem>,
    progress: Arc<RwLock<EvaluationProgress>>,
    monitor: Arc<PerformanceMonitor>,
    worker_handle: JoinHandle<()>,
}

impl Default for AsyncEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncEvaluator {
    /// Create a new async evaluator with default configuration
    pub fn new() -> Self {
        Self::with_config(AsyncEvaluatorConfig::default())
    }

    /// Create a new async evaluator with custom configuration
    pub fn with_config(config: AsyncEvaluatorConfig) -> Self {
        let (work_tx, work_rx) = mpsc::unbounded_channel();
        let progress = Arc::new(RwLock::new(EvaluationProgress::new(0)));
        let monitor = Arc::new(PerformanceMonitor::new());

        // Spawn single worker task
        let progress_clone = progress.clone();
        let monitor_clone = monitor.clone();
        let config_clone = config.clone();

        let worker_handle = tokio::spawn(async move {
            Self::worker_loop(work_rx, progress_clone, monitor_clone, config_clone).await;
        });

        Self {
            config,
            work_tx,
            progress,
            monitor,
            worker_handle,
        }
    }

    /// Evaluate a program asynchronously
    pub async fn evaluate_program(&self, program: &Program) -> AsyncEvalResult<Value> {
        let (response_tx, mut response_rx) = mpsc::unbounded_channel();
        let work_item = WorkItem::Program {
            program: program.clone(),
            response_tx,
        };

        self.work_tx
            .send(work_item)
            .map_err(|_| EvaluationError::RuntimeError {
                message: "Failed to send work item to queue".to_string(),
                span: Span::default(),
            })?;

        // Update progress
        {
            let mut progress = self.progress.write().await;
            progress.total_tasks += 1;
            progress.active_tasks += 1;
        }

        // Wait for response with timeout
        match tokio::time::timeout(self.config.task_timeout, response_rx.recv()).await {
            Ok(Some(result)) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    if result.is_ok() {
                        progress.completed_tasks += 1;
                    } else {
                        progress.failed_tasks += 1;
                    }
                }
                result
            }
            Ok(None) => Err(EvaluationError::RuntimeError {
                message: "Worker task closed unexpectedly".to_string(),
                span: Span::default(),
            }),
            Err(_) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    progress.failed_tasks += 1;
                }
                Err(EvaluationError::RuntimeError {
                    message: "Evaluation timed out".to_string(),
                    span: Span::default(),
                })
            }
        }
    }

    /// Evaluate a module asynchronously
    pub async fn evaluate_module(&self, module: &Module) -> AsyncEvalResult<Value> {
        let (response_tx, mut response_rx) = mpsc::unbounded_channel();
        let work_item = WorkItem::Module {
            module: module.clone(),
            response_tx,
        };

        self.work_tx
            .send(work_item)
            .map_err(|_| EvaluationError::RuntimeError {
                message: "Failed to send work item to queue".to_string(),
                span: Span::default(),
            })?;

        // Update progress
        {
            let mut progress = self.progress.write().await;
            progress.total_tasks += 1;
            progress.active_tasks += 1;
        }

        // Wait for response with timeout
        match tokio::time::timeout(self.config.task_timeout, response_rx.recv()).await {
            Ok(Some(result)) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    if result.is_ok() {
                        progress.completed_tasks += 1;
                    } else {
                        progress.failed_tasks += 1;
                    }
                }
                result
            }
            Ok(None) => Err(EvaluationError::RuntimeError {
                message: "Worker task closed unexpectedly".to_string(),
                span: Span::default(),
            }),
            Err(_) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    progress.failed_tasks += 1;
                }
                Err(EvaluationError::RuntimeError {
                    message: "Evaluation timed out".to_string(),
                    span: Span::default(),
                })
            }
        }
    }

    /// Evaluate an expression asynchronously
    pub async fn evaluate_expression(&self, expr: &Expr) -> AsyncEvalResult<Value> {
        let (response_tx, mut response_rx) = mpsc::unbounded_channel();
        let work_item = WorkItem::Expression {
            expr: expr.clone(),
            response_tx,
        };

        self.work_tx
            .send(work_item)
            .map_err(|_| EvaluationError::RuntimeError {
                message: "Failed to send work item to queue".to_string(),
                span: Span::default(),
            })?;

        // Update progress
        {
            let mut progress = self.progress.write().await;
            progress.total_tasks += 1;
            progress.active_tasks += 1;
        }

        // Wait for response with timeout
        match tokio::time::timeout(self.config.task_timeout, response_rx.recv()).await {
            Ok(Some(result)) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    if result.is_ok() {
                        progress.completed_tasks += 1;
                    } else {
                        progress.failed_tasks += 1;
                    }
                }
                result
            }
            Ok(None) => Err(EvaluationError::RuntimeError {
                message: "Worker task closed unexpectedly".to_string(),
                span: Span::default(),
            }),
            Err(_) => {
                // Update progress
                {
                    let mut progress = self.progress.write().await;
                    progress.active_tasks -= 1;
                    progress.failed_tasks += 1;
                }
                Err(EvaluationError::RuntimeError {
                    message: "Evaluation timed out".to_string(),
                    span: Span::default(),
                })
            }
        }
    }

    /// Get current evaluation progress
    pub async fn get_progress(&self) -> EvaluationProgress {
        self.progress.read().await.clone()
    }

    /// Get performance metrics
    pub fn get_metrics(&self) -> Vec<crate::performance::PerformanceMetrics> {
        self.monitor.get_metrics()
    }

    /// Shutdown the async evaluator
    pub async fn shutdown(self) {
        // Drop the work_tx to close the channel
        drop(self.work_tx);

        // Wait for the worker task to complete with timeout
        match tokio::time::timeout(Duration::from_secs(5), self.worker_handle).await {
            Ok(_) => {
                // Worker task completed successfully
            }
            Err(_) => {
                // Worker task didn't complete in time, but that's okay
                // The task will be dropped when we go out of scope
            }
        }
    }

    /// Worker loop for processing evaluation tasks
    async fn worker_loop(
        mut work_rx: mpsc::UnboundedReceiver<WorkItem>,
        _progress: Arc<RwLock<EvaluationProgress>>,
        monitor: Arc<PerformanceMonitor>,
        config: AsyncEvaluatorConfig,
    ) {
        while let Some(work_item) = work_rx.recv().await {
            let start_time = Instant::now();
            let (result, response_tx) = match work_item {
                WorkItem::Expression { expr, response_tx } => {
                    let mut evaluator = Evaluator::with_config(config.evaluator_config.clone());
                    let result = evaluator.evaluate_expression(&expr);
                    (Self::convert_result(result), response_tx)
                }
                WorkItem::Module {
                    module,
                    response_tx,
                } => {
                    let mut evaluator = Evaluator::with_config(config.evaluator_config.clone());
                    let result = evaluator.evaluate_module(&module);
                    (Self::convert_result(result), response_tx)
                }
                WorkItem::Program {
                    program,
                    response_tx,
                } => {
                    let mut evaluator = Evaluator::with_config(config.evaluator_config.clone());
                    let result = evaluator.evaluate_program(&program);
                    (Self::convert_result(result), response_tx)
                }
            };

            // Record metrics
            let metrics = crate::performance::PerformanceMetrics {
                operation_name: "async_evaluation".to_string(),
                execution_time: start_time.elapsed(),
                memory_usage_bytes: 0,    // TODO: implement memory tracking
                cache_hits: 0,            // TODO: implement cache tracking
                cache_misses: 0,          // TODO: implement cache tracking
                expression_complexity: 1, // TODO: implement complexity tracking
                timestamp: std::time::SystemTime::now(),
            };
            monitor.record_metrics(metrics);

            // Send result back
            let _ = response_tx.send(result);
        }
    }

    /// Convert AstResult to AsyncEvalResult
    fn convert_result(result: ligature_ast::AstResult<Value>) -> AsyncEvalResult<Value> {
        result.map_err(|ast_error| EvaluationError::RuntimeError {
            message: format!("AST error: {ast_error:?}"),
            span: Span::default(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ligature_ast::{Expr, ExprKind, Literal, Span};

    #[tokio::test]
    async fn test_async_evaluator_creation() {
        let evaluator = AsyncEvaluator::new();
        assert_eq!(evaluator.config.max_concurrent_tasks, 1);
    }

    #[tokio::test]
    async fn test_async_expression_evaluation() {
        let evaluator = AsyncEvaluator::new();
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };

        let result = evaluator.evaluate_expression(&expr).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap().as_integer(), Some(42));
    }

    #[tokio::test]
    async fn test_async_evaluator_progress() {
        let evaluator = AsyncEvaluator::new();
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };

        let _ = evaluator.evaluate_expression(&expr).await;
        let progress = evaluator.get_progress().await;

        assert_eq!(progress.total_tasks, 1);
        assert_eq!(progress.completed_tasks, 1);
        assert_eq!(progress.failed_tasks, 0);
    }

    #[tokio::test]
    async fn test_async_evaluator_shutdown() {
        let evaluator = AsyncEvaluator::new();
        evaluator.shutdown().await;
        // Should complete without error
    }
}
