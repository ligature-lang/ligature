//! Evaluation engine for the Ligature language.
//!
//! This crate provides evaluation capabilities for Ligature programs,
//! including both sequential and concurrent evaluation strategies.

pub mod adaptive_optimizer;
pub mod advanced_optimizations;
pub mod benchmarks;
pub mod concurrent;
pub mod concurrent_type_checker;
pub mod config;
pub mod enhanced_async_evaluator;
pub mod environment;
pub mod error;
pub mod evaluator;
pub mod memory;
pub mod parallel;
pub mod performance;
pub mod resolver;
pub mod validation;
pub mod value;

// Re-export main types
pub use adaptive_optimizer::{AdaptiveOptimizer, AdaptiveOptimizerConfig};
pub use concurrent::{
    CacheKey, ConcurrentExpressionCache, ConcurrentTypeEnvironment, ConcurrentValueCache,
};
pub use concurrent_type_checker::{
    ConcurrentConstraintSolver, ConcurrentTypeChecker, Constraint, ConstraintId, Solution,
    TypeSubstitution,
};
pub use config::EvaluatorConfig;
pub use enhanced_async_evaluator::{EnhancedAsyncEvaluator, EnhancedAsyncEvaluatorConfig};
pub use environment::EvaluationEnvironment;
pub use error::EvaluationError;
pub use evaluator::Evaluator;
pub use parallel::{
    ParallelEvaluator, ParallelEvaluatorConfig, Task, TaskId, TaskStatus, WorkQueue, Worker,
};
pub use performance::{
    PerformanceConfig, PerformanceMetrics, PerformanceMonitor, PerformanceReport,
};
pub use value::Value;

// Re-export common types from dependencies
pub use ligature_ast::{AstResult, Expr, Module, Program, Type};

/// Evaluate a complete program using the default evaluator.
pub fn evaluate_program(program: &Program) -> AstResult<Value> {
    let mut evaluator = Evaluator::new();
    evaluator.evaluate_program(program)
}

/// Evaluate a single expression using the default evaluator.
pub fn evaluate_expression(expr: &Expr) -> AstResult<Value> {
    let mut evaluator = Evaluator::new();
    evaluator.evaluate_expression(expr)
}
