//! Enhanced asynchronous evaluator for the Ligature language.
//!
//! This module provides advanced asynchronous evaluation capabilities
//! including concurrent execution, caching, and performance optimizations.

use crate::{
    concurrent::{ConcurrentExpressionCache, ConcurrentTypeEnvironment, ConcurrentValueCache},
    concurrent_type_checker::ConcurrentTypeChecker,
    environment::EvaluationEnvironment,
    value::Value,
};
use dashmap::DashMap;
use ligature_ast::{AstError, AstResult, Expr, Program, Span};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// Configuration for the enhanced async evaluator
#[derive(Debug, Clone)]
pub struct EnhancedAsyncEvaluatorConfig {
    /// Number of worker threads for concurrent evaluation
    pub num_workers: usize,
    /// Maximum cache size for expressions
    pub expression_cache_size: usize,
    /// Maximum cache size for values
    pub value_cache_size: usize,
    /// Maximum memory usage for caches in bytes
    pub max_cache_memory: usize,
    /// Task timeout for evaluation
    pub task_timeout: Duration,
    /// Whether to enable concurrent type checking
    pub enable_concurrent_type_checking: bool,
    /// Whether to enable expression caching
    pub enable_expression_caching: bool,
    /// Whether to enable value caching
    pub enable_value_caching: bool,
    /// Whether to enable performance monitoring
    pub enable_performance_monitoring: bool,
}

impl Default for EnhancedAsyncEvaluatorConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus::get(),
            expression_cache_size: 10000,
            value_cache_size: 5000,
            max_cache_memory: 1000000,
            task_timeout: Duration::from_secs(30),
            enable_concurrent_type_checking: true,
            enable_expression_caching: true,
            enable_value_caching: true,
            enable_performance_monitoring: true,
        }
    }
}

/// Performance metrics for the enhanced evaluator
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    /// Total evaluation time
    pub total_evaluation_time: Duration,
    /// Time spent in type checking
    pub type_checking_time: Duration,
    /// Time spent in expression evaluation
    pub expression_evaluation_time: Duration,
    /// Number of cache hits
    pub cache_hits: usize,
    /// Number of cache misses
    pub cache_misses: usize,
    /// Number of concurrent tasks executed
    pub concurrent_tasks: usize,
    /// Memory usage in bytes
    pub memory_usage: usize,
}

impl PerformanceMetrics {
    /// Create new performance metrics
    pub fn new() -> Self {
        Self {
            total_evaluation_time: Duration::ZERO,
            type_checking_time: Duration::ZERO,
            expression_evaluation_time: Duration::ZERO,
            cache_hits: 0,
            cache_misses: 0,
            concurrent_tasks: 0,
            memory_usage: 0,
        }
    }

    /// Get cache hit rate
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }

    /// Get average evaluation time per task
    pub fn average_evaluation_time(&self) -> Duration {
        if self.concurrent_tasks == 0 {
            Duration::ZERO
        } else {
            self.total_evaluation_time / self.concurrent_tasks as u32
        }
    }
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

/// Enhanced asynchronous evaluator for Ligature programs
#[derive(Debug)]
pub struct EnhancedAsyncEvaluator {
    /// Configuration
    config: EnhancedAsyncEvaluatorConfig,
    /// Expression cache
    expression_cache: Option<Arc<ConcurrentExpressionCache>>,
    /// Value cache
    value_cache: Option<Arc<ConcurrentValueCache>>,
    /// Type environment
    type_environment: Arc<ConcurrentTypeEnvironment>,
    /// Concurrent type checker
    type_checker: Option<ConcurrentTypeChecker>,
    /// Performance metrics
    metrics: Arc<RwLock<PerformanceMetrics>>,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl EnhancedAsyncEvaluator {
    /// Create a new enhanced async evaluator
    pub fn new(config: EnhancedAsyncEvaluatorConfig) -> AstResult<Self> {
        let expression_cache = if config.enable_expression_caching {
            Some(Arc::new(ConcurrentExpressionCache::new(
                config.expression_cache_size,
            )))
        } else {
            None
        };

        let value_cache = if config.enable_value_caching {
            Some(Arc::new(ConcurrentValueCache::new(config.value_cache_size)))
        } else {
            None
        };

        let type_checker = if config.enable_concurrent_type_checking {
            Some(ConcurrentTypeChecker::new(config.num_workers))
        } else {
            None
        };

        Ok(Self {
            config,
            expression_cache,
            value_cache,
            type_environment: Arc::new(ConcurrentTypeEnvironment::new()),
            type_checker,
            metrics: Arc::new(RwLock::new(PerformanceMetrics::new())),
            stats: Arc::new(DashMap::new()),
        })
    }

    /// Evaluate a program asynchronously
    pub async fn evaluate_program(&self, program: &Program) -> AstResult<Vec<Value>> {
        let start_time = Instant::now();

        // Type check the program if enabled
        if let Some(ref type_checker) = self.type_checker {
            let type_check_start = Instant::now();
            type_checker.check_program_parallel(program).await?;
            let type_check_time = type_check_start.elapsed();

            if self.config.enable_performance_monitoring {
                let mut metrics = self.metrics.write().await;
                metrics.type_checking_time += type_check_time;
            }
        }

        // Evaluate all declarations concurrently
        let mut evaluation_handles = Vec::new();

        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                let evaluator = self.clone();
                let expr = value_decl.value.clone();
                let env = EvaluationEnvironment::new();

                let handle =
                    tokio::spawn(async move { evaluator.evaluate_expression(&expr, &env).await });

                evaluation_handles.push(handle);
            }
        }

        // Wait for all evaluations to complete
        let evaluation_start = Instant::now();
        let results = futures::future::join_all(evaluation_handles).await;
        let evaluation_time = evaluation_start.elapsed();
        let results_len = results.len();

        // Collect results and handle errors
        let mut values = Vec::new();
        for result in results {
            match result {
                Ok(Ok(value)) => values.push(value),
                Ok(Err(error)) => return Err(error),
                Err(join_error) => {
                    return Err(AstError::InternalError {
                        message: format!("Task join error: {join_error}"),
                        span: Span::default(),
                    });
                }
            }
        }

        // Update performance metrics
        if self.config.enable_performance_monitoring {
            let mut metrics = self.metrics.write().await;
            metrics.total_evaluation_time = start_time.elapsed();
            metrics.expression_evaluation_time += evaluation_time;
            metrics.concurrent_tasks += results_len;
        }

        Ok(values)
    }

    /// Evaluate a single expression asynchronously
    pub async fn evaluate_expression(
        &self,
        expr: &Expr,
        env: &EvaluationEnvironment,
    ) -> AstResult<Value> {
        // Check expression cache first
        if let Some(ref cache) = self.expression_cache {
            let cache_key = crate::concurrent::CacheKey::new(expr, env, 0);
            if let Some(cached_value) = cache.get(&cache_key) {
                if self.config.enable_performance_monitoring {
                    let mut metrics = self.metrics.write().await;
                    metrics.cache_hits += 1;
                }
                return Ok(cached_value);
            }
        }

        if self.config.enable_performance_monitoring {
            let mut metrics = self.metrics.write().await;
            metrics.cache_misses += 1;
        }

        // Evaluate the expression
        let result = self.do_evaluate_expression(expr, env).await;

        // Cache the result if successful
        if let (Ok(value), Some(cache)) = (&result, &self.expression_cache) {
            let cache_key = crate::concurrent::CacheKey::new(expr, env, 0);
            cache.put(cache_key, value.clone());
        }

        result
    }

    /// Perform the actual expression evaluation
    async fn do_evaluate_expression(
        &self,
        expr: &Expr,
        env: &EvaluationEnvironment,
    ) -> AstResult<Value> {
        match &expr.kind {
            ligature_ast::ExprKind::Literal(literal) => match literal {
                ligature_ast::Literal::Integer(i) => Ok(Value::integer(*i, expr.span)),
                ligature_ast::Literal::Float(f) => Ok(Value::float(*f, expr.span)),
                ligature_ast::Literal::String(s) => Ok(Value::string(s.clone(), expr.span)),
                ligature_ast::Literal::Boolean(b) => Ok(Value::boolean(*b, expr.span)),
                ligature_ast::Literal::Unit => Ok(Value::unit(expr.span)),
                ligature_ast::Literal::List(elements) => {
                    let mut evaluated_elements = Vec::new();
                    for element in elements {
                        let evaluated = Box::pin(self.evaluate_expression(element, env)).await?;
                        evaluated_elements.push(evaluated);
                    }
                    Ok(Value::list(evaluated_elements, expr.span))
                }
            },
            ligature_ast::ExprKind::Variable(name) => {
                env.lookup(name)
                    .ok_or_else(|| AstError::UndefinedIdentifier {
                        name: name.clone(),
                        span: expr.span,
                    })
            }
            ligature_ast::ExprKind::Application { function, argument } => {
                let function_value = Box::pin(self.evaluate_expression(function, env)).await?;
                let argument_value = Box::pin(self.evaluate_expression(argument, env)).await?;

                // Apply the function (simplified)
                self.apply_function(&function_value, &argument_value, expr.span)
                    .await
            }
            ligature_ast::ExprKind::Abstraction {
                parameter, body, ..
            } => {
                // Create a closure
                Ok(Value::function(
                    parameter.clone(),
                    body.as_ref().clone(),
                    expr.span,
                ))
            }
            ligature_ast::ExprKind::Let { name, value, body } => {
                let value_result = Box::pin(self.evaluate_expression(value, env)).await?;
                let mut new_env = env.clone();
                new_env.bind(name.clone(), value_result);
                Box::pin(self.evaluate_expression(body, &new_env)).await
            }
            ligature_ast::ExprKind::Record { fields } => {
                let mut record_fields = std::collections::HashMap::new();
                for field in fields {
                    let field_value = Box::pin(self.evaluate_expression(&field.value, env)).await?;
                    record_fields.insert(field.name.clone(), field_value);
                }
                Ok(Value::record(record_fields, expr.span))
            }
            ligature_ast::ExprKind::FieldAccess { record, field } => {
                let record_value = Box::pin(self.evaluate_expression(record, env)).await?;

                if let Some(record_fields) = record_value.as_record() {
                    record_fields
                        .get(field)
                        .cloned()
                        .ok_or(AstError::InvalidExpression { span: expr.span })
                } else {
                    Err(AstError::InvalidExpression { span: expr.span })
                }
            }
            ligature_ast::ExprKind::Union { variant, value } => {
                let union_value = if let Some(val) = value {
                    Some(Box::pin(self.evaluate_expression(val, env)).await?)
                } else {
                    None
                };
                Ok(Value::union(variant.clone(), union_value, expr.span))
            }
            ligature_ast::ExprKind::Match { scrutinee, cases } => {
                let scrutinee_value = Box::pin(self.evaluate_expression(scrutinee, env)).await?;

                for case in cases {
                    if self.match_pattern(&scrutinee_value, &case.pattern) {
                        return Box::pin(self.evaluate_expression(&case.expression, env)).await;
                    }
                }

                Err(AstError::InvalidExpression { span: expr.span })
            }
            ligature_ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_value = Box::pin(self.evaluate_expression(condition, env)).await?;

                if let Some(condition_bool) = condition_value.as_boolean() {
                    if condition_bool {
                        Box::pin(self.evaluate_expression(then_branch, env)).await
                    } else {
                        Box::pin(self.evaluate_expression(else_branch, env)).await
                    }
                } else {
                    Err(AstError::InvalidExpression { span: expr.span })
                }
            }
            ligature_ast::ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                let left_value = Box::pin(self.evaluate_expression(left, env)).await?;
                let right_value = Box::pin(self.evaluate_expression(right, env)).await?;

                self.apply_binary_operator(operator, &left_value, &right_value, expr.span)
                    .await
            }
            ligature_ast::ExprKind::UnaryOp { operator, operand } => {
                let operand_value = Box::pin(self.evaluate_expression(operand, env)).await?;

                self.apply_unary_operator(operator, &operand_value, expr.span)
                    .await
            }
            ligature_ast::ExprKind::Annotated { expression, .. } => {
                Box::pin(self.evaluate_expression(expression, env)).await
            }
        }
    }

    /// Apply a function to an argument
    async fn apply_function(
        &self,
        function: &Value,
        argument: &Value,
        span: Span,
    ) -> AstResult<Value> {
        // Simplified function application
        match function {
            Value {
                kind: crate::value::ValueKind::Function { parameter, body },
                ..
            } => {
                let mut new_env = EvaluationEnvironment::new();
                new_env.bind(parameter.as_ref().clone(), argument.clone());
                Box::pin(self.evaluate_expression(body, &new_env)).await
            }
            Value {
                kind:
                    crate::value::ValueKind::Closure {
                        parameter,
                        body,
                        environment,
                    },
                ..
            } => {
                let env_copy = environment.clone();
                let mut env_copy = (*env_copy).clone();
                env_copy.bind(parameter.as_ref().clone(), argument.clone());
                Box::pin(self.evaluate_expression(body, &env_copy)).await
            }
            _ => Err(AstError::InvalidExpression { span }),
        }
    }

    /// Apply a binary operator
    async fn apply_binary_operator(
        &self,
        operator: &ligature_ast::BinaryOperator,
        left: &Value,
        right: &Value,
        span: Span,
    ) -> AstResult<Value> {
        left.apply_binary_op(operator, right)
            .map_err(|e| AstError::InternalError { message: e, span })
    }

    /// Apply a unary operator
    async fn apply_unary_operator(
        &self,
        operator: &ligature_ast::UnaryOperator,
        operand: &Value,
        span: Span,
    ) -> AstResult<Value> {
        operand
            .apply_unary_op(operator)
            .map_err(|e| AstError::InternalError { message: e, span })
    }

    /// Match a value against a pattern
    #[allow(clippy::only_used_in_recursion)]
    fn match_pattern(&self, value: &Value, pattern: &ligature_ast::Pattern) -> bool {
        match pattern {
            ligature_ast::Pattern::Wildcard => true,
            ligature_ast::Pattern::Variable(_) => true,
            ligature_ast::Pattern::Literal(literal) => match (value, literal) {
                (
                    Value {
                        kind: crate::value::ValueKind::Integer(v),
                        ..
                    },
                    ligature_ast::Literal::Integer(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::String(v),
                        ..
                    },
                    ligature_ast::Literal::String(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::Boolean(v),
                        ..
                    },
                    ligature_ast::Literal::Boolean(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::Float(v),
                        ..
                    },
                    ligature_ast::Literal::Float(l),
                ) => (**v - *l).abs() < f64::EPSILON,
                (
                    Value {
                        kind: crate::value::ValueKind::Unit,
                        ..
                    },
                    ligature_ast::Literal::Unit,
                ) => true,
                _ => false,
            },
            ligature_ast::Pattern::Record { fields } => {
                if let Some(record_fields) = value.as_record() {
                    fields.iter().all(|field| {
                        if let Some(value_field) = record_fields.get(&field.name) {
                            self.match_pattern(value_field, &field.pattern)
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            }
            ligature_ast::Pattern::Union {
                variant,
                value: pattern_value,
            } => {
                if let Some((value_variant, value_payload)) = value.as_union() {
                    if value_variant == variant {
                        if let Some(pattern_val) = pattern_value {
                            if let Some(value_val) = value_payload {
                                self.match_pattern(value_val, pattern_val)
                            } else {
                                false
                            }
                        } else {
                            value_payload.is_none()
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            ligature_ast::Pattern::List { elements } => {
                if let Some(list_elements) = value.as_list() {
                    if elements.len() == list_elements.len() {
                        elements
                            .iter()
                            .zip(list_elements.iter())
                            .all(|(pattern, value)| self.match_pattern(value, pattern))
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    /// Get performance metrics
    pub async fn performance_metrics(&self) -> PerformanceMetrics {
        self.metrics.read().await.clone()
    }

    /// Get evaluator statistics
    pub fn stats(&self) -> std::collections::HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }

    /// Clear all caches
    pub fn clear_caches(&self) {
        if let Some(ref cache) = self.expression_cache {
            cache.clear();
        }
        if let Some(ref cache) = self.value_cache {
            cache.clear();
        }
    }
}

impl Clone for EnhancedAsyncEvaluator {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            expression_cache: self.expression_cache.clone(),
            value_cache: self.value_cache.clone(),
            type_environment: Arc::clone(&self.type_environment),
            type_checker: self.type_checker.clone(),
            metrics: Arc::clone(&self.metrics),
            stats: Arc::clone(&self.stats),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ligature_ast::{Expr, ExprKind, Literal, Span, Type};

    #[tokio::test]
    async fn test_enhanced_async_evaluator() {
        let config = EnhancedAsyncEvaluatorConfig::default();
        let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();

        let program = Program {
            declarations: vec![ligature_ast::Declaration::value(
                "x".to_string(),
                Some(Type::integer(Span::default())),
                Expr {
                    kind: ExprKind::Literal(Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            )],
            span: Span::default(),
        };

        let results = evaluator.evaluate_program(&program).await;
        assert!(results.is_ok());

        let metrics = evaluator.performance_metrics().await;
        assert!(metrics.total_evaluation_time > Duration::ZERO);
    }

    #[tokio::test]
    async fn test_expression_evaluation() {
        let config = EnhancedAsyncEvaluatorConfig::default();
        let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();

        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let env = EvaluationEnvironment::new();

        let result = evaluator.evaluate_expression(&expr, &env).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Value::integer(42, Span::default()));
    }
}
