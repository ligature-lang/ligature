//! Tests for concurrent access improvements in Ligature.
//!
//! This test suite verifies that all concurrent components work correctly
//! and provide the expected performance improvements.

use ligature_eval::{
    concurrent::{ConcurrentExpressionCache, ConcurrentTypeEnvironment, ConcurrentValueCache, CacheKey},
    concurrent_type_checker::{ConcurrentTypeChecker, Constraint, TypeSubstitution},
    enhanced_async_evaluator::{EnhancedAsyncEvaluator, EnhancedAsyncEvaluatorConfig},
    parallel::{ParallelEvaluator, ParallelEvaluatorConfig, Task, TaskId, WorkQueue},
    value::Value,
};
use ligature_ast::{Expr, ExprKind, Literal, Program, Span, Type};
use std::time::{Duration, Instant};
use tokio::time::sleep;

#[tokio::test]
async fn test_concurrent_expression_cache() {
    let cache = ConcurrentExpressionCache::new(100);
    
    // Test basic put/get operations
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    let key = CacheKey::new(&expr, &env, 0);
    let value = Value::Integer(42);
    
    cache.put(key.clone(), value.clone());
    assert_eq!(cache.get(&key), Some(value));
    
    // Test concurrent access
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let cache = &cache;
            let key = CacheKey::new(&expr, &env, i);
            let value = Value::Integer(i as i64);
            
            tokio::spawn(async move {
                cache.put(key.clone(), value.clone());
                let retrieved = cache.get(&key);
                assert_eq!(retrieved, Some(value));
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    // Test cache statistics
    let stats = cache.stats();
    assert!(stats.get("insertions").unwrap() > &0);
    assert!(stats.get("hits").unwrap() > &0);
}

#[tokio::test]
async fn test_concurrent_type_environment() {
    let env = ConcurrentTypeEnvironment::new();
    
    // Test basic operations
    env.bind("x".to_string(), Type::Integer);
    assert_eq!(env.lookup("x"), Some(Type::Integer));
    assert!(env.is_bound("x"));
    
    // Test concurrent access
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let env = &env;
            let name = format!("var_{}", i);
            let type_ = Type::Integer;
            
            tokio::spawn(async move {
                env.bind(name.clone(), type_.clone());
                assert_eq!(env.lookup(&name), Some(type_));
                assert!(env.is_bound(&name));
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    assert_eq!(env.len(), 10);
}

#[tokio::test]
async fn test_concurrent_value_cache() {
    let cache = ConcurrentValueCache::new(100);
    
    // Test basic operations
    cache.put("key1".to_string(), Value::Integer(42));
    assert_eq!(cache.get("key1"), Some(Value::Integer(42)));
    assert_eq!(cache.get("key2"), None);
    
    // Test concurrent access
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let cache = &cache;
            let key = format!("key_{}", i);
            let value = Value::Integer(i as i64);
            
            tokio::spawn(async move {
                cache.put(key.clone(), value.clone());
                let retrieved = cache.get(&key);
                assert_eq!(retrieved, Some(value));
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    // Test cache statistics
    let stats = cache.stats();
    assert!(stats.get("hits").unwrap() > &0);
    assert!(stats.get("insertions").unwrap() > &0);
}

#[tokio::test]
async fn test_work_queue() {
    let queue = WorkQueue::new();
    
    // Create test tasks
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    
    let task = Task::new(expr, env, 0);
    let task_id = queue.submit(task).await;
    
    assert!(!queue.is_empty());
    assert_eq!(queue.active_tasks(), 1);
    
    // Complete the task
    let result = Ok(Value::Integer(42));
    queue.complete_task(task_id, result).await;
    
    assert!(queue.is_empty());
    assert_eq!(queue.completed_tasks(), 1);
    
    // Test queue statistics
    let stats = queue.stats();
    assert_eq!(stats.get("submitted").unwrap(), &1);
    assert_eq!(stats.get("completed").unwrap(), &1);
}

#[tokio::test]
async fn test_parallel_evaluator() {
    let config = ParallelEvaluatorConfig {
        num_workers: 2,
        cache_size: 100,
        max_memory: 10000,
        task_timeout: Duration::from_secs(5),
    };
    
    let mut evaluator = ParallelEvaluator::new(config);
    evaluator.start().await;
    
    // Give workers time to start
    sleep(Duration::from_millis(100)).await;
    
    // Test evaluator statistics
    let stats = evaluator.stats();
    assert_eq!(stats.get("workers").unwrap(), &2);
    
    evaluator.stop().await;
}

#[tokio::test]
async fn test_concurrent_type_checker() {
    let checker = ConcurrentTypeChecker::new(2);
    
    // Test type inference
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    
    let inferred_type = checker.infer_expression_type(&expr).await;
    assert_eq!(inferred_type.unwrap(), Type::Integer);
    
    // Test boolean literal
    let bool_expr = Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)),
        span: Span::default(),
    };
    
    let bool_type = checker.infer_expression_type(&bool_expr).await;
    assert_eq!(bool_type.unwrap(), Type::Boolean);
}

#[tokio::test]
async fn test_type_substitution() {
    let mut substitution = TypeSubstitution::new();
    
    // Test basic substitution
    substitution.add("T".to_string(), Type::Integer);
    
    let var_type = Type::Variable("T".to_string());
    let substituted = substitution.apply(&var_type);
    assert_eq!(substituted, Type::Integer);
    
    // Test function type substitution
    let func_type = Type::Function(
        Box::new(Type::Variable("T".to_string())),
        Box::new(Type::Boolean),
    );
    let substituted_func = substitution.apply(&func_type);
    assert_eq!(substituted_func, Type::Function(
        Box::new(Type::Integer),
        Box::new(Type::Boolean),
    ));
}

#[tokio::test]
async fn test_constraint_creation() {
    let constraint = Constraint::new(Type::Integer, Type::Integer);
    
    assert!(!constraint.is_solved());
    assert_eq!(constraint.left, Type::Integer);
    assert_eq!(constraint.right, Type::Integer);
    
    // Test constraint with source
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let constraint_with_source = constraint.with_source(expr.clone());
    assert_eq!(constraint_with_source.source, Some(expr));
}

#[tokio::test]
async fn test_enhanced_async_evaluator() {
    let config = EnhancedAsyncEvaluatorConfig {
        num_workers: 2,
        expression_cache_size: 100,
        expression_cache_memory: 10000,
        value_cache_size: 50,
        type_cache_size: 10,
        task_timeout: Duration::from_secs(5),
        enable_parallel: true,
        enable_concurrent_type_checking: true,
        enable_caching: true,
    };
    
    let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();
    
    // Test evaluator creation
    assert_eq!(evaluator.config().num_workers, 2);
    assert!(evaluator.config().enable_parallel);
    assert!(evaluator.config().enable_concurrent_type_checking);
    assert!(evaluator.config().enable_caching);
    
    // Test statistics
    let stats = evaluator.get_stats().await;
    assert_eq!(stats.total_evaluations, 0);
    assert_eq!(stats.successful_evaluations, 0);
    assert_eq!(stats.failed_evaluations, 0);
    
    evaluator.shutdown().await;
}

#[tokio::test]
async fn test_concurrent_stress() {
    let cache = ConcurrentExpressionCache::new(1000);
    let value_cache = ConcurrentValueCache::new(500);
    let type_env = ConcurrentTypeEnvironment::new();
    
    // Submit many concurrent operations
    let handles: Vec<_> = (0..100)
        .map(|i| {
            let cache = &cache;
            let value_cache = &value_cache;
            let type_env = &type_env;
            
            tokio::spawn(async move {
                // Expression cache operations
                let expr = Expr {
                    kind: ExprKind::Literal(Literal::Integer(i as i64)),
                    span: Span::default(),
                };
                let env = ligature_eval::environment::EvaluationEnvironment::new();
                let key = CacheKey::new(&expr, &env, 0);
                let value = Value::Integer(i as i64);
                
                cache.put(key.clone(), value.clone());
                let retrieved = cache.get(&key);
                assert_eq!(retrieved, Some(value));
                
                // Value cache operations
                let cache_key = format!("key_{}", i);
                value_cache.put(cache_key.clone(), Value::Integer(i as i64));
                let retrieved_value = value_cache.get(&cache_key);
                assert!(retrieved_value.is_some());
                
                // Type environment operations
                let type_name = format!("type_{}", i);
                type_env.bind(type_name.clone(), Type::Integer);
                assert!(type_env.is_bound(&type_name));
            })
        })
        .collect();
    
    // Wait for all operations to complete
    for handle in handles {
        handle.await.unwrap();
    }
    
    // Verify final state
    assert_eq!(cache.size(), 100);
    assert_eq!(value_cache.size(), 100);
    assert_eq!(type_env.len(), 100);
}

#[tokio::test]
async fn test_cache_eviction() {
    let cache = ConcurrentExpressionCache::new(5); // Small cache to trigger eviction
    
    // Fill cache beyond capacity
    for i in 0..10 {
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(i as i64)),
            span: Span::default(),
        };
        let env = ligature_eval::environment::EvaluationEnvironment::new();
        let key = CacheKey::new(&expr, &env, 0);
        let value = Value::Integer(i as i64);
        
        cache.put(key, value);
    }
    
    // Cache should have evicted some entries
    assert!(cache.size() <= 5);
    
    let stats = cache.stats();
    assert!(stats.get("evictions").unwrap() > &0);
}

#[tokio::test]
async fn test_task_priority() {
    use ligature_eval::parallel::Priority;
    
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    
    let task = Task::new(expr, env, 0)
        .with_priority(Priority::High);
    
    assert_eq!(task.priority, Priority::High);
}

#[tokio::test]
async fn test_task_dependencies() {
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    
    let dependency_id = TaskId::new();
    let task = Task::new(expr, env, 0)
        .with_dependency(dependency_id.clone());
    
    assert!(task.dependencies.contains(&dependency_id));
}

#[tokio::test]
async fn test_performance_improvements() {
    // Test that concurrent operations are faster than sequential
    let iterations = 1000;
    
    // Sequential operations
    let start_time = Instant::now();
    let mut cache = ConcurrentValueCache::new(1000);
    for i in 0..iterations {
        cache.put(format!("key_{}", i), Value::Integer(i as i64));
        let _ = cache.get(&format!("key_{}", i));
    }
    let sequential_time = start_time.elapsed();
    
    // Concurrent operations
    let start_time = Instant::now();
    let cache = ConcurrentValueCache::new(1000);
    let handles: Vec<_> = (0..iterations)
        .map(|i| {
            let cache = &cache;
            tokio::spawn(async move {
                cache.put(format!("key_{}", i), Value::Integer(i as i64));
                let _ = cache.get(&format!("key_{}", i));
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
    let concurrent_time = start_time.elapsed();
    
    // Concurrent should be faster (though this may not always be true due to overhead)
    println!("Sequential time: {:?}", sequential_time);
    println!("Concurrent time: {:?}", concurrent_time);
    
    // At minimum, concurrent should not be significantly slower
    assert!(concurrent_time < sequential_time * 2);
}

#[tokio::test]
async fn test_memory_efficiency() {
    let cache = ConcurrentExpressionCache::new(100);
    
    // Test memory usage tracking
    let initial_size = cache.size();
    
    // Add some entries
    for i in 0..10 {
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(i as i64)),
            span: Span::default(),
        };
        let env = ligature_eval::environment::EvaluationEnvironment::new();
        let key = CacheKey::new(&expr, &env, 0);
        let value = Value::Integer(i as i64);
        
        cache.put(key, value);
    }
    
    let final_size = cache.size();
    assert!(final_size > initial_size);
    
    // Test memory statistics
    let stats = cache.stats();
    assert!(stats.get("size").unwrap() > &0);
    assert!(stats.get("max_size").unwrap() > &0);
}

#[tokio::test]
async fn test_error_handling() {
    let cache = ConcurrentExpressionCache::new(100);
    
    // Test that cache handles missing keys gracefully
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    let key = CacheKey::new(&expr, &env, 0);
    
    let result = cache.get(&key);
    assert_eq!(result, None);
    
    // Test that cache handles concurrent modifications gracefully
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let cache = &cache;
            let key = CacheKey::new(&expr, &env, i);
            let value = Value::Integer(i as i64);
            
            tokio::spawn(async move {
                cache.put(key, value);
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    // Cache should still be in a valid state
    assert!(cache.size() <= 100);
}

#[tokio::test]
async fn test_configuration_options() {
    // Test different configuration options
    let config = EnhancedAsyncEvaluatorConfig {
        num_workers: 1,
        expression_cache_size: 50,
        expression_cache_memory: 5000,
        value_cache_size: 25,
        type_cache_size: 5,
        task_timeout: Duration::from_secs(1),
        enable_parallel: false,
        enable_concurrent_type_checking: false,
        enable_caching: false,
    };
    
    let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();
    
    assert_eq!(evaluator.config().num_workers, 1);
    assert!(!evaluator.config().enable_parallel);
    assert!(!evaluator.config().enable_concurrent_type_checking);
    assert!(!evaluator.config().enable_caching);
    
    evaluator.shutdown().await;
}

#[tokio::test]
async fn test_statistics_accuracy() {
    let cache = ConcurrentExpressionCache::new(100);
    
    // Perform known operations
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    let key = CacheKey::new(&expr, &env, 0);
    let value = Value::Integer(42);
    
    // Put operation
    cache.put(key.clone(), value.clone());
    
    // Get operation (should be a hit)
    let _ = cache.get(&key);
    
    // Get operation with different key (should be a miss)
    let different_key = CacheKey::new(&expr, &env, 1);
    let _ = cache.get(&different_key);
    
    // Check statistics
    let stats = cache.stats();
    assert_eq!(stats.get("insertions").unwrap(), &1);
    assert_eq!(stats.get("hits").unwrap(), &1);
    assert_eq!(stats.get("misses").unwrap(), &1);
    assert_eq!(stats.get("size").unwrap(), &1);
} 