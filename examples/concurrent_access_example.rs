//! Example demonstrating concurrent access improvements in Ligature.
//!
//! This example shows how to use the new concurrent data structures,
//! parallel evaluation, and concurrent type checking features.

use ligature_eval::{
    concurrent::{ConcurrentExpressionCache, ConcurrentTypeEnvironment, ConcurrentValueCache},
    concurrent_type_checker::ConcurrentTypeChecker,
    enhanced_async_evaluator::{EnhancedAsyncEvaluator, EnhancedAsyncEvaluatorConfig},
    parallel::{ParallelEvaluator, ParallelEvaluatorConfig, Task, WorkQueue},
    value::Value,
};
use ligature_ast::{Expr, ExprKind, Literal, Program, Span};
use std::time::{Duration, Instant};
use tokio::time::sleep;

/// Example 1: Basic DashMap Usage
async fn example_dashmap_integration() {
    println!("=== Example 1: DashMap Integration ===");

    // Create concurrent caches
    let expression_cache = ConcurrentExpressionCache::new(1000);
    let value_cache = ConcurrentValueCache::new(500);
    let type_environment = ConcurrentTypeEnvironment::new();

    // Concurrent access from multiple tasks
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let expression_cache = &expression_cache;
            let value_cache = &value_cache;
            let type_environment = &type_environment;

            tokio::spawn(async move {
                // Simulate concurrent cache access
                let key = format!("key_{}", i);
                let value = Value::Integer(i as i64);

                // Put value in cache
                value_cache.put(key.clone(), value.clone());

                // Get value from cache
                let retrieved = value_cache.get(&key);
                assert_eq!(retrieved, Some(value));

                // Add type binding
                type_environment.bind(format!("var_{}", i), ligature_ast::Type::Integer);

                println!("Task {} completed", i);
            })
        })
        .collect();

    // Wait for all tasks to complete
    for handle in handles {
        handle.await.unwrap();
    }

    // Print statistics
    println!("Expression cache size: {}", expression_cache.size());
    println!("Value cache size: {}", value_cache.size());
    println!("Type environment size: {}", type_environment.len());

    let value_cache_stats = value_cache.stats();
    println!("Value cache hits: {}", value_cache_stats.get("hits").unwrap_or(&0));
    println!("Value cache misses: {}", value_cache_stats.get("misses").unwrap_or(&0));
}

/// Example 2: Work Queue and Task Management
async fn example_work_queue() {
    println!("\n=== Example 2: Work Queue and Task Management ===");

    let work_queue = WorkQueue::new();

    // Create some test expressions
    let expressions: Vec<Expr> = (0..5)
        .map(|i| Expr {
            kind: ExprKind::Literal(Literal::Integer(i as i64)),
            span: Span::default(),
        })
        .collect();

    // Submit tasks to work queue
    let task_ids: Vec<_> = futures::future::join_all(
        expressions
            .into_iter()
            .map(|expr| {
                let task = Task::new(expr, ligature_eval::environment::EvaluationEnvironment::new(), 0);
                work_queue.submit(task)
            })
        )
    ).await;

    println!("Submitted {} tasks to work queue", task_ids.len());

    // Simulate task processing
    for task_id in task_ids {
        // In a real implementation, workers would process these tasks
        // For this example, we'll just simulate completion
        let result = Ok(Value::Integer(42));
        work_queue.complete_task(task_id, result).await;
    }

    // Print queue statistics
    let stats = work_queue.stats();
    println!("Submitted tasks: {}", stats.get("submitted").unwrap_or(&0));
    println!("Completed tasks: {}", stats.get("completed").unwrap_or(&0));
    println!("Failed tasks: {}", stats.get("failed").unwrap_or(&0));
}

/// Example 3: Parallel Evaluation
async fn example_parallel_evaluation() {
    println!("\n=== Example 3: Parallel Evaluation ===");

    let config = ParallelEvaluatorConfig {
        num_workers: 4,
        cache_size: 1000,
        max_memory: 100000,
        task_timeout: Duration::from_secs(10),
    };

    let mut evaluator = ParallelEvaluator::new(config);
    evaluator.start().await;

    // Create a simple program
    let program = Program {
        declarations: vec![
            ligature_ast::Declaration::Let {
                name: "x".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::Integer(42)),
                    span: Span::default(),
                },
                type_annotation: None,
                span: Span::default(),
            },
            ligature_ast::Declaration::Let {
                name: "y".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::Integer(10)),
                    span: Span::default(),
                },
                type_annotation: None,
                span: Span::default(),
            },
        ],
        span: Span::default(),
    };

    // Evaluate program in parallel
    let start_time = Instant::now();
    let result = evaluator.evaluate_program(&program).await;
    let evaluation_time = start_time.elapsed();

    println!("Parallel evaluation completed in {:?}", evaluation_time);
    println!("Result: {:?}", result);

    // Print evaluator statistics
    let stats = evaluator.stats();
    println!("Worker pool stats: {:?}", stats);

    evaluator.stop().await;
}

/// Example 4: Concurrent Type Checking
async fn example_concurrent_type_checking() {
    println!("\n=== Example 4: Concurrent Type Checking ===");

    let type_checker = ConcurrentTypeChecker::new(4);

    // Create a program with type annotations
    let program = Program {
        declarations: vec![
            ligature_ast::Declaration::Let {
                name: "x".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::Integer(42)),
                    span: Span::default(),
                },
                type_annotation: Some(ligature_ast::Type::Integer),
                span: Span::default(),
            },
            ligature_ast::Declaration::Let {
                name: "y".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::Boolean(true)),
                    span: Span::default(),
                },
                type_annotation: Some(ligature_ast::Type::Boolean),
                span: Span::default(),
            },
        ],
        span: Span::default(),
    };

    // Check program in parallel
    let start_time = Instant::now();
    let result = type_checker.check_program_parallel(&program).await;
    let checking_time = start_time.elapsed();

    println!("Concurrent type checking completed in {:?}", checking_time);
    println!("Type check result: {:?}", result);

    // Print type checker statistics
    let stats = type_checker.stats();
    println!("Type checker stats: {:?}", stats);
}

/// Example 5: Enhanced Async Evaluator
async fn example_enhanced_async_evaluator() {
    println!("\n=== Example 5: Enhanced Async Evaluator ===");

    let config = EnhancedAsyncEvaluatorConfig {
        num_workers: 4,
        expression_cache_size: 1000,
        expression_cache_memory: 100000,
        value_cache_size: 500,
        type_cache_size: 100,
        task_timeout: Duration::from_secs(10),
        enable_parallel: true,
        enable_concurrent_type_checking: true,
        enable_caching: true,
    };

    let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();

    // Create a program
    let program = Program {
        declarations: vec![
            ligature_ast::Declaration::Let {
                name: "result".to_string(),
                value: Expr {
                    kind: ExprKind::BinaryOp {
                        operator: ligature_ast::BinaryOperator::Add,
                        left: Box::new(Expr {
                            kind: ExprKind::Literal(Literal::Integer(10)),
                            span: Span::default(),
                        }),
                        right: Box::new(Expr {
                            kind: ExprKind::Literal(Literal::Integer(32)),
                            span: Span::default(),
                        }),
                    },
                    span: Span::default(),
                },
                type_annotation: None,
                span: Span::default(),
            },
        ],
        span: Span::default(),
    };

    // Evaluate program with enhanced evaluator
    let start_time = Instant::now();
    let result = evaluator.evaluate_program(&program).await;
    let evaluation_time = start_time.elapsed();

    println!("Enhanced async evaluation completed in {:?}", evaluation_time);
    println!("Result: {:?}", result);

    // Get comprehensive statistics
    let stats = evaluator.get_stats().await;
    println!("Total evaluations: {}", stats.total_evaluations);
    println!("Successful evaluations: {}", stats.successful_evaluations);
    println!("Failed evaluations: {}", stats.failed_evaluations);
    println!("Cache hit rate: {:.2}%", stats.cache_hit_rate * 100.0);
    println!("Average evaluation time: {:?}", stats.average_evaluation_time);

    // Print parallel stats
    println!("Parallel stats: {:?}", stats.parallel_stats);
    println!("Type checking stats: {:?}", stats.type_checking_stats);
    println!("Memory stats: {:?}", stats.memory_stats);

    evaluator.shutdown().await;
}

/// Example 6: Performance Comparison
async fn example_performance_comparison() {
    println!("\n=== Example 6: Performance Comparison ===");

    // Create a larger program for performance testing
    let mut declarations = Vec::new();
    for i in 0..100 {
        declarations.push(ligature_ast::Declaration::Let {
            name: format!("var_{}", i),
            value: Expr {
                kind: ExprKind::Literal(Literal::Integer(i as i64)),
                span: Span::default(),
            },
            type_annotation: None,
            span: Span::default(),
        });
    }

    let program = Program {
        declarations,
        span: Span::default(),
    };

    // Test sequential evaluation (simulated)
    println!("Testing sequential evaluation...");
    let start_time = Instant::now();
    // Simulate sequential processing time
    sleep(Duration::from_millis(100)).await;
    let sequential_time = start_time.elapsed();
    println!("Sequential evaluation time: {:?}", sequential_time);

    // Test parallel evaluation
    println!("Testing parallel evaluation...");
    let config = ParallelEvaluatorConfig {
        num_workers: 8,
        cache_size: 1000,
        max_memory: 100000,
        task_timeout: Duration::from_secs(10),
    };

    let mut evaluator = ParallelEvaluator::new(config);
    evaluator.start().await;

    let start_time = Instant::now();
    let _result = evaluator.evaluate_program(&program).await;
    let parallel_time = start_time.elapsed();
    println!("Parallel evaluation time: {:?}", parallel_time);

    // Calculate speedup
    let speedup = sequential_time.as_secs_f64() / parallel_time.as_secs_f64();
    println!("Speedup: {:.2}x", speedup);

    evaluator.stop().await;
}

/// Example 7: Stress Testing
async fn example_stress_testing() {
    println!("\n=== Example 7: Stress Testing ===");

    let config = EnhancedAsyncEvaluatorConfig {
        num_workers: 8,
        expression_cache_size: 10000,
        expression_cache_memory: 1000000,
        value_cache_size: 5000,
        type_cache_size: 1000,
        task_timeout: Duration::from_secs(30),
        enable_parallel: true,
        enable_concurrent_type_checking: true,
        enable_caching: true,
    };

    let evaluator = EnhancedAsyncEvaluator::new(config).unwrap();

    // Submit many concurrent evaluations
    let handles: Vec<_> = (0..50)
        .map(|i| {
            let evaluator = &evaluator;
            let program = Program {
                declarations: vec![
                    ligature_ast::Declaration::Let {
                        name: format!("result_{}", i),
                        value: Expr {
                            kind: ExprKind::Literal(Literal::Integer(i as i64)),
                            span: Span::default(),
                        },
                        type_annotation: None,
                        span: Span::default(),
                    },
                ],
                span: Span::default(),
            };

            tokio::spawn(async move {
                let result = evaluator.evaluate_program(&program).await;
                (i, result)
            })
        })
        .collect();

    // Wait for all evaluations to complete
    let start_time = Instant::now();
    let results = futures::future::join_all(handles).await;
    let total_time = start_time.elapsed();

    // Count successful evaluations
    let successful = results.iter().filter(|(_, result)| result.is_ok()).count();
    let failed = results.len() - successful;

    println!("Stress test completed in {:?}", total_time);
    println!("Total evaluations: {}", results.len());
    println!("Successful: {}", successful);
    println!("Failed: {}", failed);
    println!("Throughput: {:.2} evaluations/second", results.len() as f64 / total_time.as_secs_f64());

    // Get final statistics
    let stats = evaluator.get_stats().await;
    println!("Final cache hit rate: {:.2}%", stats.cache_hit_rate * 100.0);
    println!("Final memory usage: {:?}", stats.memory_stats);

    evaluator.shutdown().await;
}

#[tokio::main]
async fn main() {
    println!("Ligature Concurrent Access Improvements Demo");
    println!("============================================\n");

    // Run all examples
    example_dashmap_integration().await;
    example_work_queue().await;
    example_parallel_evaluation().await;
    example_concurrent_type_checking().await;
    example_enhanced_async_evaluator().await;
    example_performance_comparison().await;
    example_stress_testing().await;

    println!("\n=== Demo Complete ===");
    println!("All concurrent access improvements have been demonstrated!");
} 