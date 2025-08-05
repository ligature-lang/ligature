//! Integration tests for advanced performance optimizations.

use ligature_ast::{Expr, ExprKind, Literal, Span};
use ligature_eval::{
    advanced_optimizations::*,
    config::{AdvancedOptimizationConfig, MemoryManagementConfig, ParallelEvaluationConfig},
    Evaluator, EvaluatorConfig,
};
use ligature_parser::parse_expression;

#[test]
fn test_advanced_tail_call_detection() {
    let config = AdvancedOptimizationConfig {
        advanced_tail_call_detection: true,
        pattern_based_tco: true,
        context_sensitive_tco: true,
        nested_function_tco: true,
        ..Default::default()
    };

    let mut detector = AdvancedTailCallDetector::new(config);

    // Test simple tail call
    let source = "let factorial = \\n -> if n <= 1 then 1 else n * factorial (n - 1);";
    let expr = parse_expression(source).unwrap();

    let has_tail_calls = detector.detect_advanced_tail_calls(&expr);
    assert!(
        has_tail_calls,
        "Should detect tail calls in factorial function"
    );

    // Test nested function tail calls
    let source = "let outer = \\x -> let inner = \\y -> y + 1; inner x;";
    let expr = parse_expression(source).unwrap();

    let has_tail_calls = detector.detect_advanced_tail_calls(&expr);
    assert!(
        has_tail_calls,
        "Should detect tail calls in nested functions"
    );
}

#[test]
fn test_function_inlining() {
    let config = AdvancedOptimizationConfig {
        function_inlining: true,
        max_inline_size: 5,
        ..Default::default()
    };

    let mut inliner = FunctionInliner::new(config);

    // Test small function that should be inlined
    let small_function = Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: ligature_ast::BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Variable("x".to_string()),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(1)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let argument = Expr {
        kind: ExprKind::Literal(Literal::Integer(5)),
        span: Span::default(),
    };

    let should_inline = inliner.should_inline(&small_function, &argument);
    assert!(should_inline, "Small pure function should be inlined");

    // Test large function that should not be inlined
    let large_function = Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::Let {
                    name: "y".to_string(),
                    value: Box::new(Expr {
                        kind: ExprKind::BinaryOp {
                            operator: ligature_ast::BinaryOperator::Add,
                            left: Box::new(Expr {
                                kind: ExprKind::Variable("x".to_string()),
                                span: Span::default(),
                            }),
                            right: Box::new(Expr {
                                kind: ExprKind::Literal(Literal::Integer(1)),
                                span: Span::default(),
                            }),
                        },
                        span: Span::default(),
                    }),
                    body: Box::new(Expr {
                        kind: ExprKind::Let {
                            name: "z".to_string(),
                            value: Box::new(Expr {
                                kind: ExprKind::BinaryOp {
                                    operator: ligature_ast::BinaryOperator::Multiply,
                                    left: Box::new(Expr {
                                        kind: ExprKind::Variable("y".to_string()),
                                        span: Span::default(),
                                    }),
                                    right: Box::new(Expr {
                                        kind: ExprKind::Literal(Literal::Integer(2)),
                                        span: Span::default(),
                                    }),
                                },
                                span: Span::default(),
                            }),
                            body: Box::new(Expr {
                                kind: ExprKind::Variable("z".to_string()),
                                span: Span::default(),
                            }),
                        },
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let should_inline = inliner.should_inline(&large_function, &argument);
    assert!(!should_inline, "Large function should not be inlined");
}

#[test]
fn test_closure_capture_optimization() {
    let config = AdvancedOptimizationConfig {
        closure_optimization: true,
        minimal_capture: true,
        ..Default::default()
    };

    let mut optimizer = ClosureCaptureOptimizer::new(config);

    // Test closure with unused captures
    let closure_expr = Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: ligature_ast::BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Variable("x".to_string()),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(1)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let mut env = ligature_eval::environment::EvaluationEnvironment::new();
    env.bind(
        "unused_var".to_string(),
        ligature_eval::value::Value::integer(42, Span::default()),
    );
    env.bind(
        "used_var".to_string(),
        ligature_eval::value::Value::integer(10, Span::default()),
    );

    let analysis = optimizer.analyze_captures(&closure_expr, &env);

    // Should identify optimization opportunities
    assert!(
        !analysis.optimization_opportunities.is_empty(),
        "Should identify optimization opportunities"
    );
}

#[test]
fn test_parallel_evaluation() {
    let config = ParallelEvaluationConfig {
        enabled: true,
        worker_threads: 2,
        work_stealing: true,
        min_complexity: 5,
        adaptive_parallelism: true,
        thread_safe_values: true,
    };

    let mut evaluator = ParallelEvaluator::new(config);

    // Test simple expression (should not be parallelized)
    let simple_expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };

    let is_parallelizable = evaluator.is_parallelizable(&simple_expr);
    assert!(
        !is_parallelizable,
        "Simple expression should not be parallelized"
    );

    // Test complex expression (should be parallelized)
    let complex_expr = Expr {
        kind: ExprKind::Let {
            name: "x".to_string(),
            value: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: ligature_ast::BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(1)),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(2)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
            body: Box::new(Expr {
                kind: ExprKind::Let {
                    name: "y".to_string(),
                    value: Box::new(Expr {
                        kind: ExprKind::BinaryOp {
                            operator: ligature_ast::BinaryOperator::Multiply,
                            left: Box::new(Expr {
                                kind: ExprKind::Variable("x".to_string()),
                                span: Span::default(),
                            }),
                            right: Box::new(Expr {
                                kind: ExprKind::Literal(Literal::Integer(3)),
                                span: Span::default(),
                            }),
                        },
                        span: Span::default(),
                    }),
                    body: Box::new(Expr {
                        kind: ExprKind::Let {
                            name: "z".to_string(),
                            value: Box::new(Expr {
                                kind: ExprKind::BinaryOp {
                                    operator: ligature_ast::BinaryOperator::Add,
                                    left: Box::new(Expr {
                                        kind: ExprKind::Variable("y".to_string()),
                                        span: Span::default(),
                                    }),
                                    right: Box::new(Expr {
                                        kind: ExprKind::Literal(Literal::Integer(4)),
                                        span: Span::default(),
                                    }),
                                },
                                span: Span::default(),
                            }),
                            body: Box::new(Expr {
                                kind: ExprKind::Variable("z".to_string()),
                                span: Span::default(),
                            }),
                        },
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let is_parallelizable = evaluator.is_parallelizable(&complex_expr);
    assert!(
        is_parallelizable,
        "Complex expression should be parallelized"
    );
}

#[test]
fn test_generational_gc() {
    let config = MemoryManagementConfig {
        generational_gc: true,
        memory_compaction: true,
        object_pooling: true,
        young_gen_size: 1024 * 1024,    // 1MB
        old_gen_size: 10 * 1024 * 1024, // 10MB
        gc_frequency: 100,
        defragmentation: true,
        pre_allocation: true,
    };

    let mut gc = GenerationalGC::new(config);

    // Allocate some values
    for i in 0..100 {
        let value = ligature_eval::value::Value::integer(i, Span::default());
        gc.allocate(value);
    }

    let stats = gc.stats();
    assert!(
        stats.minor_collections > 0,
        "Should have performed minor collections"
    );
    assert!(stats.promotions > 0, "Should have promoted some objects");
}

#[test]
fn test_advanced_optimizations_integration() {
    // Test all optimizations working together
    let mut config = EvaluatorConfig::default();

    // Enable all advanced optimizations
    config.performance.advanced.advanced_tail_call_detection = true;
    config.performance.advanced.function_inlining = true;
    config.performance.advanced.closure_optimization = true;
    config.performance.parallel.enabled = true;
    config.performance.memory_management.generational_gc = true;

    let mut evaluator = Evaluator::with_config(config);

    // Test a complex expression that should benefit from multiple optimizations
    let source = r#"
        let factorial = \n -> 
            if n <= 1 then 1 
            else n * factorial (n - 1);
        
        let result = factorial 5;
        result
    "#;

    let expr = parse_expression(source).unwrap();
    let result = evaluator.evaluate_expression(&expr);

    assert!(
        result.is_ok(),
        "Should evaluate successfully with optimizations"
    );

    // Check that optimizations were applied
    let cache_stats = evaluator.cache_stats();
    assert!(
        cache_stats.tail_calls > 0,
        "Should have performed tail call optimizations"
    );

    let env_stats = evaluator.env_pool_stats();
    assert!(env_stats.0 > 0, "Should have used environment pooling");

    let value_stats = evaluator.value_pool_stats();
    assert!(value_stats.0 > 0, "Should have used value pooling");
}

#[test]
fn test_optimization_configuration() {
    // Test that configuration properly controls optimizations
    let mut config = EvaluatorConfig::default();

    // Disable all optimizations
    config.performance.advanced.advanced_tail_call_detection = false;
    config.performance.advanced.function_inlining = false;
    config.performance.advanced.closure_optimization = false;
    config.performance.parallel.enabled = false;
    config.performance.memory_management.generational_gc = false;

    let evaluator = Evaluator::with_config(config);

    // Verify that optimizations are disabled
    assert!(
        !evaluator
            .config
            .performance
            .advanced
            .advanced_tail_call_detection
    );
    assert!(!evaluator.config.performance.advanced.function_inlining);
    assert!(!evaluator.config.performance.advanced.closure_optimization);
    assert!(!evaluator.config.performance.parallel.enabled);
    assert!(
        !evaluator
            .config
            .performance
            .memory_management
            .generational_gc
    );
}

#[test]
fn test_performance_improvements() {
    // Test that optimizations provide performance improvements
    let mut config = EvaluatorConfig::default();

    // Enable optimizations
    config.performance.advanced.advanced_tail_call_detection = true;
    config.performance.advanced.function_inlining = true;
    config.performance.advanced.closure_optimization = true;
    config.performance.parallel.enabled = true;
    config.performance.memory_management.generational_gc = true;

    let mut evaluator = Evaluator::with_config(config);

    // Run a performance-intensive computation
    let source = r#"
        let fibonacci = \n ->
            if n <= 1 then n
            else fibonacci (n - 1) + fibonacci (n - 2);
        
        fibonacci 20
    "#;

    let expr = parse_expression(source).unwrap();
    let start = std::time::Instant::now();
    let result = evaluator.evaluate_expression(&expr);
    let duration = start.elapsed();

    assert!(result.is_ok(), "Should complete successfully");
    assert!(
        duration.as_millis() < 1000,
        "Should complete within reasonable time"
    );

    // Check optimization statistics
    let stats = evaluator.cache_stats();
    println!("Cache hit rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("Tail call optimizations: {}", stats.tail_calls);
    println!("Stack evaluations: {}", stats.stack_evals);
    println!("Environment pool reuses: {}", stats.env_pool_reuses);
}
