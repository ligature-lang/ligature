//! Comprehensive performance benchmark for Ligature optimizations.
//! Tests the three key performance improvements:
//! 1. Function Call Bottleneck: Function calls are ~600x slower than arithmetic operations
//! 2. Complete Expression Caching: Framework is in place but needs implementation
//! 3. Value Representation Optimization: Reduce cloning overhead with Arc<Value> and value interning

use ligature_ast::{AstResult, BinaryOperator, Expr, ExprKind, Literal, Span};
use ligature_eval::Evaluator;
use std::time::Instant;

fn main() -> AstResult<()> {
    println!("Ligature Performance Optimization Benchmark");
    println!("==========================================");
    println!("Testing the three key performance improvements:");
    println!("1. Function Call Performance Optimization");
    println!("2. Complete Expression Caching");
    println!("3. Value Representation Optimization");
    println!();

    // Test 1: Function Call Performance
    benchmark_function_call_performance()?;

    // Test 2: Arithmetic Operations Performance (baseline)
    benchmark_arithmetic_performance()?;

    // Test 3: Expression Caching Performance
    benchmark_expression_caching()?;

    // Test 4: Value Representation Performance
    benchmark_value_representation()?;

    // Test 5: Memory Usage and Optimization Impact
    benchmark_memory_optimization()?;

    Ok(())
}

fn benchmark_function_call_performance() -> AstResult<()> {
    println!("1. Function Call Performance Benchmark");
    println!("-------------------------------------");

    // Create a simple function: \x -> x + 1
    let function = create_simple_function();

    // Create function application: (\x -> x + 1) 5
    let application = Expr {
        kind: ExprKind::Application {
            function: Box::new(function),
            argument: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    // Benchmark with optimizations enabled
    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    evaluator.set_caching(true);
    evaluator.set_value_optimization(true);

    let iterations = 100_000;
    let start = Instant::now();

    for _ in 0..iterations {
        let _result = evaluator.evaluate_expression(&application)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    let stats = evaluator.cache_stats();

    println!("Function calls per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!("Stack evaluations: {}", stats.stack_evals);
    println!("Tail calls: {}", stats.tail_calls);
    println!("Cache hit rate: {:.2}%", stats.hit_rate());
    println!("Environment pool reuses: {}", stats.env_pool_reuses);
    println!("Value pool acquisitions: {}", stats.value_pool_acquisitions);

    Ok(())
}

fn benchmark_arithmetic_performance() -> AstResult<()> {
    println!("\n2. Arithmetic Operations Performance Benchmark");
    println!("---------------------------------------------");

    // Create a complex arithmetic expression: (1 + 2) * 3 - 4
    let arithmetic_expr = create_complex_arithmetic_expression();

    let mut evaluator = Evaluator::new();
    evaluator.set_caching(true);
    evaluator.set_value_optimization(true);

    let iterations = 1_000_000;
    let start = Instant::now();

    for _ in 0..iterations {
        let _result = evaluator.evaluate_expression(&arithmetic_expr)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    let stats = evaluator.cache_stats();

    println!("Arithmetic operations per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!("Cache hit rate: {:.2}%", stats.hit_rate());
    println!(
        "Value pool utilization: {:.2}%",
        stats.value_pool_utilization()
    );

    Ok(())
}

fn benchmark_expression_caching() -> AstResult<()> {
    println!("\n3. Expression Caching Performance Benchmark");
    println!("-------------------------------------------");

    // Create a moderately complex expression
    let expression = create_complex_expression();

    let mut evaluator = Evaluator::new();
    evaluator.set_caching(true);
    evaluator.set_value_optimization(true);

    // First pass: populate cache
    let warmup_iterations = 10_000;
    let start = Instant::now();

    for _ in 0..warmup_iterations {
        let _result = evaluator.evaluate_expression(&expression)?;
    }

    let warmup_duration = start.elapsed();

    // Second pass: test cache performance
    let cache_iterations = 100_000;
    let start = Instant::now();

    for _ in 0..cache_iterations {
        let _result = evaluator.evaluate_expression(&expression)?;
    }

    let cache_duration = start.elapsed();

    let stats = evaluator.cache_stats();

    println!("Warmup time: {warmup_duration:?}");
    println!("Cached evaluation time: {cache_duration:?}");
    println!("Cache hits: {}", stats.hits);
    println!("Cache misses: {}", stats.misses);
    println!("Cache hit rate: {:.2}%", stats.hit_rate());
    println!("Cache evictions: {}", stats.evictions);
    println!(
        "Speedup: {:.2}x",
        warmup_duration.as_secs_f64() / cache_duration.as_secs_f64()
    );

    Ok(())
}

fn benchmark_value_representation() -> AstResult<()> {
    println!("\n4. Value Representation Performance Benchmark");
    println!("---------------------------------------------");

    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    let iterations = 1_000_000;

    // Test integer values
    let start = Instant::now();
    for i in 0..iterations {
        let value = ligature_eval::Value::integer(i, Span::default());
        let _cloned = value.clone();
    }
    let int_duration = start.elapsed();

    // Test string values
    let start = Instant::now();
    for i in 0..iterations {
        let value = ligature_eval::Value::string(format!("string_{i}"), Span::default());
        let _cloned = value.clone();
    }
    let string_duration = start.elapsed();

    // Test record values
    let start = Instant::now();
    for i in 0..iterations {
        let mut fields = std::collections::HashMap::new();
        fields.insert(
            "x".to_string(),
            ligature_eval::Value::integer(i, Span::default()),
        );
        fields.insert(
            "y".to_string(),
            ligature_eval::Value::string(format!("value_{i}"), Span::default()),
        );
        let value = ligature_eval::Value::record(fields, Span::default());
        let _cloned = value.clone();
    }
    let record_duration = start.elapsed();

    println!(
        "Integer operations per second: {:.0}",
        iterations as f64 / int_duration.as_secs_f64()
    );
    println!(
        "String operations per second: {:.0}",
        iterations as f64 / string_duration.as_secs_f64()
    );
    println!(
        "Record operations per second: {:.0}",
        iterations as f64 / record_duration.as_secs_f64()
    );

    let (available, total) = evaluator.value_pool_stats();
    println!(
        "Value pool utilization: {}/{} ({:.1}%)",
        available,
        total,
        (available as f64 / total as f64) * 100.0
    );

    let interner_stats = evaluator.value_interner_stats();
    println!("Value interner stats:");
    println!("  Strings: {}", interner_stats.string_count);
    println!("  Integers: {}", interner_stats.integer_count);
    println!("  Floats: {}", interner_stats.float_count);
    println!("  Booleans: {}", interner_stats.boolean_count);

    Ok(())
}

fn benchmark_memory_optimization() -> AstResult<()> {
    println!("\n5. Memory Usage and Optimization Impact");
    println!("------------------------------------");

    let mut evaluator = Evaluator::new();
    evaluator.set_caching(true);
    evaluator.set_value_optimization(true);

    // Create a large number of expressions and values
    let iterations = 100_000;
    let mut expressions = Vec::new();

    let start = Instant::now();

    for i in 0..iterations {
        let expr = create_nested_expression(i % 10); // Limit depth to avoid stack overflow
        expressions.push(expr);

        if i % 10_000 == 0 {
            // Evaluate some expressions to test memory management
            for j in 0..100 {
                if j < expressions.len() {
                    let _result = evaluator.evaluate_expression(&expressions[j]);
                }
            }
        }
    }

    let duration = start.elapsed();

    let stats = evaluator.cache_stats();
    let (env_available, env_total) = evaluator.env_pool_stats();
    let (value_available, value_total) = evaluator.value_pool_stats();

    println!("Created {iterations} expressions in {duration:?}");
    println!("Cache size: {}", evaluator.cache_size());
    println!(
        "Cache memory usage: {} bytes",
        evaluator.cache_memory_usage()
    );
    println!(
        "Environment pool: {}/{} ({:.1}%)",
        env_available,
        env_total,
        (env_available as f64 / env_total as f64) * 100.0
    );
    println!(
        "Value pool: {}/{} ({:.1}%)",
        value_available,
        value_total,
        (value_available as f64 / value_total as f64) * 100.0
    );
    println!("Cache evictions: {}", stats.evictions);
    println!("Environment pool reuses: {}", stats.env_pool_reuses);
    println!("Value pool acquisitions: {}", stats.value_pool_acquisitions);
    println!("Value pool releases: {}", stats.value_pool_releases);

    Ok(())
}

// Helper functions

fn create_simple_function() -> Expr {
    Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Add,
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
    }
}

fn create_complex_arithmetic_expression() -> Expr {
    Expr {
        kind: ExprKind::BinaryOp {
            operator: BinaryOperator::Subtract,
            left: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Multiply,
                    left: Box::new(Expr {
                        kind: ExprKind::BinaryOp {
                            operator: BinaryOperator::Add,
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
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(3)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(4)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    }
}

fn create_complex_expression() -> Expr {
    // Create a complex expression with multiple operations
    Expr {
        kind: ExprKind::Let {
            name: "x".to_string(),
            value: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(10)),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(20)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Multiply,
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
        },
        span: Span::default(),
    }
}

fn create_nested_expression(depth: usize) -> Expr {
    if depth == 0 {
        Expr {
            kind: ExprKind::Literal(Literal::Integer(1)),
            span: Span::default(),
        }
    } else {
        Expr {
            kind: ExprKind::BinaryOp {
                operator: BinaryOperator::Add,
                left: Box::new(create_nested_expression(depth - 1)),
                right: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(depth as i64)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        }
    }
}
