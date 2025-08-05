//! Benchmark example demonstrating the performance improvements
//! of the new function call architecture.

use ligature_ast::{AstResult, BinaryOperator, Expr, ExprKind, Literal, Span};
use ligature_eval::Evaluator;
use std::time::Instant;

fn main() -> AstResult<()> {
    println!("Function Call Architecture Benchmark");
    println!("===================================");

    // Test 1: Basic Function Application Performance
    benchmark_basic_function_application()?;

    // Test 2: Environment Pooling Performance
    benchmark_environment_pooling()?;

    // Test 3: Cache Performance
    benchmark_cache_performance()?;

    Ok(())
}

fn benchmark_basic_function_application() -> AstResult<()> {
    println!("\n1. Basic Function Application Benchmark");
    println!("--------------------------------------");

    // Create a simple function: \x -> x + 1
    let function = Expr {
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
    };

    // Apply the function to 5
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
    let start = Instant::now();
    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    let result = evaluator.evaluate_expression(&application)?;
    let duration = start.elapsed();

    let stats = evaluator.cache_stats();

    println!("Result: {result:?}");
    println!("Time: {duration:?}");
    println!("Stack Evaluations: {}", stats.stack_evals);
    println!("Tail Calls: {}", stats.tail_calls);
    println!(
        "Cache Stats - Hits: {}, Misses: {}, Hit Rate: {:.2}%",
        stats.hits,
        stats.misses,
        stats.hit_rate()
    );

    Ok(())
}

fn benchmark_environment_pooling() -> AstResult<()> {
    println!("\n2. Environment Pooling Benchmark");
    println!("-------------------------------");

    // Create a simple nested function application expression
    let nested_expr = create_nested_function_application(5);

    // Benchmark with optimizations enabled
    let start = Instant::now();
    let mut evaluator = Evaluator::new();
    let result = evaluator.evaluate_expression(&nested_expr)?;
    let duration = start.elapsed();

    let (available, total) = evaluator.env_pool_stats();
    let stats = evaluator.cache_stats();

    println!("Result: {result:?}");
    println!("Time: {duration:?}");
    println!("Environment Pool - Available: {available}, Total: {total}");
    println!(
        "Cache Stats - Hits: {}, Misses: {}, Hit Rate: {:.2}%",
        stats.hits,
        stats.misses,
        stats.hit_rate()
    );

    Ok(())
}

fn create_nested_function_application(depth: usize) -> Expr {
    // Create a function that adds its parameter to a captured value
    let make_function = |n: i64| Expr {
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
                        kind: ExprKind::Literal(Literal::Integer(n)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    // Create nested function applications
    let mut current = Expr {
        kind: ExprKind::Literal(Literal::Integer(0)),
        span: Span::default(),
    };

    for i in 1..=depth {
        current = Expr {
            kind: ExprKind::Application {
                function: Box::new(make_function(i as i64)),
                argument: Box::new(current),
            },
            span: Span::default(),
        };
    }

    current
}

fn benchmark_cache_performance() -> AstResult<()> {
    println!("\n3. Cache Performance Benchmark");
    println!("-----------------------------");

    // Create a simple expression that will be evaluated multiple times
    let expression = Expr {
        kind: ExprKind::BinaryOp {
            operator: BinaryOperator::Multiply,
            left: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(3)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    // Benchmark cache performance by evaluating the same expression multiple times
    let start = Instant::now();
    let mut evaluator = Evaluator::new();

    // Evaluate the same expression multiple times to test caching
    for _ in 0..10 {
        let _result = evaluator.evaluate_expression(&expression)?;
    }

    let duration = start.elapsed();
    let stats = evaluator.cache_stats();

    println!("Time: {duration:?}");
    println!("Cache Hits: {}", stats.hits);
    println!("Cache Misses: {}", stats.misses);
    println!("Cache Hit Rate: {:.2}%", stats.hit_rate());
    println!("Cache Evictions: {}", stats.evictions);

    Ok(())
}
