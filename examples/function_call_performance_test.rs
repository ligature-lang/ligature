//! Realistic function call performance benchmark that tests actual function evaluation
//! without relying on caching to get a true measure of function call overhead.

use ligature_ast::{AstResult, BinaryOperator, Expr, ExprKind, Literal, Span};
use ligature_eval::Evaluator;
use std::time::Instant;

fn main() -> AstResult<()> {
    println!("Realistic Function Call Performance Benchmark");
    println!("=============================================");
    println!("Testing actual function call performance without caching");
    println!();

    // Test 1: Simple function calls without caching
    benchmark_simple_function_calls()?;

    // Test 2: Function calls with different arguments (no caching benefit)
    benchmark_varied_function_calls()?;

    // Test 3: Nested function calls
    benchmark_nested_function_calls()?;

    // Test 4: Function calls with environment capture
    benchmark_closure_calls()?;

    // Test 5: Comparison with optimizations enabled/disabled
    benchmark_optimization_impact()?;

    Ok(())
}

fn benchmark_simple_function_calls() -> AstResult<()> {
    println!("1. Simple Function Calls (No Caching)");
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

    // Benchmark with caching DISABLED to test actual function call performance
    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    evaluator.set_caching(false); // Disable caching for realistic test
    evaluator.set_value_optimization(true);

    let iterations = 10_000;
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

    Ok(())
}

fn benchmark_varied_function_calls() -> AstResult<()> {
    println!("\n2. Varied Function Calls (Different Arguments)");
    println!("----------------------------------------------");

    // Create a simple function: \x -> x * 2
    let function = create_doubling_function();

    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    evaluator.set_caching(false);
    evaluator.set_value_optimization(true);

    let iterations = 10_000;
    let start = Instant::now();

    // Call with different arguments each time to avoid caching benefits
    for i in 0..iterations {
        let application = Expr {
            kind: ExprKind::Application {
                function: Box::new(function.clone()),
                argument: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(i as i64)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };
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

    Ok(())
}

fn benchmark_nested_function_calls() -> AstResult<()> {
    println!("\n3. Nested Function Calls");
    println!("------------------------");

    // Create nested function: \x -> (\y -> x + y) 10
    let inner_function = create_simple_function();
    let outer_function = Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::Application {
                    function: Box::new(inner_function),
                    argument: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(10)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    evaluator.set_caching(false);
    evaluator.set_value_optimization(true);

    let iterations = 5_000;
    let start = Instant::now();

    for i in 0..iterations {
        let application = Expr {
            kind: ExprKind::Application {
                function: Box::new(outer_function.clone()),
                argument: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(i as i64)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };
        let _result = evaluator.evaluate_expression(&application)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    let stats = evaluator.cache_stats();

    println!("Nested function calls per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!("Stack evaluations: {}", stats.stack_evals);
    println!("Tail calls: {}", stats.tail_calls);

    Ok(())
}

fn benchmark_closure_calls() -> AstResult<()> {
    println!("\n4. Closure Calls (Environment Capture)");
    println!("--------------------------------------");

    // Create a closure that captures a variable: let x = 5 in \y -> x + y
    let closure = create_closure_with_capture();

    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    evaluator.set_tail_call_optimization(true);
    evaluator.set_caching(false);
    evaluator.set_value_optimization(true);

    let iterations = 5_000;
    let start = Instant::now();

    for i in 0..iterations {
        let application = Expr {
            kind: ExprKind::Application {
                function: Box::new(closure.clone()),
                argument: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(i as i64)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };
        let _result = evaluator.evaluate_expression(&application)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    let stats = evaluator.cache_stats();

    println!("Closure calls per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!("Stack evaluations: {}", stats.stack_evals);
    println!("Tail calls: {}", stats.tail_calls);

    Ok(())
}

fn benchmark_optimization_impact() -> AstResult<()> {
    println!("\n5. Optimization Impact Comparison");
    println!("---------------------------------");

    let function = create_simple_function();
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

    let iterations = 5_000;

    // Test with optimizations disabled
    let mut evaluator_basic = Evaluator::new();
    evaluator_basic.set_stack_based_evaluation(false);
    evaluator_basic.set_tail_call_optimization(false);
    evaluator_basic.set_caching(false);
    evaluator_basic.set_value_optimization(false);

    let start = Instant::now();
    for _ in 0..iterations {
        let _result = evaluator_basic.evaluate_expression(&application)?;
    }
    let basic_duration = start.elapsed();
    let basic_ops_per_sec = iterations as f64 / basic_duration.as_secs_f64();

    // Test with optimizations enabled
    let mut evaluator_optimized = Evaluator::new();
    evaluator_optimized.set_stack_based_evaluation(true);
    evaluator_optimized.set_tail_call_optimization(true);
    evaluator_optimized.set_caching(false);
    evaluator_optimized.set_value_optimization(true);

    let start = Instant::now();
    for _ in 0..iterations {
        let _result = evaluator_optimized.evaluate_expression(&application)?;
    }
    let optimized_duration = start.elapsed();
    let optimized_ops_per_sec = iterations as f64 / optimized_duration.as_secs_f64();

    let improvement = optimized_ops_per_sec / basic_ops_per_sec;

    println!("Basic (no optimizations): {basic_ops_per_sec:.0} ops/sec");
    println!("Optimized: {optimized_ops_per_sec:.0} ops/sec");
    println!("Improvement: {improvement:.1}x");
    println!("Basic time: {basic_duration:?}");
    println!("Optimized time: {optimized_duration:?}");

    Ok(())
}

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

fn create_doubling_function() -> Expr {
    Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Multiply,
                    left: Box::new(Expr {
                        kind: ExprKind::Variable("x".to_string()),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(2)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    }
}

fn create_closure_with_capture() -> Expr {
    // let x = 5 in \y -> x + y
    Expr {
        kind: ExprKind::Let {
            name: "x".to_string(),
            value: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
            body: Box::new(Expr {
                kind: ExprKind::Abstraction {
                    parameter: "y".to_string(),
                    parameter_type: None,
                    body: Box::new(Expr {
                        kind: ExprKind::BinaryOp {
                            operator: BinaryOperator::Add,
                            left: Box::new(Expr {
                                kind: ExprKind::Variable("x".to_string()),
                                span: Span::default(),
                            }),
                            right: Box::new(Expr {
                                kind: ExprKind::Variable("y".to_string()),
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
    }
}
