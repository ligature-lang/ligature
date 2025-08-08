//! Simple performance test for Ligature optimizations.

use std::time::Instant;

use ligature_ast::{AstResult, BinaryOperator, Expr, ExprKind, Literal, Span};
use ligature_eval::Evaluator;

fn main() -> AstResult<()> {
    println!("Simple Ligature Performance Test");
    println!("===============================");

    // Test 1: Basic arithmetic performance
    test_arithmetic_performance()?;

    // Test 2: Function call performance
    test_function_call_performance()?;

    // Test 3: Value creation performance
    test_value_creation_performance()?;

    Ok(())
}

fn test_arithmetic_performance() -> AstResult<()> {
    println!("\n1. Arithmetic Performance Test");
    println!("-----------------------------");

    // Create a simple arithmetic expression: 1 + 2 * 3
    let arithmetic_expr = Expr {
        kind: ExprKind::BinaryOp {
            operator: BinaryOperator::Add,
            left: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(1)),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Multiply,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(2)),
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
    };

    let mut evaluator = Evaluator::new();

    let iterations = 100_000;
    let start = Instant::now();

    for _ in 0..iterations {
        let _result = evaluator.evaluate_expression(&arithmetic_expr)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    println!("Arithmetic operations per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!(
        "Result: {:?}",
        evaluator.evaluate_expression(&arithmetic_expr)?
    );

    Ok(())
}

fn test_function_call_performance() -> AstResult<()> {
    println!("\n2. Function Call Performance Test");
    println!("--------------------------------");

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

    let mut evaluator = Evaluator::new();

    let iterations = 10_000;
    let start = Instant::now();

    for _ in 0..iterations {
        let _result = evaluator.evaluate_expression(&application)?;
    }

    let duration = start.elapsed();
    let ops_per_sec = iterations as f64 / duration.as_secs_f64();

    println!("Function calls per second: {ops_per_sec:.0}");
    println!("Total time: {duration:?}");
    println!("Result: {:?}", evaluator.evaluate_expression(&application)?);

    Ok(())
}

fn test_value_creation_performance() -> AstResult<()> {
    println!("\n3. Value Creation Performance Test");
    println!("---------------------------------");

    let iterations = 1_000_000;

    // Test integer value creation
    let start = Instant::now();
    for i in 0..iterations {
        let _value = ligature_eval::Value::integer(i, Span::default());
    }
    let int_duration = start.elapsed();

    // Test string value creation
    let start = Instant::now();
    for i in 0..iterations {
        let _value = ligature_eval::Value::string(format!("string_{i}"), Span::default());
    }
    let string_duration = start.elapsed();

    println!(
        "Integer value creation: {:.0} ops/sec",
        iterations as f64 / int_duration.as_secs_f64()
    );
    println!(
        "String value creation: {:.0} ops/sec",
        iterations as f64 / string_duration.as_secs_f64()
    );
    println!("Integer time: {int_duration:?}");
    println!("String time: {string_duration:?}");

    Ok(())
}
