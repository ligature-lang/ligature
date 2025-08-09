//! Example demonstrating async evaluation capabilities.
//!
//! This example shows how to use the async evaluator for evaluating
//! Ligature programs, modules, and expressions asynchronously.

use ligature_ast::{
    Declaration, DeclarationKind, Expr, ExprKind, Literal, Program, Span, ValueDeclaration,
};
use ligature_eval::{EnhancedAsyncEvaluator, EnhancedAsyncEvaluatorConfig};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Async Evaluation Example ===\n");

    // Create an async evaluator with custom configuration
    let config = EnhancedAsyncEvaluatorConfig {
        num_workers: 2,
        expression_cache_size: 100,
        value_cache_size: 50,
        max_cache_memory: 1000000,
        task_timeout: std::time::Duration::from_secs(10),
        enable_concurrent_type_checking: true,
        enable_expression_caching: true,
        enable_value_caching: true,
        enable_performance_monitoring: true,
    };

    let evaluator = EnhancedAsyncEvaluator::new(config)?;
    println!("✅ Created async evaluator");

    // Example 1: Evaluate a simple expression
    println!("\n--- Example 1: Simple Expression ---");
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };

    let env = ligature_eval::EvaluationEnvironment::new();
    let result = evaluator.evaluate_expression(&expr, &env).await?;
    println!("Expression result: {result:?}");

    // Example 2: Evaluate a binary operation
    println!("\n--- Example 2: Binary Operation ---");
    let binary_expr = Expr {
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
    };

    let result = evaluator.evaluate_expression(&binary_expr, &env).await?;
    println!("Binary operation result: {result:?}");

    // Example 3: Evaluate a program
    println!("\n--- Example 3: Program Evaluation ---");
    let program = Program {
        declarations: vec![Declaration::new(
            DeclarationKind::Value(ValueDeclaration {
                name: "x".to_string(),
                type_annotation: None,
                value: Expr {
                    kind: ExprKind::Literal(Literal::Integer(100)),
                    span: Span::default(),
                },
                is_recursive: false,
                span: Span::default(),
            }),
            Span::default(),
        )],
    };

    let result = evaluator.evaluate_program(&program).await?;
    println!("Program result: {result:?}");

    // Example 4: Performance metrics
    println!("\n--- Example 4: Performance Metrics ---");
    let metrics = evaluator.performance_metrics().await;
    println!("Total evaluation time: {:?}", metrics.total_evaluation_time);
    println!("Type checking time: {:?}", metrics.type_checking_time);
    println!(
        "Expression evaluation time: {:?}",
        metrics.expression_evaluation_time
    );
    println!("Cache hits: {}", metrics.cache_hits);
    println!("Cache misses: {}", metrics.cache_misses);
    println!("Cache hit rate: {:.1}%", metrics.cache_hit_rate() * 100.0);
    println!("Concurrent tasks: {}", metrics.concurrent_tasks);
    println!(
        "Average evaluation time: {:?}",
        metrics.average_evaluation_time()
    );

    // Example 5: Statistics
    println!("\n--- Example 5: Statistics ---");
    let stats = evaluator.stats();
    println!("Recorded {} statistics", stats.len());

    for (key, value) in stats.iter().take(3) {
        println!("  - {key}: {value}");
    }

    // Cleanup
    println!("\n--- Cleanup ---");
    evaluator.clear_caches();
    println!("✅ Caches cleared");

    println!("\n=== Example completed successfully! ===");
    Ok(())
}
