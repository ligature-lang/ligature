//! Example demonstrating async evaluation capabilities.
//!
//! This example shows how to use the async evaluator for evaluating
//! Ligature programs, modules, and expressions asynchronously.

use ligature_ast::{
    Declaration, DeclarationKind, Expr, ExprKind, Literal, Program, Span, ValueDeclaration,
};
use ligature_eval::{AsyncEvaluator, AsyncEvaluatorConfig};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Async Evaluation Example ===\n");

    // Create an async evaluator with custom configuration
    let config = AsyncEvaluatorConfig {
        max_concurrent_tasks: 2,
        work_queue_capacity: 100,
        task_timeout: std::time::Duration::from_secs(10),
        enable_parallel: true,
        evaluator_config: ligature_eval::EvaluatorConfig::default(),
    };

    let evaluator = AsyncEvaluator::with_config(config);
    println!("✅ Created async evaluator");

    // Example 1: Evaluate a simple expression
    println!("\n--- Example 1: Simple Expression ---");
    let expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };

    let result = evaluator.evaluate_expression(&expr).await?;
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

    let result = evaluator.evaluate_expression(&binary_expr).await?;
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
        span: Span::default(),
    };

    let result = evaluator.evaluate_program(&program).await?;
    println!("Program result: {result:?}");

    // Example 4: Progress tracking
    println!("\n--- Example 4: Progress Tracking ---");
    let progress = evaluator.get_progress().await;
    println!("Total tasks: {}", progress.total_tasks);
    println!("Completed tasks: {}", progress.completed_tasks);
    println!("Failed tasks: {}", progress.failed_tasks);
    println!("Active tasks: {}", progress.active_tasks);
    println!(
        "Completion percentage: {:.1}%",
        progress.completion_percentage()
    );
    println!("Elapsed time: {:?}", progress.elapsed_time());

    // Example 5: Performance metrics
    println!("\n--- Example 5: Performance Metrics ---");
    let metrics = evaluator.get_metrics();
    println!("Recorded {} performance metrics", metrics.len());

    for metric in metrics.iter().take(3) {
        println!("  - {}: {:?}", metric.operation_name, metric.execution_time);
    }

    // Clean shutdown
    println!("\n--- Shutdown ---");
    evaluator.shutdown().await;
    println!("✅ Async evaluator shutdown complete");

    println!("\n=== Example completed successfully! ===");
    Ok(())
}
