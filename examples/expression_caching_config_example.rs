//! Expression Caching Configuration Example
//! 
//! This example demonstrates how to configure and use the advanced expression
//! caching system in Ligature with different optimization strategies.

use ligature_ast::{Expr, ExprKind, Literal, Program, Span};
use ligature_eval::{
    config::{CacheConfig, CacheableExpressions, EvaluatorConfig, PerformanceConfig, ConfigFormat},
    Evaluator,
};
use ligature_parser::parse_program;

/// Example 1: Basic caching with default configuration
fn example_basic_caching() {
    println!("=== Example 1: Basic Caching with Default Configuration ===");
    
    let mut evaluator = Evaluator::new();
    let config = evaluator.config();
    
    println!("Default cache configuration:");
    println!("  Enabled: {}", config.cache.enabled);
    println!("  Max Size: {}", config.cache.max_size);
    println!("  Max Memory: {} bytes", config.cache.max_memory_bytes);
    println!("  Cacheable Expressions:");
    println!("    Literals: {}", config.cache.cacheable_expressions.literals);
    println!("    Variables: {}", config.cache.cacheable_expressions.variables);
    println!("    Binary Ops: {}", config.cache.cacheable_expressions.binary_ops);
    println!("    Applications: {}", config.cache.cacheable_expressions.applications);
    
    // Create a simple program with repeated expressions
    let program_text = r#"
        let x = 5 + 3
        let y = 5 + 3  // Should be cached
        let z = x + y  // Should be cached
        let w = x + y  // Should hit cache
    "#;
    
    let program = parse_program(program_text).expect("Failed to parse program");
    evaluator.evaluate_program(&program).expect("Failed to evaluate program");
    
    let stats = evaluator.cache_stats();
    println!("\nCache Statistics:");
    println!("  Hits: {}", stats.hits);
    println!("  Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("  Cache Size: {}", evaluator.cache_size());
    println!("  Memory Usage: {} bytes", evaluator.cache_memory_usage());
}

/// Example 2: Aggressive caching configuration
fn example_aggressive_caching() {
    println!("\n=== Example 2: Aggressive Caching Configuration ===");
    
    let mut config = EvaluatorConfig::default();
    
    // Enable caching for all expression types
    config.cache.cacheable_expressions.applications = true;
    config.cache.cacheable_expressions.let_expressions = true;
    config.cache.cacheable_expressions.records = true;
    config.cache.cacheable_expressions.unions = true;
    config.cache.cacheable_expressions.matches = true;
    config.cache.cacheable_expressions.if_expressions = true;
    
    // Increase cache size and memory limits
    config.cache.max_size = 5000;
    config.cache.max_memory_bytes = 10 * 1024 * 1024; // 10MB
    
    // Enable cache warming
    config.cache.warming.enabled = true;
    config.cache.warming.max_expressions = 100;
    config.cache.warming.warm_on_module_load = true;
    
    let mut evaluator = Evaluator::with_config(config);
    
    println!("Aggressive cache configuration applied:");
    println!("  Max Size: {}", evaluator.config().cache.max_size);
    println!("  Max Memory: {} bytes", evaluator.config().cache.max_memory_bytes);
    println!("  All expression types cacheable: {}", 
        evaluator.config().cache.cacheable_expressions.applications);
    
    // Create a more complex program
    let program_text = r#"
        let add = \x -> \y -> x + y
        let multiply = \x -> \y -> x * y
        
        let result1 = add 5 3
        let result2 = add 5 3  // Should be cached
        let result3 = multiply 4 6
        let result4 = multiply 4 6  // Should be cached
        
        let complex = add (multiply 2 3) (multiply 4 5)
        let complex2 = add (multiply 2 3) (multiply 4 5)  // Should be cached
    "#;
    
    let program = parse_program(program_text).expect("Failed to parse program");
    evaluator.evaluate_program(&program).expect("Failed to evaluate program");
    
    let stats = evaluator.cache_stats();
    println!("\nAggressive Cache Statistics:");
    println!("  Hits: {}", stats.hits);
    println!("  Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("  Cache Size: {}", evaluator.cache_size());
    println!("  Memory Usage: {} bytes", evaluator.cache_memory_usage());
}

/// Example 3: Conservative caching for memory-constrained environments
fn example_conservative_caching() {
    println!("\n=== Example 3: Conservative Caching for Memory-Constrained Environments ===");
    
    let mut config = EvaluatorConfig::default();
    
    // Disable caching for complex expressions
    config.cache.cacheable_expressions.applications = false;
    config.cache.cacheable_expressions.let_expressions = false;
    config.cache.cacheable_expressions.records = false;
    config.cache.cacheable_expressions.unions = false;
    config.cache.cacheable_expressions.matches = false;
    config.cache.cacheable_expressions.if_expressions = false;
    
    // Small cache size and memory limits
    config.cache.max_size = 100;
    config.cache.max_memory_bytes = 64 * 1024; // 64KB
    
    // Disable cache warming
    config.cache.warming.enabled = false;
    
    let mut evaluator = Evaluator::with_config(config);
    
    println!("Conservative cache configuration applied:");
    println!("  Max Size: {}", evaluator.config().cache.max_size);
    println!("  Max Memory: {} bytes", evaluator.config().cache.max_memory_bytes);
    println!("  Only simple expressions cacheable");
    
    // Create expressions that should be cached
    let expressions = vec![
        Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default()),
        Expr::new(ExprKind::Literal(Literal::String("hello".to_string())), Span::default()),
        Expr::new(
            ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Add,
                left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default())),
                right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(2)), Span::default())),
            },
            Span::default(),
        ),
    ];
    
    // Evaluate each expression multiple times
    for expr in &expressions {
        for _ in 0..5 {
            evaluator.evaluate_expression(expr).expect("Failed to evaluate");
        }
    }
    
    let stats = evaluator.cache_stats();
    println!("\nConservative Cache Statistics:");
    println!("  Hits: {}", stats.hits);
    println!("  Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("  Cache Size: {}", evaluator.cache_size());
    println!("  Memory Usage: {} bytes", evaluator.cache_memory_usage());
    println!("  Evictions: {}", stats.evictions);
}

/// Example 4: Performance-focused configuration
fn example_performance_focused() {
    println!("\n=== Example 4: Performance-Focused Configuration ===");
    
    let mut config = EvaluatorConfig::default();
    
    // Optimize for performance
    config.performance.tail_call_optimization = true;
    config.performance.stack_based_evaluation = true;
    config.performance.value_optimization = true;
    config.performance.max_stack_depth = 50000;
    config.performance.env_pool_size = 500;
    config.performance.value_pool_size = 5000;
    
    // Aggressive caching
    config.cache.enabled = true;
    config.cache.max_size = 10000;
    config.cache.max_memory_bytes = 50 * 1024 * 1024; // 50MB
    config.cache.cacheable_expressions.applications = true;
    config.cache.cacheable_expressions.let_expressions = true;
    config.cache.cacheable_expressions.records = true;
    
    // Enable cache warming
    config.cache.warming.enabled = true;
    config.cache.warming.max_expressions = 500;
    config.cache.warming.warm_on_module_load = true;
    
    let mut evaluator = Evaluator::with_config(config);
    
    println!("Performance-focused configuration applied:");
    println!("  TCO: {}", evaluator.config().performance.tail_call_optimization);
    println!("  Stack Evaluation: {}", evaluator.config().performance.stack_based_evaluation);
    println!("  Value Optimization: {}", evaluator.config().performance.value_optimization);
    println!("  Cache Size: {}", evaluator.config().cache.max_size);
    println!("  Cache Memory: {} bytes", evaluator.config().cache.max_memory_bytes);
    
    // Performance test with complex expressions
    let start = std::time::Instant::now();
    
    let complex_expr = Expr::new(
        ExprKind::BinaryOp {
            operator: ligature_ast::BinaryOperator::Add,
            left: Box::new(Expr::new(
                ExprKind::BinaryOp {
                    operator: ligature_ast::BinaryOperator::Multiply,
                    left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(5)), Span::default())),
                    right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(3)), Span::default())),
                },
                Span::default(),
            )),
            right: Box::new(Expr::new(
                ExprKind::BinaryOp {
                    operator: ligature_ast::BinaryOperator::Multiply,
                    left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(4)), Span::default())),
                    right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(5)), Span::default())),
                },
                Span::default(),
            )),
        },
        Span::default(),
    );
    
    // Evaluate many times to test performance
    for _ in 0..1000 {
        evaluator.evaluate_expression(&complex_expr).expect("Failed to evaluate");
    }
    
    let duration = start.elapsed();
    let stats = evaluator.cache_stats();
    
    println!("\nPerformance Test Results:");
    println!("  Total Time: {duration:?}");
    println!("  Evaluations per second: {:.0}", 1000.0 / duration.as_secs_f64());
    println!("  Cache Hits: {}", stats.hits);
    println!("  Cache Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("  Tail Calls: {}", stats.tail_calls);
    println!("  Stack Evals: {}", stats.stack_evals);
    println!("  Env Pool Reuses: {}", stats.env_pool_reuses);
}

/// Example 5: Configuration persistence and loading
async fn example_configuration_persistence() {
    println!("\n=== Example 5: Configuration Persistence and Loading ===");
    
    // Create a custom configuration
    let mut config = EvaluatorConfig::default();
    config.cache.enabled = true;
    config.cache.max_size = 2000;
    config.cache.max_memory_bytes = 5 * 1024 * 1024; // 5MB
    config.cache.cacheable_expressions.applications = true;
    config.cache.cacheable_expressions.let_expressions = true;
    config.performance.tail_call_optimization = true;
    config.performance.stack_based_evaluation = true;
    
    let mut evaluator = Evaluator::with_config(config);
    
    println!("Custom configuration created:");
    println!("  Cache Size: {}", evaluator.config().cache.max_size);
    println!("  Cache Memory: {} bytes", evaluator.config().cache.max_memory_bytes);
    println!("  Applications Cacheable: {}", evaluator.config().cache.cacheable_expressions.applications);
    
    // Save configuration to file
    match evaluator.save_config(ConfigFormat::Toml).await {
        Ok(path) => println!("Configuration saved to: {path:?}"),
        Err(e) => println!("Failed to save configuration: {}", e),
    }
    
    // Load configuration from file
    match evaluator.load_config(None).await {
        Ok(()) => println!("Configuration loaded successfully"),
        Err(e) => println!("Failed to load configuration: {}", e),
    }
    
    // Verify configuration was loaded
    let loaded_config = evaluator.config();
    println!("Loaded configuration:");
    println!("  Cache Size: {}", loaded_config.cache.max_size);
    println!("  Cache Memory: {} bytes", loaded_config.cache.max_memory_bytes);
    println!("  Applications Cacheable: {}", loaded_config.cache.cacheable_expressions.applications);
}

/// Example 6: Dynamic configuration updates
fn example_dynamic_configuration() {
    println!("\n=== Example 6: Dynamic Configuration Updates ===");
    
    let mut evaluator = Evaluator::new();
    
    println!("Initial configuration:");
    println!("  Cache Size: {}", evaluator.config().cache.max_size);
    println!("  Applications Cacheable: {}", evaluator.config().cache.cacheable_expressions.applications);
    
    // Update configuration dynamically
    let mut new_config = EvaluatorConfig::default();
    new_config.cache.max_size = 3000;
    new_config.cache.cacheable_expressions.applications = true;
    new_config.cache.cacheable_expressions.let_expressions = true;
    
    evaluator.update_config(new_config);
    
    println!("Updated configuration:");
    println!("  Cache Size: {}", evaluator.config().cache.max_size);
    println!("  Applications Cacheable: {}", evaluator.config().cache.cacheable_expressions.applications);
    println!("  Let Expressions Cacheable: {}", evaluator.config().cache.cacheable_expressions.let_expressions);
    
    // Test the updated configuration
    let program_text = r#"
        let add = \x -> \y -> x + y
        let result1 = add 5 3
        let result2 = add 5 3  // Should be cached with new config
    "#;
    
    let program = parse_program(program_text).expect("Failed to parse program");
    evaluator.evaluate_program(&program).expect("Failed to evaluate program");
    
    let stats = evaluator.cache_stats();
    println!("\nDynamic Configuration Test Results:");
    println!("  Cache Hits: {}", stats.hits);
    println!("  Cache Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
}

/// Example 7: Cache warming demonstration
fn example_cache_warming() {
    println!("\n=== Example 7: Cache Warming Demonstration ===");
    
    let mut config = EvaluatorConfig::default();
    config.cache.warming.enabled = true;
    config.cache.warming.max_expressions = 50;
    
    let mut evaluator = Evaluator::with_config(config);
    
    // Create expressions to warm the cache
    let warming_expressions = vec![
        Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default()),
        Expr::new(ExprKind::Literal(Literal::String("hello".to_string())), Span::default()),
        Expr::new(
            ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Add,
                left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default())),
                right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(2)), Span::default())),
            },
            Span::default(),
        ),
        Expr::new(
            ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Multiply,
                left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(5)), Span::default())),
                right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(3)), Span::default())),
            },
            Span::default(),
        ),
    ];
    
    // Warm the cache
    let warming_data: Vec<(&Expr, &ligature_eval::environment::EvaluationEnvironment, usize)> = 
        warming_expressions.iter().map(|expr| (expr, &evaluator.environment, 0)).collect();
    
    evaluator.expression_cache.warm_cache(warming_data);
    
    println!("Cache warmed with {} expressions", warming_expressions.len());
    
    // Now evaluate the warmed expressions
    for expr in &warming_expressions {
        evaluator.evaluate_expression(expr).expect("Failed to evaluate");
    }
    
    let stats = evaluator.cache_stats();
    println!("\nCache Warming Results:");
    println!("  Warming Hits: {}", stats.warming_hits);
    println!("  Warming Misses: {}", stats.warming_misses);
    println!("  Warming Hit Rate: {:.2}%", stats.warming_hit_rate() * 100.0);
    println!("  Total Cache Hits: {}", stats.hits);
    println!("  Total Cache Misses: {}", stats.misses);
}

#[tokio::main]
async fn main() {
    println!("Expression Caching Configuration Examples");
    println!("=========================================\n");
    
    // Run all examples
    example_basic_caching();
    example_aggressive_caching();
    example_conservative_caching();
    example_performance_focused();
    example_configuration_persistence().await;
    example_dynamic_configuration();
    example_cache_warming();
    
    println!("\n=== Summary ===");
    println!("Expression caching system provides:");
    println!("  • Configurable caching strategies");
    println!("  • Environment-aware cache keys");
    println!("  • LRU eviction with memory limits");
    println!("  • Cache warming capabilities");
    println!("  • Comprehensive statistics tracking");
    println!("  • Dynamic configuration updates");
    println!("  • Configuration persistence");
    println!("  • Performance optimization integration");
} 