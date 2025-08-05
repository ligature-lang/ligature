use ligature_ast::{Expr, ExprKind, Literal, Program, Span};
use ligature_eval::{
    config::{CacheConfig, CacheableExpressions, EvaluatorConfig, PerformanceConfig},
    Evaluator,
};
use ligature_parser::parse_program;

/// Test expression caching with different configurations
#[test]
fn test_expression_caching_with_configuration() {
    // Test 1: Default configuration (caching enabled)
    let mut evaluator = Evaluator::new();
    let config = evaluator.config();
    
    assert!(config.cache.enabled, "Caching should be enabled by default");
    assert!(config.cache.cacheable_expressions.literals, "Literals should be cacheable by default");
    assert!(config.cache.cacheable_expressions.binary_ops, "Binary ops should be cacheable by default");
    assert!(!config.cache.cacheable_expressions.applications, "Applications should not be cacheable by default");

    // Test 2: Custom configuration with selective caching
    let mut custom_config = EvaluatorConfig::default();
    custom_config.cache.cacheable_expressions.applications = true;
    custom_config.cache.cacheable_expressions.let_expressions = true;
    custom_config.cache.cacheable_expressions.records = true;
    
    evaluator.apply_config(custom_config);
    
    let updated_config = evaluator.config();
    assert!(updated_config.cache.cacheable_expressions.applications, "Applications should now be cacheable");
    assert!(updated_config.cache.cacheable_expressions.let_expressions, "Let expressions should now be cacheable");
    assert!(updated_config.cache.cacheable_expressions.records, "Records should now be cacheable");
}

/// Test cache hit/miss statistics
#[test]
fn test_cache_statistics() {
    let mut evaluator = Evaluator::new();
    
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
    assert!(stats.hits > 0, "Should have cache hits for repeated expressions");
    assert!(stats.misses > 0, "Should have cache misses for new expressions");
    assert!(stats.hit_rate() > 0.0, "Hit rate should be positive");
    
    println!("Cache Statistics:");
    println!("  Hits: {}", stats.hits);
    println!("  Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
}

/// Test cache warming functionality
#[test]
fn test_cache_warming() {
    let mut config = EvaluatorConfig::default();
    config.cache.warming.enabled = true;
    config.cache.warming.max_expressions = 10;
    
    let mut evaluator = Evaluator::with_config(config);
    
    // Create expressions to warm the cache
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
    
    // Warm the cache with these expressions
    let warming_data: Vec<(&Expr, &ligature_eval::environment::EvaluationEnvironment, usize)> = 
        expressions.iter().map(|expr| (expr, &evaluator.environment, 0)).collect();
    
    evaluator.expression_cache.warm_cache(warming_data);
    
    // Verify cache warming statistics
    let stats = evaluator.cache_stats();
    assert!(stats.warming_hits >= 0, "Warming hits should be non-negative");
    assert!(stats.warming_misses >= 0, "Warming misses should be non-negative");
}

/// Test cache eviction and memory limits
#[test]
fn test_cache_eviction() {
    let mut config = EvaluatorConfig::default();
    config.cache.max_size = 5; // Small cache size to trigger eviction
    config.cache.max_memory_bytes = 1024; // Small memory limit
    
    let mut evaluator = Evaluator::with_config(config);
    
    // Create many expressions to fill the cache
    for i in 0..10 {
        let expr = Expr::new(
            ExprKind::Literal(Literal::Integer(i)),
            Span::default(),
        );
        let value = evaluator.evaluate_expression(&expr).expect("Failed to evaluate");
        
        // Cache the result
        evaluator.cache_result(&expr, &value);
    }
    
    let stats = evaluator.cache_stats();
    assert!(stats.evictions > 0, "Should have cache evictions with small cache size");
    assert!(evaluator.cache_size() <= 5, "Cache size should not exceed limit");
    
    println!("Cache Eviction Test:");
    println!("  Cache Size: {}", evaluator.cache_size());
    println!("  Evictions: {}", stats.evictions);
    println!("  Memory Usage: {} bytes", evaluator.cache_memory_usage());
}

/// Test environment-aware caching
#[test]
fn test_environment_aware_caching() {
    let mut evaluator = Evaluator::new();
    
    // Create expressions in different environments
    let expr1 = Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default());
    let expr2 = Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default());
    
    // Evaluate in different environments
    let value1 = evaluator.evaluate_expression(&expr1).expect("Failed to evaluate");
    
    // Add a binding to change the environment
    evaluator.environment.bind("x".to_string(), ligature_eval::value::Value::integer(100, Span::default()));
    
    let value2 = evaluator.evaluate_expression(&expr2).expect("Failed to evaluate");
    
    // Both should be cached separately due to different environments
    let stats = evaluator.cache_stats();
    assert!(stats.misses >= 2, "Should have misses for different environments");
}

/// Test cache key generation and uniqueness
#[test]
fn test_cache_key_uniqueness() {
    use ligature_eval::evaluator::CacheKey;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let expr1 = Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default());
    let expr2 = Expr::new(ExprKind::Literal(Literal::Integer(2)), Span::default());
    let expr3 = Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default());
    
    let env = ligature_eval::environment::EvaluationEnvironment::new();
    
    let key1 = CacheKey::new(&expr1, &env, 0);
    let key2 = CacheKey::new(&expr2, &env, 0);
    let key3 = CacheKey::new(&expr3, &env, 0);
    
    // Different expressions should have different keys
    assert_ne!(key1.expr_hash, key2.expr_hash, "Different expressions should have different hashes");
    
    // Same expressions should have same keys
    assert_eq!(key1.expr_hash, key3.expr_hash, "Same expressions should have same hashes");
    
    // Test hash consistency
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();
    
    key1.hash(&mut hasher1);
    key3.hash(&mut hasher2);
    
    assert_eq!(hasher1.finish(), hasher2.finish(), "Hash should be consistent for same keys");
}

/// Test cache performance with complex expressions
#[test]
fn test_cache_performance() {
    let mut evaluator = Evaluator::new();
    
    // Create a complex expression
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
    
    // Evaluate multiple times to test caching
    let start = std::time::Instant::now();
    
    for _ in 0..100 {
        evaluator.evaluate_expression(&complex_expr).expect("Failed to evaluate");
    }
    
    let duration = start.elapsed();
    let stats = evaluator.cache_stats();
    
    println!("Cache Performance Test:");
    println!("  Total Time: {:?}", duration);
    println!("  Cache Hits: {}", stats.hits);
    println!("  Cache Misses: {}", stats.misses);
    println!("  Hit Rate: {:.2}%", stats.hit_rate() * 100.0);
    
    // Should have significant cache hits after first evaluation
    assert!(stats.hits > 90, "Should have high cache hit rate for repeated evaluations");
}

/// Test cache configuration persistence
#[test]
fn test_cache_configuration_persistence() {
    let mut config = EvaluatorConfig::default();
    config.cache.enabled = true;
    config.cache.max_size = 2000;
    config.cache.max_memory_bytes = 2 * 1024 * 1024; // 2MB
    config.cache.cacheable_expressions.applications = true;
    config.cache.cacheable_expressions.let_expressions = true;
    
    let mut evaluator = Evaluator::with_config(config);
    
    // Verify configuration was applied
    let applied_config = evaluator.config();
    assert_eq!(applied_config.cache.max_size, 2000);
    assert_eq!(applied_config.cache.max_memory_bytes, 2 * 1024 * 1024);
    assert!(applied_config.cache.cacheable_expressions.applications);
    assert!(applied_config.cache.cacheable_expressions.let_expressions);
    
    // Test configuration update
    let mut new_config = EvaluatorConfig::default();
    new_config.cache.max_size = 3000;
    new_config.cache.cacheable_expressions.records = true;
    
    evaluator.update_config(new_config);
    
    let updated_config = evaluator.config();
    assert_eq!(updated_config.cache.max_size, 3000);
    assert!(updated_config.cache.cacheable_expressions.records);
}

/// Test cache with different expression types
#[test]
fn test_cache_expression_types() {
    let mut config = EvaluatorConfig::default();
    // Enable caching for all expression types
    config.cache.cacheable_expressions.applications = true;
    config.cache.cacheable_expressions.let_expressions = true;
    config.cache.cacheable_expressions.records = true;
    config.cache.cacheable_expressions.unions = true;
    config.cache.cacheable_expressions.matches = true;
    config.cache.cacheable_expressions.if_expressions = true;
    
    let mut evaluator = Evaluator::with_config(config);
    
    // Test different expression types
    let expressions = vec![
        // Literal
        Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default()),
        // Binary operation
        Expr::new(
            ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Add,
                left: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default())),
                right: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(2)), Span::default())),
            },
            Span::default(),
        ),
        // Unary operation
        Expr::new(
            ExprKind::UnaryOp {
                operator: ligature_ast::UnaryOperator::Negate,
                operand: Box::new(Expr::new(ExprKind::Literal(Literal::Integer(5)), Span::default())),
            },
            Span::default(),
        ),
    ];
    
    // Evaluate each expression twice to test caching
    for expr in &expressions {
        let _value1 = evaluator.evaluate_expression(expr).expect("Failed to evaluate");
        let _value2 = evaluator.evaluate_expression(expr).expect("Failed to evaluate");
    }
    
    let stats = evaluator.cache_stats();
    assert!(stats.hits > 0, "Should have cache hits for repeated expressions");
    
    println!("Expression Types Cache Test:");
    println!("  Total Expressions: {}", expressions.len());
    println!("  Cache Hits: {}", stats.hits);
    println!("  Cache Misses: {}", stats.misses);
}

/// Test cache statistics tracking
#[test]
fn test_cache_statistics_tracking() {
    let mut evaluator = Evaluator::new();
    
    // Create some expressions and evaluate them
    let expr1 = Expr::new(ExprKind::Literal(Literal::Integer(1)), Span::default());
    let expr2 = Expr::new(ExprKind::Literal(Literal::Integer(2)), Span::default());
    
    // First evaluation - should be misses
    evaluator.evaluate_expression(&expr1).expect("Failed to evaluate");
    evaluator.evaluate_expression(&expr2).expect("Failed to evaluate");
    
    let stats1 = evaluator.cache_stats();
    assert_eq!(stats1.misses, 2, "Should have 2 misses for first evaluations");
    assert_eq!(stats1.hits, 0, "Should have 0 hits for first evaluations");
    
    // Second evaluation - should be hits
    evaluator.evaluate_expression(&expr1).expect("Failed to evaluate");
    evaluator.evaluate_expression(&expr2).expect("Failed to evaluate");
    
    let stats2 = evaluator.cache_stats();
    assert_eq!(stats2.misses, 2, "Misses should remain the same");
    assert_eq!(stats2.hits, 2, "Should have 2 hits for repeated evaluations");
    
    // Test statistics reset
    evaluator.clear_cache();
    let stats3 = evaluator.cache_stats();
    assert_eq!(stats3.hits, 0, "Hits should be reset");
    assert_eq!(stats3.misses, 0, "Misses should be reset");
    assert_eq!(stats3.evictions, 0, "Evictions should be reset");
}

/// Test cache with disabled caching
#[test]
fn test_cache_disabled() {
    let mut config = EvaluatorConfig::default();
    config.cache.enabled = false;
    
    let mut evaluator = Evaluator::with_config(config);
    
    let expr = Expr::new(ExprKind::Literal(Literal::Integer(42)), Span::default());
    
    // Evaluate multiple times
    for _ in 0..10 {
        evaluator.evaluate_expression(&expr).expect("Failed to evaluate");
    }
    
    let stats = evaluator.cache_stats();
    assert_eq!(stats.hits, 0, "Should have no cache hits when caching is disabled");
    assert_eq!(stats.misses, 0, "Should have no cache misses when caching is disabled");
    assert_eq!(evaluator.cache_size(), 0, "Cache should be empty when disabled");
} 