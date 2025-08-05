use ligature_parser::parse_expression;

fn main() {
    println!("Testing Expression Caching Implementation\n");

    // Test 1: Basic caching functionality
    println!("Test 1: Basic caching functionality");
    let mut evaluator = ligature_eval::Evaluator::new();

    // Set a small cache size to test eviction
    evaluator.set_cache_size_limit(5);

    // Parse a simple expression
    let expr = parse_expression("2 + 3 * 4").unwrap();

    // Evaluate it multiple times
    for i in 0..3 {
        let start = std::time::Instant::now();
        let result = evaluator.evaluate_expression(&expr).unwrap();
        let duration = start.elapsed();
        println!("  Evaluation {}: {:?} (took {:?})", i + 1, result, duration);
    }

    // Check cache statistics
    let stats = evaluator.cache_stats();
    println!("  Cache hits: {}", stats.hits);
    println!("  Cache misses: {}", stats.misses);
    println!("  Cache hit rate: {:.2}%", stats.hit_rate());
    println!("  Cache evictions: {}", stats.evictions);
    println!(
        "  Cache size: {}/{}",
        evaluator.cache_size(),
        evaluator.cache_size_limit()
    );
    println!();

    // Test 2: Cache eviction
    println!("Test 2: Cache eviction");
    let mut evaluator2 = ligature_eval::Evaluator::new();
    evaluator2.set_cache_size_limit(3);

    // Evaluate multiple different expressions to trigger eviction
    let expressions = ["1 + 1", "2 + 2", "3 + 3", "4 + 4", "5 + 5"];

    for (i, expr_str) in expressions.iter().enumerate() {
        let expr = parse_expression(expr_str).unwrap();
        let result = evaluator2.evaluate_expression(&expr).unwrap();
        println!("  Expression {}: {} = {:?}", i + 1, expr_str, result);
    }

    let stats2 = evaluator2.cache_stats();
    println!("  Cache hits: {}", stats2.hits);
    println!("  Cache misses: {}", stats2.misses);
    println!("  Cache hit rate: {:.2}%", stats2.hit_rate());
    println!("  Cache evictions: {}", stats2.evictions);
    println!(
        "  Cache size: {}/{}",
        evaluator2.cache_size(),
        evaluator2.cache_size_limit()
    );
    println!();

    // Test 3: Cache invalidation
    println!("Test 3: Cache invalidation");
    let mut evaluator3 = ligature_eval::Evaluator::new();

    let expr = parse_expression("x + 1").unwrap();

    // First evaluation should miss
    let result1 = evaluator3.evaluate_expression(&expr).unwrap_err(); // Should fail due to undefined variable
    println!("  First evaluation: {result1:?}");

    // Check cache stats
    let stats3 = evaluator3.cache_stats();
    println!(
        "  After first evaluation - hits: {}, misses: {}",
        stats3.hits, stats3.misses
    );

    // Clear cache
    evaluator3.clear_cache();
    let stats3_after_clear = evaluator3.cache_stats();
    println!(
        "  After clearing cache - hits: {}, misses: {}",
        stats3_after_clear.hits, stats3_after_clear.misses
    );
    println!();

    // Test 4: Cache performance with repeated expressions
    println!("Test 4: Cache performance with repeated expressions");
    let mut evaluator4 = ligature_eval::Evaluator::new();

    let expressions = [
        "2 + 3", "5 * 7", "10 - 4", "2 + 3",  // Repeated
        "5 * 7",  // Repeated
        "10 - 4", // Repeated
        "2 + 3",  // Repeated again
    ];

    for (i, expr_str) in expressions.iter().enumerate() {
        let expr = parse_expression(expr_str).unwrap();
        let start = std::time::Instant::now();
        let result = evaluator4.evaluate_expression(&expr).unwrap();
        let duration = start.elapsed();
        println!(
            "  Expression {}: {} = {:?} (took {:?})",
            i + 1,
            expr_str,
            result,
            duration
        );
    }

    let stats4 = evaluator4.cache_stats();
    println!("  Final cache stats:");
    println!("    Hits: {}", stats4.hits);
    println!("    Misses: {}", stats4.misses);
    println!("    Hit rate: {:.2}%", stats4.hit_rate());
    println!("    Evictions: {}", stats4.evictions);
    println!(
        "    Cache size: {}/{}",
        evaluator4.cache_size(),
        evaluator4.cache_size_limit()
    );

    println!("\n✅ Expression caching implementation test completed!");
}
