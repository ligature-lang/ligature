//! Example demonstrating advanced performance optimizations in Ligature.

use ligature_eval::{
    advanced_optimizations::*,
    config::{
        AdvancedOptimizationConfig, EvaluatorConfig, MemoryManagementConfig,
        ParallelEvaluationConfig,
    },
    Evaluator,
};
use ligature_parser::parse_expression;
use std::time::Instant;

fn main() {
    println!("=== Ligature Advanced Performance Optimizations Demo ===\n");

    // 1. Advanced Tail Call Detection
    demo_advanced_tail_call_detection();

    // 2. Function Inlining
    demo_function_inlining();

    // 3. Closure Capture Optimization
    demo_closure_capture_optimization();

    // 4. Parallel Evaluation
    demo_parallel_evaluation();

    // 5. Generational Garbage Collection
    demo_generational_gc();

    // 6. Integrated Performance Test
    demo_integrated_performance();

    println!("\n=== Demo Complete ===");
}

fn demo_advanced_tail_call_detection() {
    println!("1. Advanced Tail Call Detection");
    println!("   -----------------------------");

    let config = AdvancedOptimizationConfig {
        advanced_tail_call_detection: true,
        pattern_based_tco: true,
        context_sensitive_tco: true,
        nested_function_tco: true,
        ..Default::default()
    };

    let mut detector = AdvancedTailCallDetector::new(config);

    // Test recursive factorial function
    let factorial_source = r#"
        let factorial = \n -> 
            if n <= 1 then 1 
            else n * factorial (n - 1);
        factorial
    "#;

    let factorial_expr = parse_expression(factorial_source).unwrap();
    let has_tail_calls = detector.detect_advanced_tail_calls(&factorial_expr);
    println!("   Factorial function has tail calls: {}", has_tail_calls);

    // Test tail-recursive factorial function
    let tail_factorial_source = r#"
        let tail_factorial = \n acc -> 
            if n <= 1 then acc 
            else tail_factorial (n - 1) (n * acc);
        tail_factorial
    "#;

    let tail_factorial_expr = parse_expression(tail_factorial_source).unwrap();
    let has_tail_calls = detector.detect_advanced_tail_calls(&tail_factorial_expr);
    println!(
        "   Tail-recursive factorial has tail calls: {}",
        has_tail_calls
    );

    // Test nested function with tail calls
    let nested_source = r#"
        let outer = \x -> 
            let inner = \y -> y + 1; 
            inner x;
        outer
    "#;

    let nested_expr = parse_expression(nested_source).unwrap();
    let has_tail_calls = detector.detect_advanced_tail_calls(&nested_expr);
    println!("   Nested function has tail calls: {}", has_tail_calls);
    println!();
}

fn demo_function_inlining() {
    println!("2. Function Inlining");
    println!("   -----------------");

    let config = AdvancedOptimizationConfig {
        function_inlining: true,
        max_inline_size: 10,
        ..Default::default()
    };

    let mut inliner = FunctionInliner::new(config);

    // Test small function that should be inlined
    let small_function_source = r#"
        \x -> x + 1
    "#;

    let small_function = parse_expression(small_function_source).unwrap();
    let argument = parse_expression("5").unwrap();

    let should_inline = inliner.should_inline(&small_function, &argument);
    println!("   Small function should be inlined: {}", should_inline);

    // Test larger function that should not be inlined
    let large_function_source = r#"
        \x -> 
            let y = x + 1;
            let z = y * 2;
            let w = z - 3;
            w * w
    "#;

    let large_function = parse_expression(large_function_source).unwrap();
    let should_inline = inliner.should_inline(&large_function, &argument);
    println!("   Large function should be inlined: {}", should_inline);

    // Test pure vs impure functions
    let pure_function_source = r#"
        \x -> x * x
    "#;

    let pure_function = parse_expression(pure_function_source).unwrap();
    let should_inline = inliner.should_inline(&pure_function, &argument);
    println!("   Pure function should be inlined: {}", should_inline);

    let stats = inliner.stats();
    println!("   Inlining statistics: {stats:?}");
    println!();
}

fn demo_closure_capture_optimization() {
    println!("3. Closure Capture Optimization");
    println!("   ----------------------------");

    let config = AdvancedOptimizationConfig {
        closure_optimization: true,
        minimal_capture: true,
        ..Default::default()
    };

    let mut optimizer = ClosureCaptureOptimizer::new(config);

    // Test closure with unused captures
    let closure_source = r#"
        \x -> x + 1
    "#;

    let closure_expr = parse_expression(closure_source).unwrap();
    let mut env = ligature_eval::environment::EvaluationEnvironment::new();

    // Add some variables to the environment
    env.bind(
        "unused_var".to_string(),
        ligature_eval::value::Value::integer(42, ligature_ast::Span::default()),
    );
    env.bind(
        "used_var".to_string(),
        ligature_eval::value::Value::integer(10, ligature_ast::Span::default()),
    );

    let analysis = optimizer.analyze_captures(&closure_expr, &env);

    println!("   Captured variables: {analysis.captured_vars:?}");
    println!("   Unused captures: {analysis.unused_captures:?}");
    println!("   Free variables: {analysis.free_vars:?}");
    println!(
        "   Optimization opportunities: {}",
        analysis.optimization_opportunities.len()
    );

    for opportunity in &analysis.optimization_opportunities {
        println!("     - {opportunity:?}");
    }
    println!();
}

fn demo_parallel_evaluation() {
    println!("4. Parallel Evaluation");
    println!("   -------------------");

    let config = ParallelEvaluationConfig {
        enabled: true,
        worker_threads: 4,
        work_stealing: true,
        min_complexity: 5,
        adaptive_parallelism: true,
        thread_safe_values: true,
    };

    let mut evaluator = ParallelEvaluator::new(config);

    // Test simple expression (should not be parallelized)
    let simple_expr = parse_expression("42").unwrap();
    let is_parallelizable = evaluator.is_parallelizable(&simple_expr);
    println!(
        "   Simple expression is parallelizable: {}",
        is_parallelizable
    );

    // Test complex expression (should be parallelized)
    let complex_source = r#"
        let x = 1 + 2;
        let y = x * 3;
        let z = y + 4;
        let w = z * 5;
        w + 6
    "#;

    let complex_expr = parse_expression(complex_source).unwrap();
    let is_parallelizable = evaluator.is_parallelizable(&complex_expr);
    println!(
        "   Complex expression is parallelizable: {}",
        is_parallelizable
    );

    // Submit a task for parallel evaluation
    let task_id = evaluator.submit_task(
        complex_expr,
        ligature_eval::environment::EvaluationEnvironment::new(),
    );
    println!("   Submitted task with ID: {}", task_id);

    // Get results
    let results = evaluator.get_results();
    println!("   Retrieved {} results", results.len());
    println!();
}

fn demo_generational_gc() {
    println!("5. Generational Garbage Collection");
    println!("   -------------------------------");

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

    println!("   Allocating 1000 values...");
    let start = Instant::now();

    for i in 0..1000 {
        let value = ligature_eval::value::Value::integer(i, ligature_ast::Span::default());
        gc.allocate(value);
    }

    let allocation_time = start.elapsed();
    println!("   Allocation time: {allocation_time:?}");

    let stats = gc.stats();
    println!("   Minor collections: {}", stats.minor_collections);
    println!("   Major collections: {}", stats.major_collections);
    println!("   Objects promoted: {}", stats.promotions);
    println!("   Objects collected: {}", stats.collected);
    println!("   Total GC time: {}ms", stats.total_gc_time_ms);
    println!();
}

fn demo_integrated_performance() {
    println!("6. Integrated Performance Test");
    println!("   ---------------------------");

    // Create configuration with all optimizations enabled
    let mut config = EvaluatorConfig::default();

    // Enable all advanced optimizations
    config.performance.advanced.advanced_tail_call_detection = true;
    config.performance.advanced.function_inlining = true;
    config.performance.advanced.closure_optimization = true;
    config.performance.parallel.enabled = true;
    config.performance.memory_management.generational_gc = true;

    // Configure cache for better performance
    config.cache.enabled = true;
    config.cache.max_size = 2000;
    config.cache.max_memory_bytes = 2 * 1024 * 1024; // 2MB

    let mut evaluator = Evaluator::with_config(config);

    // Test performance with a complex computation
    let performance_source = r#"
        let fibonacci = \n ->
            if n <= 1 then n
            else fibonacci (n - 1) + fibonacci (n - 2);
        
        let factorial = \n ->
            if n <= 1 then 1
            else n * factorial (n - 1);
        
        let result = fibonacci 15 + factorial 8;
        result
    "#;

    println!("   Running performance test...");
    let start = Instant::now();

    let expr = parse_expression(performance_source).unwrap();
    let result = evaluator.evaluate_expression(&expr);

    let evaluation_time = start.elapsed();

    match result {
        Ok(value) => {
            println!("   Result: {value:?}");
            println!("   Evaluation time: {evaluation_time:?}");

            // Print optimization statistics
            let cache_stats = evaluator.cache_stats();
            println!("   Cache hit rate: {:.2}%", cache_stats.hit_rate() * 100.0);
            println!("   Cache hits: {}", cache_stats.hits);
            println!("   Cache misses: {}", cache_stats.misses);
            println!("   Tail call optimizations: {}", cache_stats.tail_calls);
            println!("   Stack evaluations: {}", cache_stats.stack_evals);
            println!(
                "   Environment pool reuses: {}",
                cache_stats.env_pool_reuses
            );

            let env_stats = evaluator.env_pool_stats();
            println!(
                "   Environment pool: {} available, {} total",
                env_stats.0, env_stats.1
            );

            let value_stats = evaluator.value_pool_stats();
            println!(
                "   Value pool: {} available, {} total",
                value_stats.0, value_stats.1
            );
        }
        Err(e) => {
            println!("   Error: {e:?}");
        }
    }
    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_advanced_optimizations_demo() {
        // Run all demos to ensure they work correctly
        demo_advanced_tail_call_detection();
        demo_function_inlining();
        demo_closure_capture_optimization();
        demo_parallel_evaluation();
        demo_generational_gc();
        demo_integrated_performance();
    }
}
