//! Performance Monitoring Example
//! 
//! This example demonstrates the complete performance monitoring system,
//! including metrics collection, regression detection, and adaptive optimization.

use std::sync::Arc;
use std::time::Duration;
use ligature_eval::{
    PerformanceMonitor, PerformanceConfig, AdaptiveOptimizer, AdaptiveOptimizerConfig,
    PerformanceGuard, PerformanceMetrics
};
use ligature_parser::parse_program;
use ligature_eval::evaluate_program;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Performance Monitoring Example ===\n");

    // 1. Basic Performance Monitoring
    println!("1. Setting up performance monitoring...");
    let config = PerformanceConfig {
        enable_metrics_collection: true,
        enable_regression_detection: true,
        enable_adaptive_optimization: true,
        regression_threshold: 0.1, // 10% threshold
        ..Default::default()
    };

    let monitor = Arc::new(PerformanceMonitor::with_config(config));
    println!("✓ Performance monitor initialized\n");

    // 2. Collecting Performance Metrics
    println!("2. Collecting performance metrics...");
    collect_sample_metrics(&monitor);
    println!("✓ Sample metrics collected\n");

    // 3. Performance Regression Detection
    println!("3. Testing regression detection...");
    test_regression_detection(&monitor);
    println!("✓ Regression detection tested\n");

    // 4. Adaptive Optimization
    println!("4. Testing adaptive optimization...");
    test_adaptive_optimization(&monitor);
    println!("✓ Adaptive optimization tested\n");

    // 5. Generate Performance Report
    println!("5. Generating performance report...");
    let report = monitor.generate_report();
    report.print_summary();
    println!("✓ Performance report generated\n");

    // 6. Real-world Expression Benchmarking
    println!("6. Benchmarking real expressions...");
    benchmark_expressions(&monitor);
    println!("✓ Expression benchmarking completed\n");

    println!("=== Example completed successfully! ===");
    Ok(())
}

/// Collect sample performance metrics
fn collect_sample_metrics(monitor: &Arc<PerformanceMonitor>) {
    let expressions = vec![
        "42",
        "2 + 3 * 4",
        "let x = 5 in x + 3",
        "if true then 1 else 2",
        "{x: 1, y: 2}",
        "[1, 2, 3, 4, 5]",
    ];

    for (i, expr) in expressions.iter().enumerate() {
        println!("  Benchmarking: {}", expr);
        
        // Parse the expression
        let ast = match parse_program(expr) {
            Ok(ast) => ast,
            Err(e) => {
                println!("    Error parsing: {e:?}");
                continue;
            }
        };

        // Use performance guard for automatic metrics collection
        {
            let mut guard = PerformanceGuard::new(
                monitor.clone(),
                format!("expression_{}", i),
                expr.len() // Use expression length as complexity
            );

            // Record some cache activity
            if i % 2 == 0 {
                guard.record_cache_hit();
            } else {
                guard.record_cache_miss();
            }

            // Evaluate the expression
            match evaluate_program(&ast) {
                Ok(result) => {
                    println!("    Result: {result:?}");
                }
                Err(e) => {
                    println!("    Evaluation error: {e:?}");
                }
            }
            // Guard automatically records metrics when dropped
        }
    }
}

/// Test regression detection by simulating performance degradation
fn test_regression_detection(monitor: &Arc<PerformanceMonitor>) {
    println!("  Simulating performance regression...");

    // Record baseline metrics (good performance)
    for i in 0..10 {
        let metrics = PerformanceMetrics {
            operation_name: "regression_test".to_string(),
            execution_time: Duration::from_millis(100), // Good performance
            memory_usage_bytes: 1024,
            cache_hits: 8,
            cache_misses: 2,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };
        monitor.record_metrics(metrics);
    }

    // Record degraded metrics (poor performance)
    for i in 0..10 {
        let metrics = PerformanceMetrics {
            operation_name: "regression_test".to_string(),
            execution_time: Duration::from_millis(200), // 100% degradation
            memory_usage_bytes: 2048,
            cache_hits: 4,
            cache_misses: 6,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };
        monitor.record_metrics(metrics);
    }

    // Check for regression alerts
    let alerts = monitor.get_regression_alerts();
    if !alerts.is_empty() {
        println!("  ✓ Regression detected:");
        for alert in &alerts {
            println!("    - {}: {:?} degradation ({:.1}%)", 
                alert.expression_type,
                alert.severity,
                alert.performance_degradation * 100.0
            );
        }
    } else {
        println!("  ✓ No regressions detected");
    }
}

/// Test adaptive optimization
fn test_adaptive_optimization(monitor: &Arc<PerformanceMonitor>) {
    println!("  Setting up adaptive optimizer...");
    
    let config = AdaptiveOptimizerConfig {
        enable_learning: true,
        confidence_threshold: 0.6, // Lower threshold for testing
        improvement_threshold: 0.02, // Lower threshold for testing
        max_strategies_per_cycle: 2,
        strategy_cooldown_seconds: 1, // Short cooldown for testing
        effectiveness_decay_rate: 0.95,
    };

    let mut optimizer = AdaptiveOptimizer::with_config(monitor.clone(), config);

    // Generate some performance data for optimization analysis
    for i in 0..20 {
        let metrics = PerformanceMetrics {
            operation_name: format!("optimization_test_{}", i % 5),
            execution_time: Duration::from_millis(50 + (i * 10) as u64),
            memory_usage_bytes: 1000 + (i * 100),
            cache_hits: if i % 3 == 0 { 5 } else { 2 },
            cache_misses: if i % 3 == 0 { 1 } else { 8 },
            expression_complexity: 20 + (i * 5),
            timestamp: std::time::SystemTime::now(),
        };
        monitor.record_metrics(metrics);
    }

    // Run optimization analysis
    println!("  Running optimization analysis...");
    let decisions = optimizer.analyze_and_optimize();

    if !decisions.is_empty() {
        println!("  ✓ Optimization decisions made:");
        for decision in &decisions {
            println!("    - {}: {:.1}% confidence, {:.1}% expected improvement", 
                decision.strategy_name,
                decision.confidence * 100.0,
                decision.expected_improvement * 100.0
            );
            println!("      Reasoning: {}", decision.reasoning);
        }
    } else {
        println!("  ✓ No optimizations recommended");
    }

    // Simulate learning from results
    let before_metrics = monitor.get_metrics();
    std::thread::sleep(Duration::from_millis(100));
    let after_metrics = monitor.get_metrics();
    optimizer.learn_from_results(&before_metrics, &after_metrics);

    // Generate optimization report
    let report = optimizer.generate_optimization_report();
    println!("  Optimization report:");
    println!("    - Total strategies: {}", report.total_strategies);
    println!("    - Enabled strategies: {}", report.enabled_strategies);
    println!("    - Success rate: {:.1}%", report.success_rate * 100.0);
    println!("    - Average effectiveness: {:.1}%", report.average_effectiveness * 100.0);
}

/// Benchmark various expression types
fn benchmark_expressions(monitor: &Arc<PerformanceMonitor>) {
    let test_cases = vec![
        ("simple_literal", "42", 1000),
        ("arithmetic", "2 + 3 * 4 - 5 / 2", 500),
        ("let_expression", "let x = 5 in let y = x + 3 in y * 2", 300),
        ("conditional", "if 5 > 3 then 10 else 20", 800),
        ("record", "{x: 1, y: 2, z: 3}", 600),
        ("list", "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]", 400),
    ];

    for (name, expression, iterations) in test_cases {
        println!("  Benchmarking {} ({} iterations):", name, iterations);
        
        let ast = match parse_program(expression) {
            Ok(ast) => ast,
            Err(e) => {
                println!("    Error parsing: {e:?}");
                continue;
            }
        };

        let start_time = std::time::Instant::now();
        let mut total_time = Duration::ZERO;
        let mut successful_runs = 0;

        for i in 0..iterations {
            let iteration_start = std::time::Instant::now();
            
            match evaluate_program(&ast) {
                Ok(_) => {
                    let iteration_time = iteration_start.elapsed();
                    total_time += iteration_time;
                    successful_runs += 1;

                    // Record metrics every 100th iteration to avoid overwhelming
                    if i % 100 == 0 {
                        let metrics = PerformanceMetrics {
                            operation_name: name.to_string(),
                            execution_time: iteration_time,
                            memory_usage_bytes: expression.len() * 64,
                            cache_hits: 1,
                            cache_misses: 0,
                            expression_complexity: expression.len(),
                            timestamp: std::time::SystemTime::now(),
                        };
                        monitor.record_metrics(metrics);
                    }
                }
                Err(e) => {
                    if i == 0 {
                        println!("    Evaluation error: {e:?}");
                    }
                }
            }
        }

        let total_duration = start_time.elapsed();
        let avg_time = if successful_runs > 0 {
            total_time / successful_runs as u32
        } else {
            Duration::ZERO
        };

        let throughput = if avg_time.as_nanos() > 0 {
            1_000_000_000.0 / avg_time.as_nanos() as f64
        } else {
            0.0
        };

        println!("    - Success rate: {:.1}%", (successful_runs as f64 / iterations as f64) * 100.0);
        println!("    - Average time: {avg_time:?}");
        println!("    - Throughput: {:.0} ops/sec", throughput);
        println!("    - Total time: {total_duration:?}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_monitoring_example() {
        let monitor = Arc::new(PerformanceMonitor::new());
        
        // Test metrics collection
        collect_sample_metrics(&monitor);
        let metrics = monitor.get_metrics();
        assert!(!metrics.is_empty());

        // Test regression detection
        test_regression_detection(&monitor);
        let alerts = monitor.get_regression_alerts();
        assert!(!alerts.is_empty()); // Should detect the simulated regression

        // Test adaptive optimization
        test_adaptive_optimization(&monitor);
        let optimizer = AdaptiveOptimizer::new(monitor.clone());
        let strategies = optimizer.get_strategies();
        assert!(!strategies.is_empty());
    }

    #[test]
    fn test_benchmarking() {
        let monitor = Arc::new(PerformanceMonitor::new());
        benchmark_expressions(&monitor);
        
        let report = monitor.generate_report();
        assert!(report.total_operations > 0);
    }
} 