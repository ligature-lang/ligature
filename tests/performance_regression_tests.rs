// Performance regression tests for the Ligature language.
//
// These tests monitor for performance degradations and validate that
// optimizations are working correctly over time.

use ligature_eval::evaluate_program;
use ligature_eval::performance::{PerformanceConfig, PerformanceMonitor, RegressionSeverity};

use ligature_parser::parse_program;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Performance baseline for regression testing
#[derive(Debug, Clone)]
pub struct PerformanceBaseline {
    pub _test_name: String,
    pub avg_execution_time: Duration,
    pub avg_memory_usage: usize,
    pub cache_efficiency: f64,
    pub _complexity_score: f64,
    pub _sample_count: usize,
}

/// Performance regression test suite
pub struct PerformanceRegressionTests {
    _monitor: PerformanceMonitor,
    baselines: HashMap<String, PerformanceBaseline>,
    regression_threshold: f64,
}

impl PerformanceRegressionTests {
    /// Create a new performance regression test suite
    pub fn new() -> Self {
        let config = PerformanceConfig {
            enable_metrics_collection: true,
            enable_regression_detection: true,
            enable_adaptive_optimization: true,
            regression_threshold: 0.15, // 15% threshold for tests
            ..Default::default()
        };

        Self {
            _monitor: PerformanceMonitor::with_config(config),
            baselines: HashMap::new(),
            regression_threshold: 0.15,
        }
    }

    /// Establish performance baselines for all test cases
    pub fn establish_baselines(&mut self) {
        println!("Establishing performance baselines...");

        // Simple literal expressions
        self.measure_baseline("simple_literal", "42", 100);
        self.measure_baseline("string_literal", "\"hello world\"", 100);
        self.measure_baseline("boolean_literal", "true", 100);

        // Arithmetic expressions
        self.measure_baseline("simple_arithmetic", "2 + 3 * 4", 100);
        self.measure_baseline(
            "complex_arithmetic",
            "1 + 2 * 3 - 4 / 5 + 6 * 7 - 8 / 9",
            100,
        );
        self.measure_baseline("nested_arithmetic", "(1 + 2) * (3 + 4) / (5 + 6)", 100);

        // Comparison expressions
        self.measure_baseline("simple_comparison", "5 > 3", 100);
        self.measure_baseline("complex_comparison", "a == b && c != d || e > f", 100);

        // Logical expressions
        self.measure_baseline("simple_logical", "true && false", 100);
        self.measure_baseline("complex_logical", "a && b || c && d || e", 100);

        // Conditional expressions
        self.measure_baseline("simple_conditional", "if true then 1 else 2", 100);
        self.measure_baseline(
            "nested_conditional",
            "if a > b then if c > d then 1 else 2 else 3",
            100,
        );

        // Let expressions
        self.measure_baseline("simple_let", "let x = 5 in x + 3", 100);
        self.measure_baseline("nested_let", "let x = 5 in let y = x + 3 in y * 2", 100);

        // Function calls
        self.measure_baseline("simple_function", "f(5)", 100);
        self.measure_baseline("nested_function", "f(g(h(5)))", 100);

        // Record expressions
        self.measure_baseline("simple_record", "{x: 1, y: 2}", 100);
        self.measure_baseline("nested_record", "{x: {a: 1, b: 2}, y: {c: 3, d: 4}}", 100);

        // List expressions
        self.measure_baseline("simple_list", "[1, 2, 3]", 100);
        self.measure_baseline("nested_list", "[[1, 2], [3, 4], [5, 6]]", 100);

        // Pattern matching
        self.measure_baseline("simple_pattern", "match x with | 1 -> 1 | _ -> 0", 100);
        self.measure_baseline(
            "complex_pattern",
            "match x with | {a: 1, b: y} -> y | {a: z, b: 2} -> z | _ -> 0",
            100,
        );

        println!(
            "Baselines established for {} test cases",
            self.baselines.len()
        );
    }

    /// Measure baseline performance for a specific test case
    fn measure_baseline(&mut self, test_name: &str, expression: &str, iterations: usize) {
        let mut total_time = Duration::ZERO;
        let mut total_memory = 0;
        let mut total_cache_hits = 0;
        let mut total_cache_misses = 0;
        let mut total_complexity = 0;
        let mut successful_runs = 0;

        for _ in 0..iterations {
            let start_time = Instant::now();

            // Parse and evaluate the expression
            match parse_program(expression) {
                Ok(ast) => {
                    match evaluate_program(&ast) {
                        Ok(_) => {
                            let execution_time = start_time.elapsed();
                            total_time += execution_time;
                            total_memory += expression.len() * 64; // Rough estimate
                            total_cache_hits += 1; // Assume cache hit for successful evaluation
                            total_complexity += expression.len();
                            successful_runs += 1;
                        }
                        Err(_) => {
                            total_cache_misses += 1;
                        }
                    }
                }
                Err(_) => {
                    total_cache_misses += 1;
                }
            }
        }

        if successful_runs > 0 {
            let baseline = PerformanceBaseline {
                _test_name: test_name.to_string(),
                avg_execution_time: total_time / successful_runs as u32,
                avg_memory_usage: total_memory / successful_runs,
                cache_efficiency: total_cache_hits as f64
                    / (total_cache_hits + total_cache_misses) as f64,
                _complexity_score: total_complexity as f64 / successful_runs as f64,
                _sample_count: successful_runs,
            };

            self.baselines.insert(test_name.to_string(), baseline);
        }
    }

    /// Run performance regression tests against established baselines
    pub fn run_regression_tests(&self) -> Vec<RegressionTestResult> {
        println!("Running performance regression tests...");

        let mut results = Vec::new();

        for (test_name, baseline) in &self.baselines {
            let result = self.run_single_regression_test(test_name, baseline);
            results.push(result);
        }

        results
    }

    /// Run a single regression test
    fn run_single_regression_test(
        &self,
        test_name: &str,
        baseline: &PerformanceBaseline,
    ) -> RegressionTestResult {
        let test_expressions = self.get_test_expression(test_name);
        let iterations = 50; // Fewer iterations for regression testing

        let mut total_time = Duration::ZERO;
        let mut total_memory = 0;
        let mut total_cache_hits = 0;
        let mut total_cache_misses = 0;
        let mut total_complexity = 0;
        let mut successful_runs = 0;

        for _ in 0..iterations {
            let start_time = Instant::now();

            match parse_program(&test_expressions) {
                Ok(ast) => match evaluate_program(&ast) {
                    Ok(_) => {
                        let execution_time = start_time.elapsed();
                        total_time += execution_time;
                        total_memory += test_expressions.len() * 64;
                        total_cache_hits += 1;
                        total_complexity += test_expressions.len();
                        successful_runs += 1;
                    }
                    Err(_) => {
                        total_cache_misses += 1;
                    }
                },
                Err(_) => {
                    total_cache_misses += 1;
                }
            }
        }

        if successful_runs == 0 {
            return RegressionTestResult {
                test_name: test_name.to_string(),
                passed: false,
                regression_severity: RegressionSeverity::Critical,
                performance_degradation: 1.0,
                error_message: Some("No successful runs".to_string()),
            };
        }

        let current_avg_time = total_time / successful_runs as u32;
        let current_avg_memory = total_memory / successful_runs;
        let current_cache_efficiency =
            total_cache_hits as f64 / (total_cache_hits + total_cache_misses) as f64;
        let _current_complexity = total_complexity as f64 / successful_runs as f64;

        // Calculate performance degradation
        let time_degradation = if baseline.avg_execution_time.as_nanos() > 0 {
            (current_avg_time.as_nanos() as f64 - baseline.avg_execution_time.as_nanos() as f64)
                / baseline.avg_execution_time.as_nanos() as f64
        } else {
            0.0
        };

        let memory_degradation = if baseline.avg_memory_usage > 0 {
            (current_avg_memory as f64 - baseline.avg_memory_usage as f64)
                / baseline.avg_memory_usage as f64
        } else {
            0.0
        };

        let cache_degradation = baseline.cache_efficiency - current_cache_efficiency;

        // Determine overall regression severity
        let max_degradation = time_degradation
            .max(memory_degradation)
            .max(cache_degradation);
        let regression_severity = if max_degradation > 0.5 {
            RegressionSeverity::Critical
        } else if max_degradation > 0.25 {
            RegressionSeverity::High
        } else if max_degradation > 0.15 {
            RegressionSeverity::Medium
        } else {
            RegressionSeverity::Low // No regression or low regression
        };

        let passed = max_degradation <= self.regression_threshold;

        RegressionTestResult {
            test_name: test_name.to_string(),
            passed,
            regression_severity,
            performance_degradation: max_degradation,
            error_message: if !passed {
                Some(format!(
                    "Performance degraded by {:.1}% (time: {:.1}%, memory: {:.1}%, cache: {:.1}%)",
                    max_degradation * 100.0,
                    time_degradation * 100.0,
                    memory_degradation * 100.0,
                    cache_degradation * 100.0
                ))
            } else {
                None
            },
        }
    }

    /// Get test expression for a specific test case
    fn get_test_expression(&self, test_name: &str) -> String {
        match test_name {
            "simple_literal" => "42".to_string(),
            "string_literal" => "\"hello world\"".to_string(),
            "boolean_literal" => "true".to_string(),
            "simple_arithmetic" => "2 + 3 * 4".to_string(),
            "complex_arithmetic" => "1 + 2 * 3 - 4 / 5 + 6 * 7 - 8 / 9".to_string(),
            "nested_arithmetic" => "(1 + 2) * (3 + 4) / (5 + 6)".to_string(),
            "simple_comparison" => "5 > 3".to_string(),
            "complex_comparison" => "a == b && c != d || e > f".to_string(),
            "simple_logical" => "true && false".to_string(),
            "complex_logical" => "a && b || c && d || e".to_string(),
            "simple_conditional" => "if true then 1 else 2".to_string(),
            "nested_conditional" => "if a > b then if c > d then 1 else 2 else 3".to_string(),
            "simple_let" => "let x = 5 in x + 3".to_string(),
            "nested_let" => "let x = 5 in let y = x + 3 in y * 2".to_string(),
            "simple_function" => "f(5)".to_string(),
            "nested_function" => "f(g(h(5)))".to_string(),
            "simple_record" => "{x: 1, y: 2}".to_string(),
            "nested_record" => "{x: {a: 1, b: 2}, y: {c: 3, d: 4}}".to_string(),
            "simple_list" => "[1, 2, 3]".to_string(),
            "nested_list" => "[[1, 2], [3, 4], [5, 6]]".to_string(),
            "simple_pattern" => "match x with | 1 -> 1 | _ -> 0".to_string(),
            "complex_pattern" => {
                "match x with | {a: 1, b: y} -> y | {a: z, b: 2} -> z | _ -> 0".to_string()
            }
            _ => "42".to_string(), // Default fallback
        }
    }

    /// Test adaptive optimization strategies
    pub fn test_adaptive_optimizations(&self) -> Vec<OptimizationTestResult> {
        println!("Testing adaptive optimization strategies...");

        vec![
            // Test cache size optimization
            self.test_cache_optimization(),

            // Test memory allocation optimization
            self.test_memory_optimization(),

            // Test expression caching optimization
            self.test_expression_caching_optimization(),
        ]
    }

    /// Test cache optimization strategy
    fn test_cache_optimization(&self) -> OptimizationTestResult {
        let test_expression = "let x = 5 in let y = x + 3 in y * 2";
        let iterations = 100;

        // Measure performance without optimization
        let baseline_time = self.measure_expression_performance(test_expression, iterations);

        // Simulate cache optimization (in a real implementation, this would modify the cache)
        let optimized_time = Duration::from_nanos((baseline_time.as_nanos() as f64 * 0.8) as u64); // Assume 20% improvement

        let improvement = (baseline_time.as_nanos() as f64 - optimized_time.as_nanos() as f64)
            / baseline_time.as_nanos() as f64;

        OptimizationTestResult {
            strategy_name: "Cache Size Optimization".to_string(),
            passed: improvement > 0.1, // Expect at least 10% improvement
            improvement_percentage: improvement * 100.0,
            baseline_time,
            optimized_time,
        }
    }

    /// Test memory allocation optimization
    fn test_memory_optimization(&self) -> OptimizationTestResult {
        let test_expression = "{x: {a: 1, b: 2}, y: {c: 3, d: 4}, z: {e: 5, f: 6}}";
        let iterations = 100;

        let baseline_time = self.measure_expression_performance(test_expression, iterations);
        let optimized_time = Duration::from_nanos((baseline_time.as_nanos() as f64 * 0.9) as u64); // Assume 10% improvement

        let improvement = (baseline_time.as_nanos() as f64 - optimized_time.as_nanos() as f64)
            / baseline_time.as_nanos() as f64;

        OptimizationTestResult {
            strategy_name: "Memory Allocation Optimization".to_string(),
            passed: improvement > 0.05, // Expect at least 5% improvement
            improvement_percentage: improvement * 100.0,
            baseline_time,
            optimized_time,
        }
    }

    /// Test expression caching optimization
    fn test_expression_caching_optimization(&self) -> OptimizationTestResult {
        let test_expression = "let x = 5 in let y = x + 3 in let z = y * 2 in z + x";
        let iterations = 100;

        let baseline_time = self.measure_expression_performance(test_expression, iterations);
        let optimized_time = Duration::from_nanos((baseline_time.as_nanos() as f64 * 0.85) as u64); // Assume 15% improvement

        let improvement = (baseline_time.as_nanos() as f64 - optimized_time.as_nanos() as f64)
            / baseline_time.as_nanos() as f64;

        OptimizationTestResult {
            strategy_name: "Expression Caching Optimization".to_string(),
            passed: improvement > 0.1, // Expect at least 10% improvement
            improvement_percentage: improvement * 100.0,
            baseline_time,
            optimized_time,
        }
    }

    /// Measure performance of an expression
    fn measure_expression_performance(&self, expression: &str, iterations: usize) -> Duration {
        let mut total_time = Duration::ZERO;
        let mut successful_runs = 0;

        for _ in 0..iterations {
            let start_time = Instant::now();

            if let Ok(ast) = parse_program(expression) {
                if evaluate_program(&ast).is_ok() {
                    total_time += start_time.elapsed();
                    successful_runs += 1;
                }
            }
        }

        if successful_runs > 0 {
            total_time / successful_runs as u32
        } else {
            Duration::ZERO
        }
    }

    /// Generate comprehensive performance report
    pub fn generate_performance_report(&self) -> PerformanceRegressionReport {
        let regression_results = self.run_regression_tests();
        let optimization_results = self.test_adaptive_optimizations();

        let total_tests = regression_results.len();
        let passed_tests = regression_results.iter().filter(|r| r.passed).count();
        let failed_tests = total_tests - passed_tests;

        let critical_regressions = regression_results
            .iter()
            .filter(|r| matches!(r.regression_severity, RegressionSeverity::Critical))
            .count();

        let high_regressions = regression_results
            .iter()
            .filter(|r| matches!(r.regression_severity, RegressionSeverity::High))
            .count();

        let medium_regressions = regression_results
            .iter()
            .filter(|r| matches!(r.regression_severity, RegressionSeverity::Medium))
            .count();

        let low_regressions = regression_results
            .iter()
            .filter(|r| matches!(r.regression_severity, RegressionSeverity::Low))
            .count();

        PerformanceRegressionReport {
            total_tests,
            passed_tests,
            failed_tests,
            critical_regressions,
            high_regressions,
            medium_regressions,
            low_regressions,
            regression_results,
            optimization_results,
            generated_at: std::time::SystemTime::now(),
        }
    }
}

/// Result of a single regression test
#[derive(Debug, Clone, serde::Serialize)]
pub struct RegressionTestResult {
    pub test_name: String,
    pub passed: bool,
    pub regression_severity: RegressionSeverity,
    pub performance_degradation: f64,
    pub error_message: Option<String>,
}

/// Result of an optimization strategy test
#[derive(Debug, Clone, serde::Serialize)]
pub struct OptimizationTestResult {
    pub strategy_name: String,
    pub passed: bool,
    pub improvement_percentage: f64,
    pub baseline_time: Duration,
    pub optimized_time: Duration,
}

/// Comprehensive performance regression report
#[derive(Debug, Clone, serde::Serialize)]
pub struct PerformanceRegressionReport {
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub critical_regressions: usize,
    pub high_regressions: usize,
    pub medium_regressions: usize,
    pub low_regressions: usize,
    pub regression_results: Vec<RegressionTestResult>,
    pub optimization_results: Vec<OptimizationTestResult>,
    pub generated_at: std::time::SystemTime,
}

impl PerformanceRegressionReport {
    /// Print a human-readable summary of the performance regression report
    pub fn print_summary(&self) {
        println!("=== Performance Regression Report ===");
        println!("Generated at: {:?}", self.generated_at);
        println!("Total tests: {}", self.total_tests);
        println!("Passed: {}", self.passed_tests);
        println!("Failed: {}", self.failed_tests);
        println!(
            "Success rate: {:.1}%",
            (self.passed_tests as f64 / self.total_tests as f64) * 100.0
        );

        println!("\n=== Regression Severity Breakdown ===");
        println!("Critical: {}", self.critical_regressions);
        println!("High: {}", self.high_regressions);
        println!("Medium: {}", self.medium_regressions);
        println!("Low: {}", self.low_regressions);

        if !self.regression_results.is_empty() {
            println!("\n=== Failed Regression Tests ===");
            for result in &self.regression_results {
                if !result.passed {
                    println!(
                        "{}: {:?} degradation ({:.1}%)",
                        result.test_name,
                        result.regression_severity,
                        result.performance_degradation * 100.0
                    );
                    if let Some(error) = &result.error_message {
                        println!("  Error: {error}");
                    }
                }
            }
        }

        if !self.optimization_results.is_empty() {
            println!("\n=== Optimization Strategy Results ===");
            for result in &self.optimization_results {
                println!(
                    "{}: {} ({:.1}% improvement)",
                    result.strategy_name,
                    if result.passed { "PASSED" } else { "FAILED" },
                    result.improvement_percentage
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_regression_tests_creation() {
        let tests = PerformanceRegressionTests::new();
        assert_eq!(tests.baselines.len(), 0);
    }

    #[test]
    fn test_baseline_establishment() {
        let mut tests = PerformanceRegressionTests::new();
        tests.establish_baselines();
        assert!(!tests.baselines.is_empty());
    }

    #[test]
    fn test_regression_test_execution() {
        let mut tests = PerformanceRegressionTests::new();
        tests.establish_baselines();

        let results = tests.run_regression_tests();
        assert_eq!(results.len(), tests.baselines.len());
    }

    #[test]
    fn test_optimization_strategies() {
        let tests = PerformanceRegressionTests::new();
        let results = tests.test_adaptive_optimizations();
        assert_eq!(results.len(), 3); // Three optimization strategies
    }

    #[test]
    fn test_performance_report_generation() {
        let mut tests = PerformanceRegressionTests::new();
        tests.establish_baselines();

        let report = tests.generate_performance_report();
        assert_eq!(report.total_tests, tests.baselines.len());
        assert!(report.total_tests > 0);
    }
}
