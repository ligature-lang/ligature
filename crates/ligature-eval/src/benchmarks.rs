//! Benchmarking utilities for the Ligature evaluation engine.

use crate::{Evaluator, MemoryStats, MemoryTracker, CacheStats};
use ligature_ast::{AstError, Span};
use ligature_parser::parse_program;
use std::time::{Duration, Instant};

/// Benchmark results for a specific test.
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub iterations: usize,
    pub total_time: Duration,
    pub average_time: Duration,
    pub min_time: Duration,
    pub max_time: Duration,
    pub memory_usage: Option<MemoryStats>,
    pub throughput: f64, // operations per second
    pub cache_stats: Option<CacheStats>,
}

/// Benchmark suite for Ligature evaluation.
pub struct BenchmarkSuite {
    evaluator: Evaluator,
    memory_tracker: MemoryTracker,
    results: Vec<BenchmarkResult>,
    enable_memory_tracking: bool,
}

impl BenchmarkSuite {
    /// Create a new benchmark suite.
    pub fn new() -> Self {
        Self {
            evaluator: Evaluator::new(),
            memory_tracker: MemoryTracker::new(),
            results: Vec::new(),
            enable_memory_tracking: false,
        }
    }
}

impl Default for BenchmarkSuite {
    fn default() -> Self {
        Self::new()
    }
}

impl BenchmarkSuite {
    /// Create a new benchmark suite with memory tracking enabled.
    pub fn with_memory_tracking() -> Self {
        Self {
            evaluator: Evaluator::new(),
            memory_tracker: MemoryTracker::new(),
            results: Vec::new(),
            enable_memory_tracking: true,
        }
    }

    /// Enable or disable memory tracking.
    pub fn set_memory_tracking(&mut self, enable: bool) {
        self.enable_memory_tracking = enable;
        if enable {
            let _ = self.memory_tracker.set_baseline();
        } else {
            self.memory_tracker.reset();
        }
    }

    /// Run a benchmark with the given name, program, and iterations.
    pub fn run_benchmark(
        &mut self,
        name: &str,
        program: &str,
        iterations: usize,
    ) -> Result<BenchmarkResult, AstError> {
        let mut times = Vec::with_capacity(iterations);

        // Parse the program once
        let parsed_program = parse_program(program)?;

        // Set memory baseline if tracking is enabled
        if self.enable_memory_tracking {
            self.memory_tracker
                .set_baseline()
                .map_err(|e| AstError::ParseError {
                    message: format!("Failed to set memory baseline: {e}"),
                    span: Span::default(),
                })?;
        }

        // Warm up the evaluator
        for _ in 0..10 {
            let _ = self.evaluator.evaluate_program(&parsed_program)?;
        }

        // Run the actual benchmark
        for i in 0..iterations {
            let start = Instant::now();
            let _ = self.evaluator.evaluate_program(&parsed_program)?;
            times.push(start.elapsed());

            // Update memory tracking if enabled (only every 100 iterations to reduce overhead)
            if self.enable_memory_tracking && i % 100 == 0 {
                let _ = self.memory_tracker.get_current_usage();
            }
        }

        let total_time: Duration = times.iter().sum();
        let average_time = total_time / iterations as u32;
        let min_time = times.iter().min().copied().unwrap_or(Duration::ZERO);
        let max_time = times.iter().max().copied().unwrap_or(Duration::ZERO);
        let throughput = iterations as f64 / total_time.as_secs_f64();

        // Get memory usage if tracking is enabled
        let memory_usage = if self.enable_memory_tracking {
            self.memory_tracker
                .get_peak_usage()
                .map_err(|e| AstError::ParseError {
                    message: format!("Failed to get memory usage: {e}"),
                    span: Span::default(),
                })
                .ok()
        } else {
            None
        };

        // Get cache statistics
        let cache_stats = Some(self.evaluator.cache_stats().clone());

        let result = BenchmarkResult {
            name: name.to_string(),
            iterations,
            total_time,
            average_time,
            min_time,
            max_time,
            memory_usage,
            throughput,
            cache_stats,
        };

        self.results.push(result.clone());
        Ok(result)
    }

    /// Run all built-in benchmarks.
    pub fn run_all_benchmarks(&mut self) -> Result<Vec<BenchmarkResult>, AstError> {
        let benchmarks = vec![
            ("simple_arithmetic", SIMPLE_ARITHMETIC, 10000),
            ("function_calls", FUNCTION_CALLS, 5000),
            ("pattern_matching", PATTERN_MATCHING, 3000),
            ("record_operations", RECORD_OPERATIONS, 5000),
            ("union_operations", UNION_OPERATIONS, 3000),
            ("list_operations", LIST_OPERATIONS, 2000),
            ("nested_expressions", NESTED_EXPRESSIONS, 1000),
            ("module_operations", MODULE_OPERATIONS, 1000),
            ("large_records", LARGE_RECORDS, 500),
            ("complex_patterns", COMPLEX_PATTERNS, 500),
            ("performance_stress_test", PERFORMANCE_STRESS_TEST, 100),
        ];

        for (name, program, iterations) in benchmarks {
            println!("Running benchmark: {name}");
            self.run_benchmark(name, program, iterations)?;
        }

        Ok(self.results.clone())
    }

    /// Print a summary of all benchmark results.
    pub fn print_summary(&self) {
        println!("\n=== Ligature Benchmark Results ===\n");

        for result in &self.results {
            println!("{}:", result.name);
            println!("  Iterations: {}", result.iterations);
            println!("  Average time: {:?}", result.average_time);
            println!("  Min time: {:?}", result.min_time);
            println!("  Max time: {:?}", result.max_time);
            println!("  Total time: {:?}", result.total_time);
            println!("  Throughput: {:.2} ops/sec", result.throughput);
            if let Some(memory) = &result.memory_usage {
                println!("  Memory usage: {} bytes (RSS)", memory.rss);
                println!("  Virtual memory: {} bytes", memory.vms);
                if let Some(delta) = memory.delta {
                    println!("  Memory delta: {delta} bytes");
                }
            }
            if let Some(cache_stats) = &result.cache_stats {
                println!("  Cache hits: {}", cache_stats.hits);
                println!("  Cache misses: {}", cache_stats.misses);
                println!("  Cache hit rate: {:.2}%", cache_stats.hit_rate());
                println!("  Cache evictions: {}", cache_stats.evictions);
            }
            println!();
        }

        // Calculate overall statistics
        if !self.results.is_empty() {
            let total_benchmarks = self.results.len();
            let total_time: Duration = self.results.iter().map(|r| r.total_time).sum();
            let avg_time: Duration = total_time / total_benchmarks as u32;
            let avg_throughput: f64 =
                self.results.iter().map(|r| r.throughput).sum::<f64>() / total_benchmarks as f64;

            println!("Overall Statistics:");
            println!("  Total benchmarks: {total_benchmarks}");
            println!("  Total time: {total_time:?}");
            println!("  Average benchmark time: {avg_time:?}");
            println!("  Average throughput: {:.2} ops/sec", avg_throughput);
        }
    }

    /// Export results to CSV format.
    pub fn export_csv(&self, filename: &str) -> std::io::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let mut file = File::create(filename)?;

        // Write header with memory and cache columns if any results have that data
        let has_memory_data = self.results.iter().any(|r| r.memory_usage.is_some());
        let has_cache_data = self.results.iter().any(|r| r.cache_stats.is_some());

        if has_memory_data && has_cache_data {
            writeln!(file, "name,iterations,total_time_ns,avg_time_ns,min_time_ns,max_time_ns,throughput_ops_per_sec,memory_rss_bytes,memory_vms_bytes,memory_delta_bytes,cache_hits,cache_misses,cache_hit_rate,cache_evictions")?;
        } else if has_memory_data {
            writeln!(file, "name,iterations,total_time_ns,avg_time_ns,min_time_ns,max_time_ns,throughput_ops_per_sec,memory_rss_bytes,memory_vms_bytes,memory_delta_bytes")?;
        } else if has_cache_data {
            writeln!(file, "name,iterations,total_time_ns,avg_time_ns,min_time_ns,max_time_ns,throughput_ops_per_sec,cache_hits,cache_misses,cache_hit_rate,cache_evictions")?;
        } else {
            writeln!(
                file,
                "name,iterations,total_time_ns,avg_time_ns,min_time_ns,max_time_ns,throughput_ops_per_sec"
            )?;
        }

        for result in &self.results {
            if has_memory_data && has_cache_data {
                let memory_rss = result.memory_usage.as_ref().map(|m| m.rss).unwrap_or(0);
                let memory_vms = result.memory_usage.as_ref().map(|m| m.vms).unwrap_or(0);
                let memory_delta = result
                    .memory_usage
                    .as_ref()
                    .and_then(|m| m.delta)
                    .unwrap_or(0);
                let cache_hits = result.cache_stats.as_ref().map(|c| c.hits).unwrap_or(0);
                let cache_misses = result.cache_stats.as_ref().map(|c| c.misses).unwrap_or(0);
                let cache_hit_rate = result.cache_stats.as_ref().map(|c| c.hit_rate()).unwrap_or(0.0);
                let cache_evictions = result.cache_stats.as_ref().map(|c| c.evictions).unwrap_or(0);

                writeln!(
                    file,
                    "{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                    result.name,
                    result.iterations,
                    result.total_time.as_nanos(),
                    result.average_time.as_nanos(),
                    result.min_time.as_nanos(),
                    result.max_time.as_nanos(),
                    result.throughput,
                    memory_rss,
                    memory_vms,
                    memory_delta,
                    cache_hits,
                    cache_misses,
                    cache_hit_rate,
                    cache_evictions
                )?;
            } else if has_memory_data {
                let memory_rss = result.memory_usage.as_ref().map(|m| m.rss).unwrap_or(0);
                let memory_vms = result.memory_usage.as_ref().map(|m| m.vms).unwrap_or(0);
                let memory_delta = result
                    .memory_usage
                    .as_ref()
                    .and_then(|m| m.delta)
                    .unwrap_or(0);

                writeln!(
                    file,
                    "{},{},{},{},{},{},{},{},{},{}",
                    result.name,
                    result.iterations,
                    result.total_time.as_nanos(),
                    result.average_time.as_nanos(),
                    result.min_time.as_nanos(),
                    result.max_time.as_nanos(),
                    result.throughput,
                    memory_rss,
                    memory_vms,
                    memory_delta
                )?;
            } else if has_cache_data {
                let cache_hits = result.cache_stats.as_ref().map(|c| c.hits).unwrap_or(0);
                let cache_misses = result.cache_stats.as_ref().map(|c| c.misses).unwrap_or(0);
                let cache_hit_rate = result.cache_stats.as_ref().map(|c| c.hit_rate()).unwrap_or(0.0);
                let cache_evictions = result.cache_stats.as_ref().map(|c| c.evictions).unwrap_or(0);

                writeln!(
                    file,
                    "{},{},{},{},{},{},{},{},{},{},{}",
                    result.name,
                    result.iterations,
                    result.total_time.as_nanos(),
                    result.average_time.as_nanos(),
                    result.min_time.as_nanos(),
                    result.max_time.as_nanos(),
                    result.throughput,
                    cache_hits,
                    cache_misses,
                    cache_hit_rate,
                    cache_evictions
                )?;
            } else {
                writeln!(
                    file,
                    "{},{},{},{},{},{},{}",
                    result.name,
                    result.iterations,
                    result.total_time.as_nanos(),
                    result.average_time.as_nanos(),
                    result.min_time.as_nanos(),
                    result.max_time.as_nanos(),
                    result.throughput
                )?;
            }
        }

        Ok(())
    }
}

// Benchmark programs

const SIMPLE_ARITHMETIC: &str = r#"
let x = 42;
let y = 17;
let z = x + y * 3 - 10;
let result = z / 2 + 5;
"#;

const FUNCTION_CALLS: &str = r#"
let add = \x y -> x + y;
let multiply = \x y -> x * y;
let subtract = \x y -> x - y;

let result1 = add 10 20;
let result2 = multiply result1 3;
let result3 = subtract result2 50;
let final_result = add result3 100;
"#;

const PATTERN_MATCHING: &str = r#"
type Option = Some a | None;

let get_value = \option -> match option of
    Some value => value,
    None => 0;

let test1 = get_value (Some 42);
let test2 = get_value None;
let test3 = get_value (Some 100);
"#;

const RECORD_OPERATIONS: &str = r#"
let user = {
    name = "Alice",
    age = 30,
    email = "alice@example.com"
};

let updated_user = {
    name = user.name,
    age = user.age + 1,
    email = user.email
};

let name = updated_user.name;
let age = updated_user.age;
"#;

const UNION_OPERATIONS: &str = r#"
type Result = Success a | Error String;

let handle_result = \result -> match result of
    Success value => value,
    Error msg => 0;

let test_results = [
    Success 42,
    Error "Something went wrong",
    Success 100,
    Error "Another error"
];

let processed = map handle_result test_results;
"#;

const LIST_OPERATIONS: &str = r#"
let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

let doubled = map (\x -> x * 2) numbers;
let filtered = filter (\x -> x > 5) doubled;
let sum = fold (\acc x -> acc + x) 0 filtered;
"#;

const NESTED_EXPRESSIONS: &str = r#"
let complex_calculation = 
    let x = 10 in
    let y = x * 2 in
    let z = y + 5 in
    let w = z / 3 in
    w * w + x;

let nested_function = \a ->
    let b = a + 1 in
    let c = b * 2 in
    let d = c - 3 in
    d / 4;

let result = nested_function complex_calculation;
"#;

const MODULE_OPERATIONS: &str = r#"
module Math {
    let add = \x y -> x + y;
    let subtract = \x y -> x - y;
    let multiply = \x y -> x * y;
    let divide = \x y -> x / y;
}

let result1 = Math.add 10 20;
let result2 = Math.subtract result1 5;
let result3 = Math.multiply result2 3;
let final_result = Math.divide result3 2;
"#;

const LARGE_RECORDS: &str = r#"
let large_record = {
    field1 = "value1",
    field2 = 42,
    field3 = true,
    field4 = "value4",
    field5 = 100,
    field6 = false,
    field7 = "value7",
    field8 = 200,
    field9 = true,
    field10 = "value10",
    field11 = 300,
    field12 = false,
    field13 = "value13",
    field14 = 400,
    field15 = true,
    field16 = "value16",
    field17 = 500,
    field18 = false,
    field19 = "value19",
    field20 = 600
};

let access_all_fields = 
    large_record.field1 ++ 
    toString large_record.field2 ++ 
    toString large_record.field3 ++ 
    large_record.field4 ++ 
    toString large_record.field5;
"#;

const COMPLEX_PATTERNS: &str = r#"
type Shape = Circle Float | Rectangle Float Float | Triangle Float Float Float;

let area = \shape -> match shape of
    Circle radius => 3.14159 * radius * radius,
    Rectangle width height => width * height,
    Triangle a b c => 
        let s = (a + b + c) / 2 in
        sqrt (s * (s - a) * (s - b) * (s - c));

let shapes = [
    Circle 5.0,
    Rectangle 10.0 20.0,
    Triangle 3.0 4.0 5.0,
    Circle 3.0,
    Rectangle 5.0 15.0
];

let areas = map area shapes;
let total_area = fold (\acc area -> acc + area) 0.0 areas;
"#;

const PERFORMANCE_STRESS_TEST: &str = r#"
// A complex stress test that exercises multiple language features
module PerformanceTest {
    let factorial = \n -> 
        if n <= 1 then 1 else n * factorial (n - 1);
    
    let fibonacci = \n ->
        if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2);
    
    let complex_calculation = \x y z ->
        let a = x * y in
        let b = y * z in
        let c = z * x in
        let sum = a + b + c in
        let product = a * b * c in
        if sum > product then sum else product;
}

let test_data = {
    numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    config = {
        enabled = true,
        threshold = 100,
        timeout = 30
    },
    results = [
        { success = true, value = 42 },
        { success = false, value = 0 },
        { success = true, value = 100 }
    ]
};

let processed_results = map (\result -> 
    if result.success then 
        PerformanceTest.complex_calculation result.value 2 3
    else 
        0
) test_data.results;

let final_result = fold (\acc x -> acc + x) 0 processed_results;
"#;

/// Run a quick performance test.
pub fn quick_performance_test() -> Result<(), AstError> {
    let mut suite = BenchmarkSuite::new();
    let results = suite.run_all_benchmarks()?;

    println!("Quick Performance Test Results:");
    for result in results {
        println!(
            "  {}: {:?} avg ({:.2} ops/sec)",
            result.name, result.average_time, result.throughput
        );
    }

    Ok(())
}

/// Run a quick performance test with memory tracking.
pub fn quick_performance_test_with_memory() -> Result<(), AstError> {
    let mut suite = BenchmarkSuite::with_memory_tracking();
    let results = suite.run_all_benchmarks()?;

    println!("Quick Performance Test Results (with memory tracking):");
    for result in results {
        println!(
            "  {}: {:?} avg ({:.2} ops/sec)",
            result.name, result.average_time, result.throughput
        );
        if let Some(memory) = &result.memory_usage {
            println!("    Memory: {} bytes (RSS)", memory.rss);
        }
    }

    Ok(())
}

/// Run a lightweight performance test for testing purposes.
pub fn lightweight_performance_test_with_memory() -> Result<(), AstError> {
    let mut suite = BenchmarkSuite::with_memory_tracking();

    // Run only a few benchmarks with fewer iterations for testing
    let test_benchmarks = vec![
        ("simple_arithmetic", SIMPLE_ARITHMETIC, 100),
        ("function_calls", FUNCTION_CALLS, 50),
        ("pattern_matching", PATTERN_MATCHING, 30),
    ];

    for (name, program, iterations) in test_benchmarks {
        println!("Running test benchmark: {name}");
        suite.run_benchmark(name, program, iterations)?;
    }

    let results = suite.results.clone();
    println!("Lightweight Performance Test Results (with memory tracking):");
    for result in results {
        println!(
            "  {}: {:?} avg ({:.2} ops/sec)",
            result.name, result.average_time, result.throughput
        );
        if let Some(memory) = &result.memory_usage {
            println!("    Memory: {} bytes (RSS)", memory.rss);
        }
    }

    Ok(())
}

/// Run a comprehensive performance analysis.
pub fn comprehensive_performance_analysis() -> Result<(), AstError> {
    let mut suite = BenchmarkSuite::new();
    let _results = suite.run_all_benchmarks()?;

    suite.print_summary();
    suite
        .export_csv("benchmark_results.csv")
        .map_err(|_| AstError::ParseError {
            message: "Failed to export CSV".to_string(),
            span: ligature_ast::Span::default(),
        })?;

    println!("Results exported to benchmark_results.csv");
    Ok(())
}

/// Run a comprehensive performance analysis with memory tracking.
pub fn comprehensive_performance_analysis_with_memory() -> Result<(), AstError> {
    let mut suite = BenchmarkSuite::with_memory_tracking();
    let _results = suite.run_all_benchmarks()?;

    suite.print_summary();
    suite
        .export_csv("benchmark_results_with_memory.csv")
        .map_err(|_| AstError::ParseError {
            message: "Failed to export CSV".to_string(),
            span: ligature_ast::Span::default(),
        })?;

    println!("Results exported to benchmark_results_with_memory.csv");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_benchmark_suite_creation() {
        let suite = BenchmarkSuite::new();
        assert_eq!(suite.results.len(), 0);
        assert!(!suite.enable_memory_tracking);
    }

    #[test]
    fn test_benchmark_suite_with_memory_tracking() {
        let suite = BenchmarkSuite::with_memory_tracking();
        assert_eq!(suite.results.len(), 0);
        assert!(suite.enable_memory_tracking);
    }

    #[test]
    fn test_simple_benchmark() {
        let mut suite = BenchmarkSuite::new();
        let result = suite.run_benchmark("test", "let x = 42;", 10).unwrap();

        assert_eq!(result.name, "test");
        assert_eq!(result.iterations, 10);
        assert!(result.average_time > Duration::ZERO);
        assert!(result.memory_usage.is_none()); // Memory tracking disabled by default
        assert!(result.throughput > 0.0);
    }

    #[test]
    fn test_benchmark_with_memory_tracking() {
        let mut suite = BenchmarkSuite::with_memory_tracking();
        let result = suite.run_benchmark("test", "let x = 42;", 10).unwrap();

        assert_eq!(result.name, "test");
        assert_eq!(result.iterations, 10);
        assert!(result.average_time > Duration::ZERO);
        assert!(result.memory_usage.is_some()); // Memory tracking enabled

        let memory = result.memory_usage.unwrap();
        assert!(memory.rss > 0);
        assert!(memory.vms > 0);
        assert!(result.throughput > 0.0);
    }

    #[test]
    fn test_memory_tracking_toggle() {
        let mut suite = BenchmarkSuite::new();
        assert!(!suite.enable_memory_tracking);

        suite.set_memory_tracking(true);
        assert!(suite.enable_memory_tracking);

        suite.set_memory_tracking(false);
        assert!(!suite.enable_memory_tracking);
    }

    #[test]
    fn test_quick_performance_test() {
        // Test that performance testing works with a simple benchmark
        let mut suite = BenchmarkSuite::new();
        let result = suite
            .run_benchmark("simple_test", "let x = 42;", 10)
            .unwrap();

        assert_eq!(result.name, "simple_test");
        assert_eq!(result.iterations, 10);
        assert!(result.average_time > Duration::ZERO);
        assert!(result.memory_usage.is_none()); // Memory tracking disabled by default
        assert!(result.throughput > 0.0);
    }

    #[test]
    fn test_quick_performance_test_with_memory() {
        // Test that memory tracking works with a simple benchmark
        let mut suite = BenchmarkSuite::with_memory_tracking();
        let result = suite
            .run_benchmark("simple_test", "let x = 42;", 10)
            .unwrap();

        assert_eq!(result.name, "simple_test");
        assert_eq!(result.iterations, 10);
        assert!(result.average_time > Duration::ZERO);
        assert!(result.memory_usage.is_some()); // Memory tracking enabled

        let memory = result.memory_usage.unwrap();
        assert!(memory.rss > 0);
        assert!(memory.vms > 0);
        assert!(result.throughput > 0.0);
    }
}
