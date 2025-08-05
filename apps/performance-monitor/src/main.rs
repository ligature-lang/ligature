//! Performance monitoring CLI tool for the Ligature language.
//!
//! This tool provides comprehensive performance monitoring, regression testing,
//! and adaptive optimization management.

use clap::{App, Arg, SubCommand};
use ligature_eval::evaluate_program;
use ligature_eval::{
    AdaptiveOptimizer, AdaptiveOptimizerConfig, PerformanceConfig, PerformanceMonitor,
    PerformanceReport,
};
use ligature_parser::parse_program;
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let matches = App::new("ligature-performance-monitor")
        .version("1.0")
        .about("Performance monitoring and optimization tool for Ligature")
        .subcommand(
            SubCommand::with_name("monitor")
                .about("Monitor performance in real-time")
                .arg(
                    Arg::with_name("config")
                        .short('c')
                        .long("config")
                        .value_name("FILE")
                        .help("Configuration file path")
                        .takes_value(true),
                )
                .arg(
                    Arg::with_name("duration")
                        .short('d')
                        .long("duration")
                        .value_name("SECONDS")
                        .help("Monitoring duration in seconds")
                        .takes_value(true)
                        .default_value("60"),
                ),
        )
        .subcommand(
            SubCommand::with_name("regression-test")
                .about("Run performance regression tests")
                .arg(
                    Arg::with_name("baseline")
                        .short('b')
                        .long("baseline")
                        .value_name("FILE")
                        .help("Baseline performance file")
                        .takes_value(true),
                )
                .arg(
                    Arg::with_name("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .help("Output report file")
                        .takes_value(true),
                ),
        )
        .subcommand(
            SubCommand::with_name("optimize")
                .about("Run adaptive optimization")
                .arg(
                    Arg::with_name("iterations")
                        .short('i')
                        .long("iterations")
                        .value_name("COUNT")
                        .help("Number of optimization iterations")
                        .takes_value(true)
                        .default_value("10"),
                )
                .arg(
                    Arg::with_name("report")
                        .short('r')
                        .long("report")
                        .help("Generate optimization report"),
                ),
        )
        .subcommand(
            SubCommand::with_name("benchmark")
                .about("Run performance benchmarks")
                .arg(
                    Arg::with_name("expression")
                        .short('e')
                        .long("expression")
                        .value_name("EXPR")
                        .help("Expression to benchmark")
                        .takes_value(true),
                )
                .arg(
                    Arg::with_name("iterations")
                        .short('i')
                        .long("iterations")
                        .value_name("COUNT")
                        .help("Number of iterations")
                        .takes_value(true)
                        .default_value("1000"),
                )
                .arg(
                    Arg::with_name("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .help("Output file for results"),
                ),
        )
        .subcommand(
            SubCommand::with_name("report")
                .about("Generate performance report")
                .arg(
                    Arg::with_name("input")
                        .short('i')
                        .long("input")
                        .value_name("FILE")
                        .help("Input metrics file")
                        .takes_value(true),
                )
                .arg(
                    Arg::with_name("output")
                        .short('o')
                        .long("output")
                        .value_name("FILE")
                        .help("Output report file")
                        .takes_value(true),
                )
                .arg(
                    Arg::with_name("format")
                        .short('f')
                        .long("format")
                        .value_name("FORMAT")
                        .help("Output format (json, csv, human)")
                        .takes_value(true)
                        .default_value("human"),
                ),
        )
        .get_matches();

    match matches.subcommand() {
        Some(("monitor", args)) => {
            run_monitoring(args).await?;
        }
        Some(("regression-test", args)) => {
            run_regression_tests(args).await?;
        }
        Some(("optimize", args)) => {
            run_optimization(args).await?;
        }
        Some(("benchmark", args)) => {
            run_benchmark(args).await?;
        }
        Some(("report", args)) => {
            generate_report(args).await?;
        }
        _ => {
            println!("Use --help for usage information");
        }
    }

    Ok(())
}

/// Run real-time performance monitoring
async fn run_monitoring(args: &clap::ArgMatches) -> Result<(), Box<dyn std::error::Error>> {
    println!("Starting performance monitoring...");

    let config = if let Some(config_path) = args.value_of("config") {
        load_config(config_path)?
    } else {
        PerformanceConfig::default()
    };

    let duration_seconds: u64 = args.value_of("duration").unwrap().parse()?;
    let duration = Duration::from_secs(duration_seconds);

    let monitor = PerformanceMonitor::with_config(config);
    let start_time = std::time::Instant::now();

    println!("Monitoring for {} seconds...", duration_seconds);
    println!("Press Ctrl+C to stop early");

    // Set up signal handling for graceful shutdown
    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel();
    let ctrl_c = tokio::signal::ctrl_c();

    tokio::select! {
        _ = async {
            loop {
                tokio::time::sleep(Duration::from_secs(1)).await;

                // Simulate some performance metrics
                let metrics = ligature_eval::PerformanceMetrics {
                    operation_name: "monitoring_sample".to_string(),
                    execution_time: Duration::from_millis(rand::random::<u64>() % 100 + 10),
                    memory_usage_bytes: rand::random::<usize>() % 10000 + 1000,
                    cache_hits: rand::random::<u64>() % 10,
                    cache_misses: rand::random::<u64>() % 5,
                    expression_complexity: rand::random::<usize>() % 50 + 10,
                    timestamp: std::time::SystemTime::now(),
                };

                monitor.record_metrics(metrics);

                if start_time.elapsed() >= duration {
                    break;
                }
            }
            let _ = shutdown_tx.send(());
        } => {}

        _ = ctrl_c => {
            println!("\nReceived interrupt signal, stopping...");
        }
    }

    // Wait for shutdown
    let _ = shutdown_rx.await;

    // Generate final report
    let report = monitor.generate_report();
    report.print_summary();

    println!("Monitoring completed.");
    Ok(())
}

/// Run performance regression tests
async fn run_regression_tests(args: &clap::ArgMatches) -> Result<(), Box<dyn std::error::Error>> {
    println!("Running performance regression tests...");

    // Import the regression test module
    use crate::performance_regression_tests::PerformanceRegressionTests;

    let mut tests = PerformanceRegressionTests::new();

    // Establish baselines
    tests.establish_baselines();

    // Run regression tests
    let report = tests.generate_performance_report();
    report.print_summary();

    // Save results if output file specified
    if let Some(output_path) = args.value_of("output") {
        let output_path = PathBuf::from(output_path);
        save_regression_report(&report, &output_path)?;
        println!("Regression report saved to: {:?}", output_path);
    }

    Ok(())
}

/// Run adaptive optimization
async fn run_optimization(args: &clap::ArgMatches) -> Result<(), Box<dyn std::error::Error>> {
    println!("Running adaptive optimization...");

    let iterations: usize = args.value_of("iterations").unwrap().parse()?;
    let generate_report = args.is_present("report");

    let config = AdaptiveOptimizerConfig::default();
    let monitor = std::sync::Arc::new(PerformanceMonitor::new());
    let mut optimizer = AdaptiveOptimizer::with_config(monitor.clone(), config);

    for i in 0..iterations {
        println!("Optimization iteration {}/{}", i + 1, iterations);

        // Generate some test performance data
        for j in 0..10 {
            let metrics = ligature_eval::PerformanceMetrics {
                operation_name: format!("test_op_{}", j),
                execution_time: Duration::from_millis(rand::random::<u64>() % 200 + 50),
                memory_usage_bytes: rand::random::<usize>() % 20000 + 5000,
                cache_hits: rand::random::<u64>() % 15,
                cache_misses: rand::random::<u64>() % 10,
                expression_complexity: rand::random::<usize>() % 100 + 20,
                timestamp: std::time::SystemTime::now(),
            };
            monitor.record_metrics(metrics);
        }

        // Run optimization analysis
        let decisions = optimizer.analyze_and_optimize();

        if !decisions.is_empty() {
            println!("Applied {} optimizations:", decisions.len());
            for decision in &decisions {
                println!(
                    "  - {} (confidence: {:.1}%, expected improvement: {:.1}%)",
                    decision.strategy_name,
                    decision.confidence * 100.0,
                    decision.expected_improvement * 100.0
                );
            }
        } else {
            println!("No optimizations applied");
        }

        // Simulate learning from results
        let before_metrics = monitor.get_metrics();
        tokio::time::sleep(Duration::from_millis(100)).await;
        let after_metrics = monitor.get_metrics();
        optimizer.learn_from_results(&before_metrics, &after_metrics);

        tokio::time::sleep(Duration::from_millis(500)).await;
    }

    if generate_report {
        let report = optimizer.generate_optimization_report();
        report.print_summary();
    }

    println!("Optimization completed.");
    Ok(())
}

/// Run performance benchmarks
async fn run_benchmark(args: &clap::ArgMatches) -> Result<(), Box<dyn std::error::Error>> {
    let expression = args.value_of("expression").unwrap_or("42");
    let iterations: usize = args.value_of("iterations").unwrap().parse()?;

    println!("Running benchmark for expression: {}", expression);
    println!("Iterations: {}", iterations);

    // Parse the expression
    let ast = parse_program(expression)?;

    let monitor = PerformanceMonitor::new();
    let start_time = std::time::Instant::now();

    let mut total_time = Duration::ZERO;
    let mut successful_runs = 0;
    let mut failed_runs = 0;

    for i in 0..iterations {
        let iteration_start = std::time::Instant::now();

        match evaluate_program(&ast) {
            Ok(_) => {
                let iteration_time = iteration_start.elapsed();
                total_time += iteration_time;
                successful_runs += 1;

                // Record metrics
                let metrics = ligature_eval::PerformanceMetrics {
                    operation_name: "benchmark".to_string(),
                    execution_time: iteration_time,
                    memory_usage_bytes: expression.len() * 64, // Rough estimate
                    cache_hits: 1,
                    cache_misses: 0,
                    expression_complexity: expression.len(),
                    timestamp: std::time::SystemTime::now(),
                };
                monitor.record_metrics(metrics);
            }
            Err(e) => {
                failed_runs += 1;
                if i == 0 {
                    eprintln!("Evaluation error: {:?}", e);
                }
            }
        }

        // Progress indicator
        if (i + 1) % 100 == 0 {
            print!(".");
            std::io::stdout().flush()?;
        }
    }

    let total_duration = start_time.elapsed();
    let avg_time = if successful_runs > 0 {
        total_time / successful_runs as u32
    } else {
        Duration::ZERO
    };

    println!("\n\nBenchmark Results:");
    println!("Expression: {}", expression);
    println!("Total iterations: {}", iterations);
    println!("Successful runs: {}", successful_runs);
    println!("Failed runs: {}", failed_runs);
    println!(
        "Success rate: {:.1}%",
        (successful_runs as f64 / iterations as f64) * 100.0
    );
    println!("Total time: {:?}", total_duration);
    println!("Average execution time: {:?}", avg_time);
    println!(
        "Throughput: {:.0} ops/sec",
        if avg_time.as_nanos() > 0 {
            1_000_000_000.0 / avg_time.as_nanos() as f64
        } else {
            0.0
        }
    );

    // Generate detailed report
    let report = monitor.generate_report();
    report.print_summary();

    // Save results if output file specified
    if let Some(output_path) = args.value_of("output") {
        let output_path = PathBuf::from(output_path);
        save_benchmark_results(&report, &output_path)?;
        println!("Benchmark results saved to: {:?}", output_path);
    }

    Ok(())
}

/// Generate performance report
async fn generate_report(args: &clap::ArgMatches) -> Result<(), Box<dyn std::error::Error>> {
    let format = args.value_of("format").unwrap();

    if let Some(input_path) = args.value_of("input") {
        // Load metrics from file and generate report
        let monitor = load_metrics_from_file(input_path)?;
        let report = monitor.generate_report();

        if let Some(output_path) = args.value_of("output") {
            save_report(&report, output_path, format)?;
            println!("Report saved to: {}", output_path);
        } else {
            report.print_summary();
        }
    } else {
        // Generate report from current monitoring session
        let monitor = PerformanceMonitor::new();
        let report = monitor.generate_report();

        if let Some(output_path) = args.value_of("output") {
            save_report(&report, output_path, format)?;
            println!("Report saved to: {}", output_path);
        } else {
            report.print_summary();
        }
    }

    Ok(())
}

// Helper functions

fn load_config(_path: &str) -> Result<PerformanceConfig, Box<dyn std::error::Error>> {
    // In a real implementation, this would load from a file
    // For now, return default config
    Ok(PerformanceConfig::default())
}

fn save_regression_report(
    report: &crate::performance_regression_tests::PerformanceRegressionReport,
    path: &PathBuf,
) -> Result<(), Box<dyn std::error::Error>> {
    let json = serde_json::to_string_pretty(report)?;
    std::fs::write(path, json)?;
    Ok(())
}

fn save_benchmark_results(
    report: &PerformanceReport,
    path: &PathBuf,
) -> Result<(), Box<dyn std::error::Error>> {
    let json = serde_json::to_string_pretty(report)?;
    std::fs::write(path, json)?;
    Ok(())
}

fn save_report(
    report: &PerformanceReport,
    path: &str,
    format: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let content = match format {
        "json" => serde_json::to_string_pretty(report)?,
        "csv" => convert_to_csv(report)?,
        "human" => {
            report.print_summary();
            String::new() // Human format is printed to stdout
        }
        _ => return Err("Unsupported format".into()),
    };

    if !content.is_empty() {
        std::fs::write(path, content)?;
    }

    Ok(())
}

fn convert_to_csv(report: &PerformanceReport) -> Result<String, Box<dyn std::error::Error>> {
    let mut csv = String::new();
    csv.push_str("metric,value\n");
    csv.push_str(&format!("total_operations,{}\n", report.total_operations));
    csv.push_str(&format!(
        "avg_execution_time_nanos,{}\n",
        report.avg_execution_time.as_nanos()
    ));
    csv.push_str(&format!(
        "avg_memory_usage_bytes,{}\n",
        report.avg_memory_usage
    ));
    csv.push_str(&format!("cache_efficiency,{}\n", report.cache_efficiency));
    Ok(csv)
}

fn load_metrics_from_file(_path: &str) -> Result<PerformanceMonitor, Box<dyn std::error::Error>> {
    // In a real implementation, this would load metrics from a file
    // For now, return a new monitor
    Ok(PerformanceMonitor::new())
}

// Include the performance regression tests module
mod performance_regression_tests {
    include!("../../../tests/performance_regression_tests.rs");
}
