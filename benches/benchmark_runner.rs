use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::process::Command;
use serde::{Deserialize, Serialize};
use sysinfo::{System, SystemExt, ProcessExt};

/// Benchmark result data structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub name: String,
    pub category: String,
    pub input_size: usize,
    pub iterations: u64,
    pub total_time: Duration,
    pub avg_time: Duration,
    pub throughput: f64, // operations per second
    pub memory_usage: Option<MemoryUsage>,
    pub success: bool,
    pub error_message: Option<String>,
}

/// Memory usage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryUsage {
    pub peak_memory_kb: u64,
    pub final_memory_kb: u64,
    pub memory_increase_kb: u64,
}

/// Benchmark suite configuration
#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    pub warmup_iterations: u64,
    pub measurement_iterations: u64,
    pub timeout_seconds: u64,
    pub memory_profiling: bool,
    pub output_format: OutputFormat,
}

/// Output format for benchmark results
#[derive(Debug, Clone)]
pub enum OutputFormat {
    Json,
    Csv,
    Human,
    All,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            warmup_iterations: 1000,
            measurement_iterations: 10000,
            timeout_seconds: 30,
            memory_profiling: true,
            output_format: OutputFormat::Human,
        }
    }
}

/// Custom benchmark runner
pub struct BenchmarkRunner {
    config: BenchmarkConfig,
    results: Vec<BenchmarkResult>,
}

impl BenchmarkRunner {
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            config,
            results: Vec::new(),
        }
    }

    /// Run benchmarks for a specific crate
    pub fn run_crate_benchmarks(&mut self, crate_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        println!("Running benchmarks for crate: {}", crate_name);
        
        let start_time = Instant::now();
        
        // Run cargo bench for the specific crate
        let output = Command::new("cargo")
            .args(&["bench", "--package", crate_name])
            .output()?;
        
        if !output.status.success() {
            let error = String::from_utf8_lossy(&output.stderr);
            eprintln!("Benchmark failed for {}: {}", crate_name, error);
            return Err(format!("Benchmark failed: {}", error).into());
        }
        
        let duration = start_time.elapsed();
        println!("Benchmarks completed for {} in {:?}", crate_name, duration);
        
        Ok(())
    }

    /// Run custom benchmarks with detailed profiling
    pub fn run_custom_benchmarks(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Running custom benchmarks...");
        
        // Parser benchmarks
        self.run_parser_benchmarks()?;
        
        // Evaluator benchmarks
        self.run_evaluator_benchmarks()?;
        
        // End-to-end benchmarks
        self.run_end_to_end_benchmarks()?;
        
        self.generate_report()?;
        
        Ok(())
    }

    /// Run parser-specific benchmarks
    fn run_parser_benchmarks(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Running parser benchmarks...");
        
        let parser_cases = vec![
            ("simple_literal", "42", "literals"),
            ("arithmetic", "1 + 2 * 3", "arithmetic"),
            ("complex_expression", "let x = { a: 1, b: [2, 3] } in x.a + x.b[0]", "complex"),
        ];
        
        for (name, input, category) in parser_cases {
            self.run_single_benchmark(name, input, category, "parser")?;
        }
        
        Ok(())
    }

    /// Run evaluator-specific benchmarks
    fn run_evaluator_benchmarks(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Running evaluator benchmarks...");
        
        let eval_cases = vec![
            ("simple_eval", "1 + 2", "arithmetic"),
            ("conditional_eval", "if true then 1 else 2", "conditional"),
            ("record_eval", "let r = { x: 1, y: 2 } in r.x + r.y", "record"),
        ];
        
        for (name, input, category) in eval_cases {
            self.run_single_benchmark(name, input, category, "evaluator")?;
        }
        
        Ok(())
    }

    /// Run end-to-end benchmarks
    fn run_end_to_end_benchmarks(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Running end-to-end benchmarks...");
        
        let e2e_cases = vec![
            ("config_parsing", "let config = { port: 8080, debug: true } in config.port", "config"),
            ("complex_config", "let env = \"production\" in if env == \"production\" then { port: 443 } else { port: 3000 }", "config"),
        ];
        
        for (name, input, category) in e2e_cases {
            self.run_single_benchmark(name, input, category, "end_to_end")?;
        }
        
        Ok(())
    }

    /// Run a single benchmark with detailed profiling
    fn run_single_benchmark(
        &mut self,
        name: &str,
        input: &str,
        category: &str,
        benchmark_type: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut sys = System::new_all();
        let start_memory = sys.used_memory();
        
        let start_time = Instant::now();
        let mut peak_memory = start_memory;
        
        // Warmup phase
        for _ in 0..self.config.warmup_iterations {
            self.execute_benchmark_operation(input, benchmark_type)?;
            
            // Update memory usage
            sys.refresh_memory();
            peak_memory = peak_memory.max(sys.used_memory());
        }
        
        // Measurement phase
        let measurement_start = Instant::now();
        for _ in 0..self.config.measurement_iterations {
            self.execute_benchmark_operation(input, benchmark_type)?;
            
            // Update memory usage
            sys.refresh_memory();
            peak_memory = peak_memory.max(sys.used_memory());
        }
        
        let total_time = measurement_start.elapsed();
        let avg_time = total_time / self.config.measurement_iterations;
        let throughput = self.config.measurement_iterations as f64 / total_time.as_secs_f64();
        
        let final_memory = sys.used_memory();
        let memory_usage = if self.config.memory_profiling {
            Some(MemoryUsage {
                peak_memory_kb: peak_memory,
                final_memory_kb: final_memory,
                memory_increase_kb: final_memory.saturating_sub(start_memory),
            })
        } else {
            None
        };
        
        let result = BenchmarkResult {
            name: name.to_string(),
            category: category.to_string(),
            input_size: input.len(),
            iterations: self.config.measurement_iterations,
            total_time,
            avg_time,
            throughput,
            memory_usage,
            success: true,
            error_message: None,
        };
        
        self.results.push(result);
        
        println!("  ✓ {}: {:.2} ops/sec, avg: {:?}", name, throughput, avg_time);
        
        Ok(())
    }

    /// Execute a benchmark operation (placeholder for actual implementation)
    fn execute_benchmark_operation(&self, input: &str, benchmark_type: &str) -> Result<(), Box<dyn std::error::Error>> {
        // This would be replaced with actual benchmark execution
        // For now, we'll simulate some work
        match benchmark_type {
            "parser" => {
                // Simulate parsing
                std::thread::sleep(Duration::from_micros(100));
            }
            "evaluator" => {
                // Simulate evaluation
                std::thread::sleep(Duration::from_micros(200));
            }
            "end_to_end" => {
                // Simulate end-to-end processing
                std::thread::sleep(Duration::from_micros(300));
            }
            _ => {
                std::thread::sleep(Duration::from_micros(150));
            }
        }
        
        Ok(())
    }

    /// Generate benchmark report
    fn generate_report(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n=== Benchmark Report ===");
        
        match self.config.output_format {
            OutputFormat::Json => self.generate_json_report()?,
            OutputFormat::Csv => self.generate_csv_report()?,
            OutputFormat::Human => self.generate_human_report()?,
            OutputFormat::All => {
                self.generate_human_report()?;
                self.generate_json_report()?;
                self.generate_csv_report()?;
            }
        }
        
        Ok(())
    }

    /// Generate human-readable report
    fn generate_human_report(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("\nBenchmark Results:");
        println!("{:<20} {:<15} {:<12} {:<15} {:<15}", "Name", "Category", "Throughput", "Avg Time", "Memory (KB)");
        println!("{:-<80}", "");
        
        for result in &self.results {
            let memory_str = if let Some(mem) = &result.memory_usage {
                format!("{}", mem.peak_memory_kb)
            } else {
                "N/A".to_string()
            };
            
            println!(
                "{:<20} {:<15} {:<12.2} {:<15?} {:<15}",
                result.name,
                result.category,
                result.throughput,
                result.avg_time,
                memory_str
            );
        }
        
        // Summary statistics
        self.print_summary_statistics();
        
        Ok(())
    }

    /// Generate JSON report
    fn generate_json_report(&self) -> Result<(), Box<dyn std::error::Error>> {
        let json = serde_json::to_string_pretty(&self.results)?;
        std::fs::write("benchmark_results.json", json)?;
        println!("JSON report saved to benchmark_results.json");
        Ok(())
    }

    /// Generate CSV report
    fn generate_csv_report(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut csv = String::new();
        csv.push_str("name,category,input_size,iterations,total_time_ns,avg_time_ns,throughput,peak_memory_kb,final_memory_kb,memory_increase_kb,success\n");
        
        for result in &self.results {
            let memory_data = if let Some(mem) = &result.memory_usage {
                format!("{},{},{}", mem.peak_memory_kb, mem.final_memory_kb, mem.memory_increase_kb)
            } else {
                "N/A,N/A,N/A".to_string()
            };
            
            csv.push_str(&format!(
                "{},{},{},{},{},{},{},{},{}\n",
                result.name,
                result.category,
                result.input_size,
                result.iterations,
                result.total_time.as_nanos(),
                result.avg_time.as_nanos(),
                result.throughput,
                memory_data,
                result.success
            ));
        }
        
        std::fs::write("benchmark_results.csv", csv)?;
        println!("CSV report saved to benchmark_results.csv");
        Ok(())
    }

    /// Print summary statistics
    fn print_summary_statistics(&self) {
        println!("\nSummary Statistics:");
        
        // Group by category
        let mut category_stats: HashMap<String, Vec<&BenchmarkResult>> = HashMap::new();
        for result in &self.results {
            category_stats.entry(result.category.clone()).or_default().push(result);
        }
        
        for (category, results) in category_stats {
            let avg_throughput: f64 = results.iter().map(|r| r.throughput).sum::<f64>() / results.len() as f64;
            let avg_time: Duration = results.iter().map(|r| r.avg_time).sum::<Duration>() / results.len() as u32;
            
            println!("  {}: avg throughput = {:.2} ops/sec, avg time = {:?}", category, avg_throughput, avg_time);
        }
    }
}

/// Main function for running benchmarks
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        warmup_iterations: 100,
        measurement_iterations: 1000,
        timeout_seconds: 30,
        memory_profiling: true,
        output_format: OutputFormat::All,
    };
    
    let mut runner = BenchmarkRunner::new(config);
    
    // Run custom benchmarks
    runner.run_custom_benchmarks()?;
    
    // Run crate benchmarks
    runner.run_crate_benchmarks("ligature-parser")?;
    runner.run_crate_benchmarks("ligature-eval")?;
    
    Ok(())
} 