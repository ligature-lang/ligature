# Benchmark System

The Ligature project includes a comprehensive benchmark system for measuring performance of the parser and evaluator components.

## Overview

The benchmark system consists of:

1. **Criterion-based benchmarks** - Standard Rust benchmarks using the Criterion crate
2. **Custom benchmark runner** - Programmatic benchmark execution with detailed profiling
3. **Benchmark scripts** - Shell scripts for easy execution and reporting
4. **Memory profiling** - Detailed memory usage tracking
5. **Multiple output formats** - Human-readable, JSON, and CSV reports

## Quick Start

### Running All Benchmarks

```bash
# Run all benchmarks with default settings
./benches/run_benchmarks.sh

# Run with verbose output
./benches/run_benchmarks.sh -v

# Run only parser benchmarks
./benches/run_benchmarks.sh -c ligature-parser

# Run with custom iteration counts
./benches/run_benchmarks.sh -w 500 -i 5000
```

### Running Individual Crate Benchmarks

```bash
# Run parser benchmarks
cargo bench --package ligature-parser

# Run evaluator benchmarks
cargo bench --package ligature-eval

# Run with specific benchmark
cargo bench --package ligature-parser -- parser
```

## Benchmark Categories

### Parser Benchmarks

The parser benchmarks test various aspects of the Ligature parser:

- **Literals**: Integer, float, string, and boolean literals
- **Arithmetic**: Simple and complex arithmetic expressions
- **Comparison**: Comparison operators and compound comparisons
- **Logical**: Logical operators and short-circuit evaluation
- **Let expressions**: Simple and nested let bindings
- **Function calls**: Simple and nested function calls
- **Records**: Simple and nested record construction
- **Lists**: Simple and nested list construction
- **Complex expressions**: Real-world configuration expressions
- **Error handling**: Malformed input and syntax errors
- **Large expressions**: Stress testing with large inputs
- **Memory usage**: Memory allocation patterns

### Evaluator Benchmarks

The evaluator benchmarks test the evaluation engine:

- **Literals**: Direct value evaluation
- **Arithmetic**: Mathematical operations
- **Comparison**: Comparison operations
- **Logical**: Boolean operations with short-circuiting
- **Let expressions**: Variable binding and scoping
- **Conditional expressions**: If-then-else evaluation
- **Records**: Record construction and field access
- **Lists**: List construction and indexing
- **Complex expressions**: Multi-step evaluation
- **Error handling**: Runtime errors and type mismatches
- **End-to-end**: Complete parse-and-evaluate workflows

## Configuration Options

### Command Line Options

| Option             | Description                           | Default                         |
| ------------------ | ------------------------------------- | ------------------------------- |
| `-c, --crates`     | Comma-separated list of crates        | `ligature-parser,ligature-eval` |
| `-f, --format`     | Output format (human, json, csv, all) | `human`                         |
| `-m, --memory`     | Enable memory profiling               | `true`                          |
| `-w, --warmup`     | Number of warmup iterations           | `1000`                          |
| `-i, --iterations` | Number of measurement iterations      | `10000`                         |
| `-t, --timeout`    | Timeout in seconds                    | `30`                            |
| `-v, --verbose`    | Enable verbose output                 | `false`                         |
| `--custom`         | Run custom benchmarks only            | `false`                         |
| `--no-reports`     | Don't generate reports                | `false`                         |

### Environment Variables

| Variable                           | Description                    | Default                         |
| ---------------------------------- | ------------------------------ | ------------------------------- |
| `BENCHMARK_CRATES`                 | Space-separated list of crates | `ligature-parser ligature-eval` |
| `BENCHMARK_OUTPUT_FORMAT`          | Output format                  | `human`                         |
| `BENCHMARK_MEMORY_PROFILING`       | Enable memory profiling        | `true`                          |
| `BENCHMARK_WARMUP_ITERATIONS`      | Warmup iterations              | `1000`                          |
| `BENCHMARK_MEASUREMENT_ITERATIONS` | Measurement iterations         | `10000`                         |

## Output Formats

### Human-Readable Output

```
Benchmark Results:
Name                 Category         Throughput    Avg Time        Memory (KB)
--------------------------------------------------------------------------------
simple_literal       literals         12500.50      80.00µs         1024
arithmetic           arithmetic       8500.25       117.65µs        1536
complex_expression   complex          3200.10       312.50µs        2048

Summary Statistics:
  literals: avg throughput = 12500.50 ops/sec, avg time = 80.00µs
  arithmetic: avg throughput = 8500.25 ops/sec, avg time = 117.65µs
  complex: avg throughput = 3200.10 ops/sec, avg time = 312.50µs
```

### JSON Output

```json
[
  {
    "name": "simple_literal",
    "category": "literals",
    "input_size": 2,
    "iterations": 10000,
    "total_time": "800000000",
    "avg_time": "80000",
    "throughput": 12500.5,
    "memory_usage": {
      "peak_memory_kb": 1024,
      "final_memory_kb": 1024,
      "memory_increase_kb": 0
    },
    "success": true,
    "error_message": null
  }
]
```

### CSV Output

```csv
name,category,input_size,iterations,total_time_ns,avg_time_ns,throughput,peak_memory_kb,final_memory_kb,memory_increase_kb,success
simple_literal,literals,2,10000,800000000,80000,12500.5,1024,1024,0,true
arithmetic,arithmetic,7,10000,1176500000,117650,8500.25,1536,1536,0,true
```

## Benchmark Results

### Performance Targets

| Component           | Target Throughput | Target Latency |
| ------------------- | ----------------- | -------------- |
| Parser (simple)     | > 10,000 ops/sec  | < 100µs        |
| Parser (complex)    | > 3,000 ops/sec   | < 300µs        |
| Evaluator (simple)  | > 8,000 ops/sec   | < 125µs        |
| Evaluator (complex) | > 2,500 ops/sec   | < 400µs        |
| End-to-end          | > 2,000 ops/sec   | < 500µs        |

### Memory Usage Targets

| Component  | Peak Memory | Memory Increase |
| ---------- | ----------- | --------------- |
| Parser     | < 2MB       | < 1MB           |
| Evaluator  | < 4MB       | < 2MB           |
| End-to-end | < 6MB       | < 3MB           |

## Adding New Benchmarks

### Adding Criterion Benchmarks

1. Create a new benchmark file in the appropriate crate:

```rust
// crates/ligature-parser/benches/new_benchmarks.rs
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_new_feature(c: &mut Criterion) {
    c.bench_function("new_feature", |b| {
        b.iter(|| {
            // Your benchmark code here
        });
    });
}

criterion_group!(benches, bench_new_feature);
criterion_main!(benches);
```

2. Add the benchmark to the crate's `Cargo.toml`:

```toml
[[bench]]
name = "new_benchmarks"
harness = false
```

### Adding Custom Benchmarks

1. Add benchmark cases to the appropriate benchmark function in `benches/benchmark_runner.rs`:

```rust
fn run_new_benchmarks(&mut self) -> Result<(), Box<dyn std::error::Error>> {
    let cases = vec![
        ("new_case_1", "input_1", "category_1"),
        ("new_case_2", "input_2", "category_2"),
    ];

    for (name, input, category) in cases {
        self.run_single_benchmark(name, input, category, "new_type")?;
    }

    Ok(())
}
```

2. Call the new benchmark function in `run_custom_benchmarks()`.

## Continuous Integration

The benchmark system integrates with CI/CD pipelines:

### GitHub Actions

```yaml
- name: Run Benchmarks
  run: |
    ./benches/run_benchmarks.sh -f json --no-reports
    # Upload results as artifacts
```

### Performance Regression Detection

The system can detect performance regressions:

```bash
# Compare against baseline
./benches/run_benchmarks.sh --compare-baseline baseline.json

# Generate regression report
./benches/run_benchmarks.sh --regression-report
```

## Troubleshooting

### Common Issues

1. **Benchmarks fail to compile**

   - Ensure all dependencies are available
   - Check that criterion is in dev-dependencies
   - Verify benchmark file syntax

2. **Memory profiling not working**

   - Ensure sysinfo crate is available
   - Check system permissions for memory access
   - Verify memory profiling is enabled

3. **Slow benchmark execution**

   - Reduce iteration counts for development
   - Use `--custom` flag for faster execution
   - Check system resources

4. **Inconsistent results**
   - Ensure system is not under load
   - Use consistent hardware for comparisons
   - Check for thermal throttling

### Debug Mode

Enable debug output for troubleshooting:

```bash
# Enable verbose output
./benches/run_benchmarks.sh -v

# Run with debug logging
RUST_LOG=debug ./benches/run_benchmarks.sh

# Run single benchmark for debugging
cargo bench --package ligature-parser -- parser --verbose
```

## Best Practices

### Writing Benchmarks

1. **Use realistic inputs** - Test with real-world data sizes and patterns
2. **Test edge cases** - Include error conditions and boundary cases
3. **Measure what matters** - Focus on user-visible performance
4. **Keep benchmarks fast** - Use appropriate iteration counts
5. **Document assumptions** - Explain benchmark setup and expectations

### Interpreting Results

1. **Look for trends** - Focus on relative performance changes
2. **Consider variance** - Account for measurement noise
3. **Check memory usage** - Monitor for memory leaks
4. **Validate correctness** - Ensure benchmarks test correct behavior
5. **Compare apples to apples** - Use consistent hardware and conditions

### Performance Optimization

1. **Profile first** - Use profiling tools to identify bottlenecks
2. **Measure impact** - Verify that optimizations improve performance
3. **Test regressions** - Ensure optimizations don't break functionality
4. **Document changes** - Record optimization rationale and impact
5. **Monitor over time** - Track performance trends across releases

## Contributing

When contributing to the benchmark system:

1. **Add tests** - Include benchmarks for new features
2. **Update documentation** - Document new benchmark categories
3. **Maintain consistency** - Follow existing patterns and conventions
4. **Validate results** - Ensure benchmarks produce meaningful data
5. **Review performance** - Consider performance impact of changes

## References

- [Criterion Documentation](https://bheisler.github.io/criterion.rs/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Benchmarking Best Practices](https://github.com/sharkdp/hyperfine#benchmarking-best-practices)
