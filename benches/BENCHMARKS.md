# Ligature Benchmark System

A comprehensive benchmark system for measuring and monitoring the performance of the Ligature language parser and evaluator.

## 🚀 Quick Start

```bash
# Run all benchmarks
./benches/run_benchmarks.sh

# Run with custom settings
./benches/run_benchmarks.sh -w 500 -i 5000 -f json

# Run only parser benchmarks
./benches/run_benchmarks.sh -c ligature-parser

# Run custom benchmarks only
./benches/run_benchmarks.sh --custom
```

## 📊 What's Included

### Criterion Benchmarks

- **Parser Benchmarks**: Test parsing performance for all language constructs
- **Evaluator Benchmarks**: Test evaluation performance and memory usage
- **Error Handling**: Benchmark error recovery and reporting
- **Large Expressions**: Stress test with complex inputs

### Custom Benchmark Runner

- **Memory Profiling**: Detailed memory usage tracking
- **Multiple Output Formats**: Human-readable, JSON, and CSV reports
- **Performance Regression Detection**: Automatic regression alerts
- **Configurable Parameters**: Warmup, iterations, timeouts

### Benchmark Scripts

- **Easy Execution**: Simple command-line interface
- **CI/CD Integration**: Ready for automated testing
- **Report Generation**: Automatic report creation
- **Configuration Management**: TOML-based configuration

## 📁 File Structure

```
├── crates/
│   ├── ligature-parser/benches/parser_benchmarks.rs
│   └── ligature-eval/benches/eval_benchmarks.rs
├── benches/
│   ├── run_benchmarks.sh          # Main benchmark runner
│   ├── benchmark_runner.rs        # Custom benchmark engine
│   ├── benchmark_config.toml      # Configuration file
│   └── BENCHMARKS.md              # This file
├── docs/
│   └── benchmarks.md              # Detailed documentation
└── examples/
    └── benchmark_example.lig      # Example expressions
```

## 🎯 Performance Targets

| Component           | Target Throughput | Target Latency | Memory Limit |
| ------------------- | ----------------- | -------------- | ------------ |
| Parser (simple)     | > 10,000 ops/sec  | < 100µs        | < 2MB        |
| Parser (complex)    | > 3,000 ops/sec   | < 300µs        | < 2MB        |
| Evaluator (simple)  | > 8,000 ops/sec   | < 125µs        | < 4MB        |
| Evaluator (complex) | > 2,500 ops/sec   | < 400µs        | < 4MB        |
| End-to-end          | > 2,000 ops/sec   | < 500µs        | < 6MB        |

## 📈 Output Examples

### Human-Readable

```
Benchmark Results:
Name                 Category         Throughput    Avg Time        Memory (KB)
--------------------------------------------------------------------------------
simple_literal       literals         12500.50      80.00µs         1024
arithmetic           arithmetic       8500.25       117.65µs        1536
complex_expression   complex          3200.10       312.50µs        2048
```

### JSON

```json
{
  "name": "simple_literal",
  "category": "literals",
  "throughput": 12500.5,
  "avg_time": "80000",
  "memory_usage": {
    "peak_memory_kb": 1024,
    "memory_increase_kb": 0
  }
}
```

## 🔧 Configuration

The benchmark system is highly configurable through `benchmark_config.toml`:

```toml
[performance]
warmup_iterations = 1000
measurement_iterations = 10000
timeout_seconds = 30

[targets.parser]
simple_throughput = 10000  # ops/sec
complex_throughput = 3000   # ops/sec
```

## 🛠️ Adding New Benchmarks

### Criterion Benchmarks

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

### Custom Benchmarks

```rust
// Add to benches/benchmark_runner.rs
let cases = vec![
    ("new_case", "input", "category"),
];
```

## 🔍 Monitoring & Alerts

- **Performance Regression Detection**: Automatic alerts for performance drops
- **Memory Leak Detection**: Track memory usage patterns
- **Trend Analysis**: Monitor performance over time
- **CI/CD Integration**: Fail builds on regressions

## 📚 Documentation

- **[Detailed Documentation](docs/benchmarks.md)**: Complete guide with examples
- **[Configuration Reference](benchmark_config.toml)**: All available options
- **[Example Expressions](examples/benchmark_example.lig)**: Test cases for benchmarking

## 🤝 Contributing

When adding new features to Ligature:

1. **Add Benchmarks**: Include benchmarks for new language constructs
2. **Update Targets**: Adjust performance targets if needed
3. **Test Regressions**: Ensure changes don't cause performance regressions
4. **Document Changes**: Update benchmark documentation

## 🚨 Troubleshooting

### Common Issues

1. **Benchmarks fail to compile**

   ```bash
   cargo clean
   cargo build
   ```

2. **Memory profiling not working**

   ```bash
   # Check system permissions
   ./benches/run_benchmarks.sh -m -v
   ```

3. **Slow execution**
   ```bash
   # Use development settings
   ./benches/run_benchmarks.sh -w 100 -i 1000
   ```

### Getting Help

- Check the [detailed documentation](docs/benchmarks.md)
- Review [example expressions](examples/benchmark_example.lig)
- Run with verbose output: `./benches/run_benchmarks.sh -v`

## 📊 Continuous Integration

The benchmark system integrates seamlessly with CI/CD:

```yaml
# GitHub Actions example
- name: Run Benchmarks
  run: |
    ./benches/run_benchmarks.sh -f json --no-reports
    # Upload results as artifacts
```

## 🎉 Success Metrics

- **Performance Monitoring**: Track performance trends over time
- **Regression Prevention**: Catch performance issues early
- **Optimization Validation**: Verify optimization effectiveness
- **Quality Assurance**: Ensure consistent performance

---

For detailed information, see [docs/benchmarks.md](docs/benchmarks.md).
