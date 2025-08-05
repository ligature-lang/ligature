# Ligature Benchmark System

This directory contains the benchmark system for measuring and monitoring the performance of the Ligature language parser and evaluator.

## Files

- **`run_benchmarks.sh`** - Main benchmark runner script
- **`benchmark_runner.rs`** - Custom benchmark engine for detailed profiling
- **`benchmark_config.toml`** - Configuration file for benchmark settings
- **`BENCHMARKS.md`** - Comprehensive documentation for the benchmark system

## Quick Start

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

## Crate Benchmarks

The individual crates also have their own benchmark directories:

- `crates/ligature-parser/benches/` - Parser-specific benchmarks
- `crates/ligature-eval/benches/` - Evaluator-specific benchmarks

## Documentation

For detailed information about the benchmark system, see:

- [BENCHMARKS.md](BENCHMARKS.md) - Complete benchmark documentation
- [docs/benchmarks.md](../docs/benchmarks.md) - Technical documentation
