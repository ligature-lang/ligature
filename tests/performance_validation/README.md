# Performance Validation Test Suite

This directory contains the performance validation tests for Ligature's optimization system.

## Overview

The performance validation suite tests the three key performance improvements:

1. **Function Call Performance**: Tests stack-based evaluation and tail call optimization
2. **Arithmetic Operations**: Tests caching and value optimization for arithmetic expressions
3. **Memory Usage**: Tests value interning and pooling optimizations
4. **Cache Effectiveness**: Tests expression caching system

## Running the Tests

```bash
# From the project root
cd tests/performance_validation
cargo run

# Or from the project root
cargo run -p ligature-performance-validation
```

## Test Results

The tests output detailed performance metrics including:

- Operations per second (baseline vs optimized)
- Improvement factors
- Cache hit rates
- Memory usage statistics
- Optimization status (PASS/FAIL)

## Current Status

- ✅ **Cache Effectiveness**: 99.95% hit rate (exceeds target)
- ❌ **Function Call Performance**: 1.6x improvement (target: 100x)
- ❌ **Arithmetic Operations**: 0.5x (regression, target: 6x)
- ❌ **Memory Usage**: 1.1-1.2x improvement (target: 1.5-3x)

## Configuration

The test suite can be configured by modifying the test parameters in `performance_validation.rs`:

- `iterations`: Number of test iterations
- `test_expressions`: Types of expressions to test
- `optimization_flags`: Which optimizations to enable/disable

## Integration

This test suite is integrated into the main workspace and can be run as part of the overall test suite. It provides continuous validation of performance optimizations and helps identify regressions.

## Files

- `performance_validation.rs` - Main test implementation
- `Cargo.toml` - Project configuration
- `README.md` - This documentation
