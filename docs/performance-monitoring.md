# Performance Monitoring System

The Ligature Performance Monitoring System provides comprehensive runtime performance metrics collection, adaptive optimization, and performance regression detection to maintain long-term performance excellence.

## Overview

The performance monitoring system consists of three main components:

1. **Runtime Performance Metrics** - Collects detailed performance data during execution
2. **Performance Regression Tests** - Detects performance degradations over time
3. **Adaptive Optimization Engine** - Automatically applies and learns from optimization strategies

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Performance Monitor                      │
├─────────────────────────────────────────────────────────────┤
│  • Metrics Collection    • Expression Profiling            │
│  • Regression Detection  • Optimization Recommendations     │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                 Adaptive Optimizer                          │
├─────────────────────────────────────────────────────────────┤
│  • Strategy Evaluation   • Learning Algorithm              │
│  • Decision Making       • Effectiveness Tracking          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                Performance Regression Tests                 │
├─────────────────────────────────────────────────────────────┤
│  • Baseline Establishment • Regression Detection           │
│  • Optimization Testing   • Report Generation              │
└─────────────────────────────────────────────────────────────┘
```

## Features

### 1. Runtime Performance Metrics

The system collects comprehensive performance metrics for every operation:

- **Execution Time** - Precise timing of expression evaluation
- **Memory Usage** - Memory consumption tracking
- **Cache Performance** - Hit/miss ratios and efficiency
- **Expression Complexity** - Complexity scoring for optimization decisions
- **System Load** - CPU and memory utilization

#### Metrics Collection

```rust
use ligature_eval::performance::{PerformanceMonitor, PerformanceGuard};

let monitor = Arc::new(PerformanceMonitor::new());

// Automatic metrics collection with guard
{
    let mut guard = PerformanceGuard::new(
        monitor.clone(),
        "complex_expression".to_string(),
        50 // complexity score
    );
    
    // Your evaluation code here
    let result = evaluate_expression(&ast);
    
    // Guard automatically records metrics when dropped
}
```

#### Performance Profiles

The system maintains detailed profiles for different expression types:

```rust
let profiles = monitor.get_profiles();
for (expr_type, profile) in profiles {
    println!("{}: avg time={:?}, cache efficiency={:.1}%", 
        expr_type, 
        profile.avg_execution_time,
        profile.cache_efficiency * 100.0
    );
}
```

### 2. Performance Regression Detection

Automatically detects performance degradations with configurable thresholds:

#### Regression Severity Levels

- **Low** - < 10% degradation
- **Medium** - 10-25% degradation  
- **High** - 25-50% degradation
- **Critical** - > 50% degradation

#### Configuration

```rust
use ligature_eval::performance::PerformanceConfig;

let config = PerformanceConfig {
    enable_regression_detection: true,
    regression_threshold: 0.15, // 15% threshold
    metrics_retention_days: 30,
    ..Default::default()
};

let monitor = PerformanceMonitor::with_config(config);
```

#### Regression Alerts

```rust
let alerts = monitor.get_regression_alerts();
for alert in alerts {
    println!("Regression detected in {}: {:?} degradation ({:.1}%)", 
        alert.expression_type,
        alert.severity,
        alert.performance_degradation * 100.0
    );
}
```

### 3. Adaptive Optimization Engine

The adaptive optimizer automatically applies optimization strategies based on performance data:

#### Optimization Strategies

1. **Cache Size Optimization**
   - Increases cache size when hit rates are low
   - Targets 90% hit rate for optimal performance

2. **Expression Caching**
   - Enables caching for complex expressions
   - Uses complexity thresholds to determine when to cache

3. **Memory Allocation Optimization**
   - Optimizes memory allocation patterns
   - Reduces memory pressure and fragmentation

4. **Ineffective Optimization Disabling**
   - Automatically disables strategies that don't improve performance
   - Reduces overhead from ineffective optimizations

#### Learning Algorithm

The optimizer learns from the effectiveness of applied strategies:

```rust
use ligature_eval::adaptive_optimizer::AdaptiveOptimizer;

let optimizer = AdaptiveOptimizer::new(monitor.clone());

// Analyze and apply optimizations
let decisions = optimizer.analyze_and_optimize();

// Learn from results
optimizer.learn_from_results(&before_metrics, &after_metrics);
```

#### Strategy Effectiveness Tracking

```rust
let strategies = optimizer.get_strategies();
for (name, strategy) in strategies {
    println!("{}: {:.1}% effective ({} applications, {} successes)", 
        name,
        strategy.effectiveness_score * 100.0,
        strategy.application_count,
        strategy.success_count
    );
}
```

## CLI Tool Usage

The `ligature-performance-monitor` CLI tool provides easy access to all features:

### Installation

```bash
cargo install --path apps/performance-monitor
```

### Commands

#### Real-time Monitoring

```bash
# Monitor for 60 seconds
ligature-performance-monitor monitor

# Monitor with custom duration and config
ligature-performance-monitor monitor -d 300 -c config.toml
```

#### Performance Regression Testing

```bash
# Run regression tests
ligature-performance-monitor regression-test

# Save results to file
ligature-performance-monitor regression-test -o results.json
```

#### Adaptive Optimization

```bash
# Run optimization for 10 iterations
ligature-performance-monitor optimize

# Run with custom iterations and generate report
ligature-performance-monitor optimize -i 20 -r
```

#### Benchmarking

```bash
# Benchmark a simple expression
ligature-performance-monitor benchmark -e "2 + 3 * 4"

# Benchmark with custom iterations
ligature-performance-monitor benchmark -e "complex_expression" -i 5000

# Save benchmark results
ligature-performance-monitor benchmark -e "test" -o benchmark.json
```

#### Report Generation

```bash
# Generate human-readable report
ligature-performance-monitor report

# Generate JSON report
ligature-performance-monitor report -f json -o report.json

# Generate CSV report
ligature-performance-monitor report -f csv -o report.csv
```

## Configuration

### Performance Monitor Configuration

```toml
# performance_config.toml
[performance]
enable_metrics_collection = true
enable_regression_detection = true
enable_adaptive_optimization = true
metrics_retention_days = 30
regression_threshold = 0.15
cache_size_limit = 1000
memory_usage_limit = 104857600  # 100MB
```

### Adaptive Optimizer Configuration

```toml
# optimizer_config.toml
[optimizer]
enable_learning = true
confidence_threshold = 0.7
improvement_threshold = 0.05
max_strategies_per_cycle = 3
strategy_cooldown_seconds = 300
effectiveness_decay_rate = 0.95
```

## Integration with Existing Code

### Adding Performance Monitoring to Evaluator

```rust
use ligature_eval::performance::{PerformanceMonitor, PerformanceGuard};

pub struct Evaluator {
    performance_monitor: Arc<PerformanceMonitor>,
    // ... other fields
}

impl Evaluator {
    pub fn evaluate_expression(&mut self, expr: &Expr) -> AstResult<Value> {
        let complexity = self.calculate_complexity(expr);
        let mut guard = PerformanceGuard::new(
            self.performance_monitor.clone(),
            expr.get_type_name(),
            complexity
        );
        
        // Record cache hits/misses
        if self.cache.contains(expr) {
            guard.record_cache_hit();
        } else {
            guard.record_cache_miss();
        }
        
        // Perform evaluation
        let result = self.evaluate_internal(expr);
        
        // Guard automatically records metrics when dropped
        result
    }
}
```

### Performance Regression Testing

```rust
use ligature_eval::performance::PerformanceRegressionTests;

#[test]
fn test_performance_regressions() {
    let mut tests = PerformanceRegressionTests::new();
    
    // Establish baselines (run once)
    tests.establish_baselines();
    
    // Run regression tests
    let report = tests.generate_performance_report();
    
    // Assert no critical regressions
    assert_eq!(report.critical_regressions, 0);
    assert_eq!(report.high_regressions, 0);
    
    // Optional: assert minimum performance thresholds
    assert!(report.passed_tests as f64 / report.total_tests as f64 > 0.95);
}
```

## Performance Targets

The system is designed to maintain these performance targets:

| Component | Target Throughput | Target Latency | Memory Limit |
|-----------|------------------|----------------|--------------|
| Simple Expressions | > 10,000 ops/sec | < 100µs | < 2MB |
| Complex Expressions | > 3,000 ops/sec | < 300µs | < 4MB |
| End-to-end | > 2,000 ops/sec | < 500µs | < 6MB |

## Monitoring and Alerting

### Performance Dashboards

The system can export metrics for integration with monitoring systems:

```bash
# Export metrics in Prometheus format
ligature-performance-monitor report -f prometheus -o metrics.prom

# Export for Grafana
ligature-performance-monitor report -f json -o grafana.json
```

### Alerting Rules

Example alerting rules for critical performance issues:

```yaml
# alerting_rules.yml
groups:
  - name: ligature_performance
    rules:
      - alert: CriticalPerformanceRegression
        expr: ligature_regression_severity == "critical"
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Critical performance regression detected"
          
      - alert: HighMemoryUsage
        expr: ligature_memory_usage_percent > 80
        for: 2m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage detected"
```

## Best Practices

### 1. Baseline Establishment

- Establish performance baselines on representative hardware
- Run baseline tests multiple times to account for variance
- Store baselines in version control for regression tracking

### 2. Monitoring Strategy

- Monitor continuously in production environments
- Set up alerts for critical regressions
- Use different thresholds for development vs production

### 3. Optimization Management

- Review optimization decisions regularly
- Manually override ineffective strategies when needed
- Document optimization decisions and their rationale

### 4. Performance Testing

- Include performance tests in CI/CD pipelines
- Run regression tests before releases
- Monitor performance trends over time

## Troubleshooting

### Common Issues

1. **High Memory Usage**
   - Check memory allocation optimization settings
   - Review expression complexity thresholds
   - Consider reducing cache sizes

2. **Poor Cache Performance**
   - Analyze cache hit rates by expression type
   - Adjust cache size optimization thresholds
   - Review expression caching strategies

3. **False Regression Alerts**
   - Increase regression thresholds for noisy environments
   - Use longer baseline periods
   - Filter out known performance variations

4. **Ineffective Optimizations**
   - Review optimization strategy effectiveness scores
   - Check if strategies are being applied too frequently
   - Adjust confidence and improvement thresholds

### Debugging

Enable verbose logging for detailed performance analysis:

```bash
RUST_LOG=debug ligature-performance-monitor monitor -d 60
```

### Performance Profiling

Use the built-in profiler for detailed analysis:

```bash
ligature-performance-monitor benchmark -e "complex_expression" -i 10000 --profile
```

## Future Enhancements

### Planned Features

1. **Machine Learning Integration**
   - Advanced pattern recognition for optimization
   - Predictive performance modeling
   - Automated strategy generation

2. **Distributed Monitoring**
   - Multi-node performance tracking
   - Cluster-wide optimization coordination
   - Cross-service performance correlation

3. **Advanced Analytics**
   - Performance trend analysis
   - Anomaly detection
   - Capacity planning recommendations

4. **Integration APIs**
   - REST API for external monitoring systems
   - WebSocket streaming for real-time dashboards
   - Plugin system for custom metrics

## Contributing

When contributing to the performance monitoring system:

1. **Add Tests** - Include performance tests for new features
2. **Update Baselines** - Re-establish baselines when behavior changes
3. **Document Changes** - Update configuration and usage documentation
4. **Performance Impact** - Ensure changes don't negatively impact performance

### Development Setup

```bash
# Build the performance monitor
cargo build --package ligature-performance-monitor

# Run tests
cargo test --package ligature-performance-monitor

# Run benchmarks
cargo bench --package ligature-eval
```

## Conclusion

The Ligature Performance Monitoring System provides comprehensive tools for maintaining and improving performance over time. By combining runtime metrics collection, intelligent regression detection, and adaptive optimization, it ensures that Ligature applications maintain excellent performance characteristics throughout their lifecycle.

For more information, see the [API documentation](../api/performance-monitoring.md) and [examples](../examples/performance-monitoring/). 