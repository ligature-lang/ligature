//! Performance monitoring and adaptive optimization for the Ligature evaluator.
//!
//! This module provides runtime performance metrics collection, adaptive optimization
//! strategies, and performance regression detection to maintain long-term performance.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Performance metrics for a single operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub operation_name: String,
    pub execution_time: Duration,
    pub memory_usage_bytes: usize,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub expression_complexity: usize,
    pub timestamp: std::time::SystemTime,
}

/// Performance profile for a specific expression type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpressionProfile {
    pub expression_type: String,
    pub avg_execution_time: Duration,
    pub avg_memory_usage: usize,
    pub cache_efficiency: f64,
    pub complexity_score: f64,
    pub sample_count: usize,
    pub last_updated: std::time::SystemTime,
}

/// Performance regression detection
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegressionAlert {
    pub expression_type: String,
    pub severity: RegressionSeverity,
    pub old_performance: ExpressionProfile,
    pub new_performance: ExpressionProfile,
    pub performance_degradation: f64,
    pub timestamp: std::time::SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RegressionSeverity {
    Low,      // < 10% degradation
    Medium,   // 10-25% degradation
    High,     // 25-50% degradation
    Critical, // > 50% degradation
}

/// Adaptive optimization strategies
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OptimizationStrategy {
    /// Increase cache size for frequently accessed expressions
    IncreaseCacheSize { target_hit_rate: f64 },
    /// Enable expression caching for complex expressions
    EnableExpressionCaching { complexity_threshold: usize },
    /// Optimize memory allocation patterns
    OptimizeMemoryAllocation { target_memory_usage: usize },
    /// Disable optimizations that aren't helping
    DisableOptimization { optimization_name: String },
    /// No optimization needed
    NoOptimization,
}

/// Performance monitor that tracks metrics and manages adaptive optimization
pub struct PerformanceMonitor {
    metrics: Arc<Mutex<Vec<PerformanceMetrics>>>,
    #[allow(clippy::type_complexity)]
    profiles: Arc<Mutex<HashMap<String, ExpressionProfile>>>,
    regression_alerts: Arc<Mutex<Vec<RegressionAlert>>>,
    #[allow(dead_code)]
    optimization_strategies: Arc<Mutex<Vec<OptimizationStrategy>>>,
    config: PerformanceConfig,
}

#[derive(Debug, Clone)]
pub struct PerformanceConfig {
    pub enable_metrics_collection: bool,
    pub enable_regression_detection: bool,
    pub enable_adaptive_optimization: bool,
    pub metrics_retention_days: u32,
    pub regression_threshold: f64,
    pub cache_size_limit: usize,
    pub memory_usage_limit: usize,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            enable_metrics_collection: true,
            enable_regression_detection: true,
            enable_adaptive_optimization: true,
            metrics_retention_days: 30,
            regression_threshold: 0.1, // 10% degradation threshold
            cache_size_limit: 1000,
            memory_usage_limit: 100 * 1024 * 1024, // 100MB
        }
    }
}

impl Default for PerformanceMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceMonitor {
    /// Create a new performance monitor with default configuration
    pub fn new() -> Self {
        Self::with_config(PerformanceConfig::default())
    }

    /// Create a new performance monitor with custom configuration
    pub fn with_config(config: PerformanceConfig) -> Self {
        Self {
            metrics: Arc::new(Mutex::new(Vec::new())),
            profiles: Arc::new(Mutex::new(HashMap::new())),
            regression_alerts: Arc::new(Mutex::new(Vec::new())),
            optimization_strategies: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    /// Record performance metrics for an operation
    pub fn record_metrics(&self, metrics: PerformanceMetrics) {
        if !self.config.enable_metrics_collection {
            return;
        }

        if let Ok(mut metrics_vec) = self.metrics.lock() {
            metrics_vec.push(metrics.clone());

            // Clean up old metrics
            self.cleanup_old_metrics(&mut metrics_vec);

            // Update expression profiles
            self.update_expression_profile(&metrics);

            // Check for performance regressions
            if self.config.enable_regression_detection {
                self.check_for_regressions(&metrics);
            }
        }
    }

    /// Get current performance metrics
    pub fn get_metrics(&self) -> Vec<PerformanceMetrics> {
        self.metrics
            .lock()
            .map(|metrics| metrics.clone())
            .unwrap_or_default()
    }

    /// Get expression profiles
    pub fn get_profiles(&self) -> HashMap<String, ExpressionProfile> {
        self.profiles
            .lock()
            .map(|profiles| profiles.clone())
            .unwrap_or_default()
    }

    /// Get regression alerts
    pub fn get_regression_alerts(&self) -> Vec<RegressionAlert> {
        self.regression_alerts
            .lock()
            .map(|alerts| alerts.clone())
            .unwrap_or_default()
    }

    /// Get recommended optimization strategies
    pub fn get_optimization_strategies(&self) -> Vec<OptimizationStrategy> {
        if !self.config.enable_adaptive_optimization {
            return vec![OptimizationStrategy::NoOptimization];
        }

        let profiles = self.get_profiles();
        let mut strategies = Vec::new();

        for (_expr_type, profile) in profiles {
            // Check cache efficiency
            if profile.cache_efficiency < 0.8 {
                strategies.push(OptimizationStrategy::IncreaseCacheSize {
                    target_hit_rate: 0.9,
                });
            }

            // Check memory usage
            if profile.avg_memory_usage > self.config.memory_usage_limit / 10 {
                strategies.push(OptimizationStrategy::OptimizeMemoryAllocation {
                    target_memory_usage: self.config.memory_usage_limit / 20,
                });
            }

            // Check expression complexity
            if profile.complexity_score > 0.7 {
                strategies.push(OptimizationStrategy::EnableExpressionCaching {
                    complexity_threshold: (profile.complexity_score * 100.0) as usize,
                });
            }
        }

        if strategies.is_empty() {
            strategies.push(OptimizationStrategy::NoOptimization);
        }

        strategies
    }

    /// Generate performance report
    pub fn generate_report(&self) -> PerformanceReport {
        let metrics = self.get_metrics();
        let profiles = self.get_profiles();
        let alerts = self.get_regression_alerts();
        let strategies = self.get_optimization_strategies();

        let total_operations = metrics.len();
        let avg_execution_time = if total_operations > 0 {
            let total_time: Duration = metrics.iter().map(|m| m.execution_time).sum();
            total_time / total_operations as u32
        } else {
            Duration::ZERO
        };

        let total_memory_usage: usize = metrics.iter().map(|m| m.memory_usage_bytes).sum();

        let avg_memory_usage = if total_operations > 0 {
            total_memory_usage / total_operations
        } else {
            0
        };

        let cache_efficiency = if total_operations > 0 {
            let total_hits: u64 = metrics.iter().map(|m| m.cache_hits).sum();
            let total_misses: u64 = metrics.iter().map(|m| m.cache_misses).sum();
            let total_accesses = total_hits + total_misses;

            if total_accesses > 0 {
                total_hits as f64 / total_accesses as f64
            } else {
                0.0
            }
        } else {
            0.0
        };

        PerformanceReport {
            total_operations,
            avg_execution_time,
            avg_memory_usage,
            cache_efficiency,
            expression_profiles: profiles,
            regression_alerts: alerts,
            optimization_strategies: strategies,
            generated_at: std::time::SystemTime::now(),
        }
    }

    /// Clean up old metrics based on retention policy
    fn cleanup_old_metrics(&self, metrics: &mut Vec<PerformanceMetrics>) {
        let retention_duration =
            Duration::from_secs(self.config.metrics_retention_days as u64 * 24 * 60 * 60);
        let cutoff_time = std::time::SystemTime::now() - retention_duration;

        metrics.retain(|metric| metric.timestamp > cutoff_time);
    }

    /// Update expression profile with new metrics
    fn update_expression_profile(&self, metrics: &PerformanceMetrics) {
        if let Ok(mut profiles) = self.profiles.lock() {
            let profile =
                profiles
                    .entry(metrics.operation_name.clone())
                    .or_insert(ExpressionProfile {
                        expression_type: metrics.operation_name.clone(),
                        avg_execution_time: Duration::ZERO,
                        avg_memory_usage: 0,
                        cache_efficiency: 0.0,
                        complexity_score: 0.0,
                        sample_count: 0,
                        last_updated: std::time::SystemTime::now(),
                    });

            // Update running averages
            profile.sample_count += 1;
            let n = profile.sample_count as f64;

            // Exponential moving average for execution time
            let alpha = 0.1; // Smoothing factor
            let new_avg_time = profile.avg_execution_time.as_nanos() as f64;
            let current_time = metrics.execution_time.as_nanos() as f64;
            let updated_time = (1.0 - alpha) * new_avg_time + alpha * current_time;
            profile.avg_execution_time = Duration::from_nanos(updated_time as u64);

            // Update memory usage average
            profile.avg_memory_usage = (((n - 1.0) * profile.avg_memory_usage as f64
                + metrics.memory_usage_bytes as f64)
                / n) as usize;

            // Update cache efficiency
            let total_accesses = metrics.cache_hits + metrics.cache_misses;
            if total_accesses > 0 {
                let current_efficiency = metrics.cache_hits as f64 / total_accesses as f64;
                profile.cache_efficiency =
                    ((n - 1.0) * profile.cache_efficiency + current_efficiency) / n;
            }

            // Update complexity score
            let complexity = metrics.expression_complexity as f64;
            profile.complexity_score = ((n - 1.0) * profile.complexity_score + complexity) / n;

            profile.last_updated = std::time::SystemTime::now();
        }
    }

    /// Check for performance regressions
    fn check_for_regressions(&self, metrics: &PerformanceMetrics) {
        if let Ok(profiles) = self.profiles.lock() {
            if let Some(old_profile) = profiles.get(&metrics.operation_name) {
                let old_time = old_profile.avg_execution_time.as_nanos() as f64;
                let new_time = metrics.execution_time.as_nanos() as f64;

                if old_time > 0.0 {
                    let degradation = (new_time - old_time) / old_time;

                    if degradation > self.config.regression_threshold {
                        let severity = if degradation > 0.5 {
                            RegressionSeverity::Critical
                        } else if degradation > 0.25 {
                            RegressionSeverity::High
                        } else if degradation > 0.1 {
                            RegressionSeverity::Medium
                        } else {
                            RegressionSeverity::Low
                        };

                        let new_profile = ExpressionProfile {
                            expression_type: metrics.operation_name.clone(),
                            avg_execution_time: metrics.execution_time,
                            avg_memory_usage: metrics.memory_usage_bytes,
                            cache_efficiency: if metrics.cache_hits + metrics.cache_misses > 0 {
                                metrics.cache_hits as f64
                                    / (metrics.cache_hits + metrics.cache_misses) as f64
                            } else {
                                0.0
                            },
                            complexity_score: metrics.expression_complexity as f64,
                            sample_count: 1,
                            last_updated: std::time::SystemTime::now(),
                        };

                        let alert = RegressionAlert {
                            expression_type: metrics.operation_name.clone(),
                            severity,
                            old_performance: old_profile.clone(),
                            new_performance: new_profile,
                            performance_degradation: degradation,
                            timestamp: std::time::SystemTime::now(),
                        };

                        if let Ok(mut alerts) = self.regression_alerts.lock() {
                            alerts.push(alert);
                        }
                    }
                }
            }
        }
    }
}

/// Performance report containing aggregated metrics and recommendations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceReport {
    pub total_operations: usize,
    pub avg_execution_time: Duration,
    pub avg_memory_usage: usize,
    pub cache_efficiency: f64,
    pub expression_profiles: HashMap<String, ExpressionProfile>,
    pub regression_alerts: Vec<RegressionAlert>,
    pub optimization_strategies: Vec<OptimizationStrategy>,
    pub generated_at: std::time::SystemTime,
}

impl PerformanceReport {
    /// Print a human-readable summary of the performance report
    pub fn print_summary(&self) {
        println!("=== Performance Report ===");
        println!("Generated at: {:?}", self.generated_at);
        println!("Total operations: {}", self.total_operations);
        println!("Average execution time: {:?}", self.avg_execution_time);
        println!("Average memory usage: {} bytes", self.avg_memory_usage);
        println!("Cache efficiency: {:.2}%", self.cache_efficiency * 100.0);

        if !self.regression_alerts.is_empty() {
            println!("\n=== Performance Regressions ===");
            for alert in &self.regression_alerts {
                println!(
                    "{}: {:?} degradation ({:.1}%)",
                    alert.expression_type,
                    alert.severity,
                    alert.performance_degradation * 100.0
                );
            }
        }

        if !self.optimization_strategies.is_empty() {
            println!("\n=== Optimization Recommendations ===");
            for strategy in &self.optimization_strategies {
                match strategy {
                    OptimizationStrategy::IncreaseCacheSize { target_hit_rate } => {
                        println!(
                            "Increase cache size to achieve {:.1}% hit rate",
                            target_hit_rate * 100.0
                        );
                    }
                    OptimizationStrategy::EnableExpressionCaching {
                        complexity_threshold,
                    } => {
                        println!(
                            "Enable expression caching for expressions with complexity > {complexity_threshold}",
                        );
                    }
                    OptimizationStrategy::OptimizeMemoryAllocation {
                        target_memory_usage,
                    } => {
                        println!(
                            "Optimize memory allocation to target {target_memory_usage} bytes",
                        );
                    }
                    OptimizationStrategy::DisableOptimization { optimization_name } => {
                        println!("Consider disabling optimization: {optimization_name}");
                    }
                    OptimizationStrategy::NoOptimization => {
                        println!("No optimizations recommended at this time");
                    }
                }
            }
        }
    }
}

/// Performance measurement guard for automatic timing
pub struct PerformanceGuard {
    monitor: Arc<PerformanceMonitor>,
    operation_name: String,
    start_time: Instant,
    cache_hits: u64,
    cache_misses: u64,
    expression_complexity: usize,
}

impl PerformanceGuard {
    /// Create a new performance guard
    pub fn new(
        monitor: Arc<PerformanceMonitor>,
        operation_name: String,
        expression_complexity: usize,
    ) -> Self {
        Self {
            monitor,
            operation_name,
            start_time: Instant::now(),
            cache_hits: 0,
            cache_misses: 0,
            expression_complexity,
        }
    }

    /// Record a cache hit
    pub fn record_cache_hit(&mut self) {
        self.cache_hits += 1;
    }

    /// Record a cache miss
    pub fn record_cache_miss(&mut self) {
        self.cache_misses += 1;
    }
}

impl Drop for PerformanceGuard {
    fn drop(&mut self) {
        let execution_time = self.start_time.elapsed();

        // Estimate memory usage (this is a rough approximation)
        let memory_usage = self.expression_complexity * 64; // Rough estimate

        let metrics = PerformanceMetrics {
            operation_name: self.operation_name.clone(),
            execution_time,
            memory_usage_bytes: memory_usage,
            cache_hits: self.cache_hits,
            cache_misses: self.cache_misses,
            expression_complexity: self.expression_complexity,
            timestamp: std::time::SystemTime::now(),
        };

        self.monitor.record_metrics(metrics);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_performance_monitor_creation() {
        let monitor = PerformanceMonitor::new();
        let metrics = monitor.get_metrics();
        assert_eq!(metrics.len(), 0);
    }

    #[test]
    fn test_metrics_recording() {
        let monitor = Arc::new(PerformanceMonitor::new());

        let metrics = PerformanceMetrics {
            operation_name: "test_operation".to_string(),
            execution_time: Duration::from_millis(100),
            memory_usage_bytes: 1024,
            cache_hits: 5,
            cache_misses: 2,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };

        monitor.record_metrics(metrics);

        let recorded_metrics = monitor.get_metrics();
        assert_eq!(recorded_metrics.len(), 1);
        assert_eq!(recorded_metrics[0].operation_name, "test_operation");
    }

    #[test]
    fn test_performance_guard() {
        let monitor = Arc::new(PerformanceMonitor::new());

        {
            let mut guard = PerformanceGuard::new(monitor.clone(), "test_guard".to_string(), 5);
            guard.record_cache_hit();
            guard.record_cache_miss();
            // Guard will automatically record metrics when dropped
        }

        let metrics = monitor.get_metrics();
        assert_eq!(metrics.len(), 1);
        assert_eq!(metrics[0].operation_name, "test_guard");
        assert_eq!(metrics[0].cache_hits, 1);
        assert_eq!(metrics[0].cache_misses, 1);
    }

    #[test]
    fn test_regression_detection() {
        let config = PerformanceConfig {
            regression_threshold: 0.1, // 10% threshold
            ..Default::default()
        };

        let monitor = PerformanceMonitor::with_config(config);

        // Record baseline metrics
        let baseline_metrics = PerformanceMetrics {
            operation_name: "test_op".to_string(),
            execution_time: Duration::from_millis(100),
            memory_usage_bytes: 1024,
            cache_hits: 5,
            cache_misses: 5,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };

        monitor.record_metrics(baseline_metrics);

        // Record degraded performance
        let degraded_metrics = PerformanceMetrics {
            operation_name: "test_op".to_string(),
            execution_time: Duration::from_millis(150), // 50% degradation
            memory_usage_bytes: 1024,
            cache_hits: 5,
            cache_misses: 5,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };

        monitor.record_metrics(degraded_metrics);

        let alerts = monitor.get_regression_alerts();
        assert!(!alerts.is_empty());
        assert_eq!(alerts[0].severity, RegressionSeverity::Critical);
    }

    #[test]
    fn test_performance_report_generation() {
        let monitor = PerformanceMonitor::new();

        // Add some test metrics
        let metrics = PerformanceMetrics {
            operation_name: "test_operation".to_string(),
            execution_time: Duration::from_millis(100),
            memory_usage_bytes: 1024,
            cache_hits: 8,
            cache_misses: 2,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };

        monitor.record_metrics(metrics);

        let report = monitor.generate_report();
        assert_eq!(report.total_operations, 1);
        assert_eq!(report.cache_efficiency, 0.8); // 8 hits / 10 total
    }
}
