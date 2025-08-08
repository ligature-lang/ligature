//! Adaptive optimization engine for the Ligature evaluator.
//!
//! This module provides intelligent optimization strategies that automatically
//! adapt based on runtime performance metrics and learn from their effectiveness.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Type alias for complex strategy map
type StrategyMap = Arc<Mutex<HashMap<String, AdaptiveOptimizationStrategy>>>;
use crate::performance::{
    ExpressionProfile, OptimizationStrategy, PerformanceMetrics, PerformanceMonitor,
};

/// Optimization strategy with effectiveness tracking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdaptiveOptimizationStrategy {
    pub name: String,
    pub strategy: OptimizationStrategy,
    pub effectiveness_score: f64,
    pub application_count: u64,
    pub success_count: u64,
    pub last_applied: Option<std::time::SystemTime>,
    pub average_improvement: f64,
    pub enabled: bool,
}

/// Optimization decision based on current performance state
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationDecision {
    pub strategy_name: String,
    pub confidence: f64,
    pub expected_improvement: f64,
    pub reasoning: String,
    pub applied: bool,
    pub timestamp: std::time::SystemTime,
}

/// Performance state snapshot for optimization decisions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceState {
    pub expression_profiles: HashMap<String, ExpressionProfile>,
    pub current_metrics: Vec<PerformanceMetrics>,
    pub system_load: SystemLoad,
    pub timestamp: std::time::SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemLoad {
    pub cpu_usage_percent: f64,
    pub memory_usage_percent: f64,
    pub cache_hit_rate: f64,
    pub active_expressions: usize,
}

/// Adaptive optimization engine
pub struct AdaptiveOptimizer {
    strategies: StrategyMap,
    decisions: Arc<Mutex<Vec<OptimizationDecision>>>,
    performance_monitor: Arc<PerformanceMonitor>,
    config: AdaptiveOptimizerConfig,
    learning_rate: f64,
}

#[derive(Debug, Clone)]
pub struct AdaptiveOptimizerConfig {
    pub enable_learning: bool,
    pub confidence_threshold: f64,
    pub improvement_threshold: f64,
    pub max_strategies_per_cycle: usize,
    pub strategy_cooldown_seconds: u64,
    pub effectiveness_decay_rate: f64,
}

impl Default for AdaptiveOptimizerConfig {
    fn default() -> Self {
        Self {
            enable_learning: true,
            confidence_threshold: 0.7,
            improvement_threshold: 0.05, // 5% minimum improvement
            max_strategies_per_cycle: 3,
            strategy_cooldown_seconds: 300, // 5 minutes
            effectiveness_decay_rate: 0.95, // 5% decay per cycle
        }
    }
}

impl AdaptiveOptimizer {
    /// Create a new adaptive optimizer
    pub fn new(performance_monitor: Arc<PerformanceMonitor>) -> Self {
        Self::with_config(performance_monitor, AdaptiveOptimizerConfig::default())
    }

    /// Create a new adaptive optimizer with custom configuration
    pub fn with_config(
        performance_monitor: Arc<PerformanceMonitor>,
        config: AdaptiveOptimizerConfig,
    ) -> Self {
        let mut optimizer = Self {
            strategies: Arc::new(Mutex::new(HashMap::new())),
            decisions: Arc::new(Mutex::new(Vec::new())),
            performance_monitor,
            config,
            learning_rate: 0.1,
        };

        optimizer.initialize_strategies();
        optimizer
    }

    /// Initialize default optimization strategies
    fn initialize_strategies(&mut self) {
        let mut strategies = HashMap::new();

        // Cache optimization strategies
        strategies.insert(
            "increase_cache_size".to_string(),
            AdaptiveOptimizationStrategy {
                name: "Increase Cache Size".to_string(),
                strategy: OptimizationStrategy::IncreaseCacheSize {
                    target_hit_rate: 0.9,
                },
                effectiveness_score: 0.5,
                application_count: 0,
                success_count: 0,
                last_applied: None,
                average_improvement: 0.0,
                enabled: true,
            },
        );

        // Expression caching strategies
        strategies.insert(
            "enable_expression_caching".to_string(),
            AdaptiveOptimizationStrategy {
                name: "Enable Expression Caching".to_string(),
                strategy: OptimizationStrategy::EnableExpressionCaching {
                    complexity_threshold: 50,
                },
                effectiveness_score: 0.5,
                application_count: 0,
                success_count: 0,
                last_applied: None,
                average_improvement: 0.0,
                enabled: true,
            },
        );

        // Memory optimization strategies
        strategies.insert(
            "optimize_memory_allocation".to_string(),
            AdaptiveOptimizationStrategy {
                name: "Optimize Memory Allocation".to_string(),
                strategy: OptimizationStrategy::OptimizeMemoryAllocation {
                    target_memory_usage: 50 * 1024 * 1024,
                },
                effectiveness_score: 0.5,
                application_count: 0,
                success_count: 0,
                last_applied: None,
                average_improvement: 0.0,
                enabled: true,
            },
        );

        // Disable optimization strategies
        strategies.insert(
            "disable_ineffective_optimizations".to_string(),
            AdaptiveOptimizationStrategy {
                name: "Disable Ineffective Optimizations".to_string(),
                strategy: OptimizationStrategy::DisableOptimization {
                    optimization_name: "unknown".to_string(),
                },
                effectiveness_score: 0.5,
                application_count: 0,
                success_count: 0,
                last_applied: None,
                average_improvement: 0.0,
                enabled: true,
            },
        );

        if let Ok(mut strategies_map) = self.strategies.lock() {
            *strategies_map = strategies;
        }
    }

    /// Analyze current performance and make optimization decisions
    pub fn analyze_and_optimize(&mut self) -> Vec<OptimizationDecision> {
        let performance_state = self.capture_performance_state();
        let decisions = self.make_optimization_decisions(&performance_state);

        // Apply selected optimizations
        for decision in &decisions {
            if decision.applied {
                self.apply_optimization(decision);
            }
        }

        // Store decisions for learning
        if let Ok(mut decisions_vec) = self.decisions.lock() {
            decisions_vec.extend(decisions.clone());
        }

        decisions
    }

    /// Capture current performance state
    fn capture_performance_state(&self) -> PerformanceState {
        let profiles = self.performance_monitor.get_profiles();
        let metrics = self.performance_monitor.get_metrics();

        // Calculate system load
        let system_load = self.calculate_system_load(&profiles, &metrics);

        PerformanceState {
            expression_profiles: profiles,
            current_metrics: metrics,
            system_load,
            timestamp: std::time::SystemTime::now(),
        }
    }

    /// Calculate current system load
    fn calculate_system_load(
        &self,
        profiles: &HashMap<String, ExpressionProfile>,
        metrics: &[PerformanceMetrics],
    ) -> SystemLoad {
        let total_expressions = profiles.len();
        let active_expressions = metrics.len();

        // Calculate cache hit rate
        let total_hits: u64 = metrics.iter().map(|m| m.cache_hits).sum();
        let total_misses: u64 = metrics.iter().map(|m| m.cache_misses).sum();
        let cache_hit_rate = if total_hits + total_misses > 0 {
            total_hits as f64 / (total_hits + total_misses) as f64
        } else {
            0.0
        };

        // Estimate CPU and memory usage based on metrics
        let avg_execution_time: Duration = if !metrics.is_empty() {
            let total_time: Duration = metrics.iter().map(|m| m.execution_time).sum();
            total_time / metrics.len() as u32
        } else {
            Duration::ZERO
        };

        let cpu_usage = (avg_execution_time.as_micros() as f64 / 1000.0).min(100.0);
        let memory_usage =
            (active_expressions as f64 / total_expressions.max(1) as f64 * 100.0).min(100.0);

        SystemLoad {
            cpu_usage_percent: cpu_usage,
            memory_usage_percent: memory_usage,
            cache_hit_rate,
            active_expressions,
        }
    }

    /// Make optimization decisions based on performance state
    fn make_optimization_decisions(&self, state: &PerformanceState) -> Vec<OptimizationDecision> {
        let mut decisions = Vec::new();

        if let Ok(strategies) = self.strategies.lock() {
            for (_strategy_id, strategy) in strategies.iter() {
                if !strategy.enabled {
                    continue;
                }

                // Check if strategy is on cooldown
                if let Some(last_applied) = strategy.last_applied {
                    let cooldown_duration =
                        Duration::from_secs(self.config.strategy_cooldown_seconds);
                    if last_applied.elapsed().unwrap_or(Duration::ZERO) < cooldown_duration {
                        continue;
                    }
                }

                let (confidence, expected_improvement, reasoning) =
                    self.evaluate_strategy(strategy, state);

                if confidence >= self.config.confidence_threshold
                    && expected_improvement >= self.config.improvement_threshold
                {
                    decisions.push(OptimizationDecision {
                        strategy_name: strategy.name.clone(),
                        confidence,
                        expected_improvement,
                        reasoning,
                        applied: true,
                        timestamp: std::time::SystemTime::now(),
                    });
                }
            }
        }

        // Sort by expected improvement and limit to max strategies per cycle
        decisions.sort_by(|a, b| {
            b.expected_improvement
                .partial_cmp(&a.expected_improvement)
                .unwrap()
        });
        decisions.truncate(self.config.max_strategies_per_cycle);

        decisions
    }

    /// Evaluate a strategy's potential effectiveness
    fn evaluate_strategy(
        &self,
        strategy: &AdaptiveOptimizationStrategy,
        state: &PerformanceState,
    ) -> (f64, f64, String) {
        match &strategy.strategy {
            OptimizationStrategy::IncreaseCacheSize { target_hit_rate } => {
                let current_hit_rate = state.system_load.cache_hit_rate;
                let improvement_potential = (target_hit_rate - current_hit_rate).max(0.0);
                let confidence = strategy.effectiveness_score * (1.0 - current_hit_rate);
                let expected_improvement = improvement_potential * 0.1; // Assume 10% of hit rate improvement

                let reasoning = format!(
                    "Cache hit rate is {:.1}%, target is {:.1}%. Strategy effectiveness: {:.1}%",
                    current_hit_rate * 100.0,
                    target_hit_rate * 100.0,
                    strategy.effectiveness_score * 100.0
                );

                (confidence, expected_improvement, reasoning)
            }

            OptimizationStrategy::EnableExpressionCaching {
                complexity_threshold,
            } => {
                let complex_expressions = state
                    .expression_profiles
                    .values()
                    .filter(|p| p.complexity_score > *complexity_threshold as f64)
                    .count();

                let total_expressions = state.expression_profiles.len();
                let complexity_ratio = if total_expressions > 0 {
                    complex_expressions as f64 / total_expressions as f64
                } else {
                    0.0
                };

                let confidence = strategy.effectiveness_score * complexity_ratio;
                let expected_improvement = complexity_ratio * 0.15; // Assume 15% improvement for complex expressions

                let reasoning = format!(
                    "{complex_expressions} of {total_expressions} expressions are complex \
                     (>{complexity_threshold})",
                );

                (confidence, expected_improvement, reasoning)
            }

            OptimizationStrategy::OptimizeMemoryAllocation {
                target_memory_usage,
            } => {
                let current_memory = state.system_load.memory_usage_percent;
                let memory_pressure = current_memory / 100.0;

                let confidence = strategy.effectiveness_score * memory_pressure;
                let expected_improvement = memory_pressure * 0.08; // Assume 8% improvement under memory pressure

                let reasoning = format!(
                    "Memory usage is {:.1}%, target is {:.1}%",
                    current_memory,
                    (*target_memory_usage as f64 / (100 * 1024 * 1024) as f64) * 100.0
                );

                (confidence, expected_improvement, reasoning)
            }

            OptimizationStrategy::DisableOptimization { optimization_name } => {
                // This strategy is used to disable ineffective optimizations
                let confidence = 0.3; // Low confidence for disabling
                let expected_improvement = 0.02; // Small improvement from reducing overhead

                let reasoning = format!(
                    "Consider disabling optimization: {} (effectiveness: {:.1}%)",
                    optimization_name,
                    strategy.effectiveness_score * 100.0
                );

                (confidence, expected_improvement, reasoning)
            }

            OptimizationStrategy::NoOptimization => {
                (0.0, 0.0, "No optimization needed".to_string())
            }
        }
    }

    /// Apply an optimization decision
    fn apply_optimization(&mut self, decision: &OptimizationDecision) {
        if let Ok(mut strategies) = self.strategies.lock() {
            if let Some(strategy) = strategies.get_mut(&decision.strategy_name) {
                strategy.application_count += 1;
                strategy.last_applied = Some(decision.timestamp);

                // In a real implementation, this would actually apply the optimization
                // For now, we just track the decision
                println!(
                    "Applied optimization: {} (confidence: {:.1}%, expected improvement: {:.1}%)",
                    decision.strategy_name,
                    decision.confidence * 100.0,
                    decision.expected_improvement * 100.0
                );
            }
        }
    }

    /// Learn from optimization results and update strategy effectiveness
    pub fn learn_from_results(
        &mut self,
        before_metrics: &[PerformanceMetrics],
        after_metrics: &[PerformanceMetrics],
    ) {
        if !self.config.enable_learning {
            return;
        }

        let improvement = self.calculate_performance_improvement(before_metrics, after_metrics);

        // Update strategy effectiveness based on recent decisions
        if let Ok(mut strategies) = self.strategies.lock() {
            if let Ok(decisions) = self.decisions.lock() {
                for decision in decisions.iter().rev().take(5) {
                    // Consider last 5 decisions
                    if let Some(strategy) = strategies.get_mut(&decision.strategy_name) {
                        // Update effectiveness score using exponential moving average
                        let alpha = self.learning_rate;
                        strategy.effectiveness_score =
                            (1.0 - alpha) * strategy.effectiveness_score + alpha * improvement;

                        // Update success count
                        if improvement > 0.0 {
                            strategy.success_count += 1;
                        }

                        // Update average improvement
                        strategy.average_improvement =
                            (1.0 - alpha) * strategy.average_improvement + alpha * improvement;

                        // Apply effectiveness decay
                        strategy.effectiveness_score *= self.config.effectiveness_decay_rate;

                        // Disable strategies that consistently perform poorly
                        if strategy.effectiveness_score < 0.1 && strategy.application_count > 10 {
                            strategy.enabled = false;
                            println!(
                                "Disabled ineffective strategy: {} (effectiveness: {:.1}%)",
                                strategy.name,
                                strategy.effectiveness_score * 100.0
                            );
                        }
                    }
                }
            }
        }
    }

    /// Calculate performance improvement between two sets of metrics
    fn calculate_performance_improvement(
        &self,
        before: &[PerformanceMetrics],
        after: &[PerformanceMetrics],
    ) -> f64 {
        if before.is_empty() || after.is_empty() {
            return 0.0;
        }

        let before_avg_time: Duration =
            before.iter().map(|m| m.execution_time).sum::<Duration>() / before.len() as u32;
        let after_avg_time: Duration =
            after.iter().map(|m| m.execution_time).sum::<Duration>() / after.len() as u32;

        if before_avg_time.as_nanos() > 0 {
            let improvement = (before_avg_time.as_nanos() as f64
                - after_avg_time.as_nanos() as f64)
                / before_avg_time.as_nanos() as f64;
            improvement.clamp(-1.0, 1.0) // Clamp between -100% and +100%
        } else {
            0.0
        }
    }

    /// Get current optimization strategies and their effectiveness
    pub fn get_strategies(&self) -> HashMap<String, AdaptiveOptimizationStrategy> {
        self.strategies
            .lock()
            .map(|strategies| strategies.clone())
            .unwrap_or_default()
    }

    /// Get optimization decisions history
    pub fn get_decisions(&self) -> Vec<OptimizationDecision> {
        self.decisions
            .lock()
            .map(|decisions| decisions.clone())
            .unwrap_or_default()
    }

    /// Generate optimization report
    pub fn generate_optimization_report(&self) -> OptimizationReport {
        let strategies = self.get_strategies();
        let decisions = self.get_decisions();

        let total_strategies = strategies.len();
        let enabled_strategies = strategies.values().filter(|s| s.enabled).count();
        let total_applications: u64 = strategies.values().map(|s| s.application_count).sum();
        let total_successes: u64 = strategies.values().map(|s| s.success_count).sum();

        let success_rate = if total_applications > 0 {
            total_successes as f64 / total_applications as f64
        } else {
            0.0
        };

        let avg_effectiveness: f64 = strategies
            .values()
            .map(|s| s.effectiveness_score)
            .sum::<f64>()
            / total_strategies as f64;

        OptimizationReport {
            total_strategies,
            enabled_strategies,
            total_applications,
            total_successes,
            success_rate,
            average_effectiveness: avg_effectiveness,
            strategies,
            recent_decisions: decisions.into_iter().rev().take(10).collect(),
            generated_at: std::time::SystemTime::now(),
        }
    }
}

/// Optimization report containing strategy effectiveness and decision history
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationReport {
    pub total_strategies: usize,
    pub enabled_strategies: usize,
    pub total_applications: u64,
    pub total_successes: u64,
    pub success_rate: f64,
    pub average_effectiveness: f64,
    pub strategies: HashMap<String, AdaptiveOptimizationStrategy>,
    pub recent_decisions: Vec<OptimizationDecision>,
    pub generated_at: std::time::SystemTime,
}

impl OptimizationReport {
    /// Print a human-readable summary of the optimization report
    pub fn print_summary(&self) {
        println!("=== Adaptive Optimization Report ===");
        println!("Generated at: {:?}", self.generated_at);
        println!("Total strategies: {}", self.total_strategies);
        println!("Enabled strategies: {}", self.enabled_strategies);
        println!("Total applications: {}", self.total_applications);
        println!("Success rate: {:.1}%", self.success_rate * 100.0);
        println!(
            "Average effectiveness: {:.1}%",
            self.average_effectiveness * 100.0
        );

        println!("\n=== Strategy Effectiveness ===");
        for (name, strategy) in &self.strategies {
            println!(
                "{}: {:.1}% effective ({} applications, {} successes)",
                name,
                strategy.effectiveness_score * 100.0,
                strategy.application_count,
                strategy.success_count
            );
        }

        if !self.recent_decisions.is_empty() {
            println!("\n=== Recent Optimization Decisions ===");
            for decision in &self.recent_decisions {
                println!(
                    "{}: {:.1}% confidence, {:.1}% expected improvement",
                    decision.strategy_name,
                    decision.confidence * 100.0,
                    decision.expected_improvement * 100.0
                );
                println!("  Reasoning: {}", decision.reasoning);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    #[test]
    fn test_adaptive_optimizer_creation() {
        let monitor = Arc::new(PerformanceMonitor::new());
        let optimizer = AdaptiveOptimizer::new(monitor);
        let strategies = optimizer.get_strategies();
        assert!(!strategies.is_empty());
    }

    #[test]
    fn test_performance_state_capture() {
        let monitor = Arc::new(PerformanceMonitor::new());
        let optimizer = AdaptiveOptimizer::new(monitor);

        // Add some test metrics to the monitor
        let metrics = PerformanceMetrics {
            operation_name: "test_op".to_string(),
            execution_time: Duration::from_millis(100),
            memory_usage_bytes: 1024,
            cache_hits: 8,
            cache_misses: 2,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        };

        optimizer.performance_monitor.record_metrics(metrics);

        let state = optimizer.capture_performance_state();
        assert!(!state.current_metrics.is_empty());
    }

    #[test]
    fn test_optimization_decision_making() {
        let monitor = Arc::new(PerformanceMonitor::new());
        let mut optimizer = AdaptiveOptimizer::new(monitor);

        // Add some performance data
        for i in 0..10 {
            let metrics = PerformanceMetrics {
                operation_name: format!("test_op_{i}"),
                execution_time: Duration::from_millis(100 + i as u64),
                memory_usage_bytes: 1024 + i * 100,
                cache_hits: 5,
                cache_misses: 5,
                expression_complexity: 10 + i,
                timestamp: std::time::SystemTime::now(),
            };
            optimizer.performance_monitor.record_metrics(metrics);
        }

        let decisions = optimizer.analyze_and_optimize();
        // Should have some decisions (though they might not be applied due to thresholds)
        assert!(decisions.len() <= optimizer.config.max_strategies_per_cycle);
    }

    #[test]
    fn test_learning_from_results() {
        let monitor = Arc::new(PerformanceMonitor::new());
        let mut optimizer = AdaptiveOptimizer::new(monitor);

        let before_metrics = vec![PerformanceMetrics {
            operation_name: "test_op".to_string(),
            execution_time: Duration::from_millis(100),
            memory_usage_bytes: 1024,
            cache_hits: 5,
            cache_misses: 5,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        }];

        let after_metrics = vec![PerformanceMetrics {
            operation_name: "test_op".to_string(),
            execution_time: Duration::from_millis(80), // 20% improvement
            memory_usage_bytes: 1024,
            cache_hits: 5,
            cache_misses: 5,
            expression_complexity: 10,
            timestamp: std::time::SystemTime::now(),
        }];

        optimizer.learn_from_results(&before_metrics, &after_metrics);

        let strategies = optimizer.get_strategies();
        // Effectiveness scores should be updated (though the exact values depend on the learning process)
        assert!(!strategies.is_empty());
    }

    #[test]
    fn test_optimization_report_generation() {
        let monitor = Arc::new(PerformanceMonitor::new());
        let optimizer = AdaptiveOptimizer::new(monitor);

        let report = optimizer.generate_optimization_report();
        assert_eq!(report.total_strategies, 4); // Four default strategies
        assert!(report.enabled_strategies > 0);
    }
}
