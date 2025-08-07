//! Configuration management for the Ligature evaluator.

use embouchure_xdg::config::XdgConfig;
use embouchure_xdg::error::XdgError;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Configuration for the Ligature evaluator with cache tuning options.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct EvaluatorConfig {
    /// Cache configuration
    #[serde(default)]
    pub cache: CacheConfig,

    /// Performance optimization settings
    #[serde(default)]
    pub performance: PerformanceConfig,

    /// Memory management settings
    #[serde(default)]
    pub memory: MemoryConfig,

    /// Debugging and monitoring settings
    #[serde(default)]
    pub debug: DebugConfig,
}

/// Cache-specific configuration options.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    /// Whether to enable expression caching
    #[serde(default = "default_enable_caching")]
    pub enabled: bool,

    /// Maximum number of cached expressions
    #[serde(default = "default_cache_size")]
    pub max_size: usize,

    /// Maximum memory usage for cache in bytes
    #[serde(default = "default_cache_memory")]
    pub max_memory_bytes: usize,

    /// Cache warming strategy
    #[serde(default)]
    pub warming: CacheWarmingConfig,

    /// Expression types to cache
    #[serde(default)]
    pub cacheable_expressions: CacheableExpressions,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enabled: default_enable_caching(),
            max_size: default_cache_size(),
            max_memory_bytes: default_cache_memory(),
            warming: CacheWarmingConfig::default(),
            cacheable_expressions: CacheableExpressions::default(),
        }
    }
}

/// Cache warming configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheWarmingConfig {
    /// Whether to enable cache warming
    #[serde(default = "default_enable_warming")]
    pub enabled: bool,

    /// Maximum number of expressions to pre-warm
    #[serde(default = "default_warming_size")]
    pub max_expressions: usize,

    /// Whether to warm cache on module load
    #[serde(default = "default_warm_on_load")]
    pub warm_on_module_load: bool,
}

impl Default for CacheWarmingConfig {
    fn default() -> Self {
        Self {
            enabled: default_enable_warming(),
            max_expressions: default_warming_size(),
            warm_on_module_load: default_warm_on_load(),
        }
    }
}

/// Configuration for which expression types to cache.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheableExpressions {
    /// Cache literal expressions
    #[serde(default = "default_cache_literals")]
    pub literals: bool,

    /// Cache variable lookups
    #[serde(default = "default_cache_variables")]
    pub variables: bool,

    /// Cache binary operations
    #[serde(default = "default_cache_binary_ops")]
    pub binary_ops: bool,

    /// Cache unary operations
    #[serde(default = "default_cache_unary_ops")]
    pub unary_ops: bool,

    /// Cache field access operations
    #[serde(default = "default_cache_field_access")]
    pub field_access: bool,

    /// Cache function applications (use with caution)
    #[serde(default = "default_cache_applications")]
    pub applications: bool,

    /// Cache let expressions
    #[serde(default = "default_cache_let")]
    pub let_expressions: bool,

    /// Cache record expressions
    #[serde(default = "default_cache_records")]
    pub records: bool,

    /// Cache union expressions
    #[serde(default = "default_cache_unions")]
    pub unions: bool,

    /// Cache match expressions
    #[serde(default = "default_cache_matches")]
    pub matches: bool,

    /// Cache if expressions
    #[serde(default = "default_cache_if")]
    pub if_expressions: bool,
}

impl Default for CacheableExpressions {
    fn default() -> Self {
        Self {
            literals: default_cache_literals(),
            variables: default_cache_variables(),
            binary_ops: default_cache_binary_ops(),
            unary_ops: default_cache_unary_ops(),
            field_access: default_cache_field_access(),
            applications: default_cache_applications(),
            let_expressions: default_cache_let(),
            records: default_cache_records(),
            unions: default_cache_unions(),
            matches: default_cache_matches(),
            if_expressions: default_cache_if(),
        }
    }
}

/// Performance optimization settings
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Enable tail call optimization
    #[serde(default = "default_enable_tco")]
    pub tail_call_optimization: bool,

    /// Enable stack-based evaluation for simple functions
    #[serde(default = "default_enable_stack_eval")]
    pub stack_based_evaluation: bool,

    /// Enable value interning optimization
    #[serde(default = "default_enable_value_optimization")]
    pub value_optimization: bool,

    /// Maximum call stack depth
    #[serde(default = "default_max_stack_depth")]
    pub max_stack_depth: usize,

    /// Environment pool size
    #[serde(default = "default_env_pool_size")]
    pub env_pool_size: usize,

    /// Value pool size
    #[serde(default = "default_value_pool_size")]
    pub value_pool_size: usize,

    /// Advanced optimization settings
    #[serde(default)]
    pub advanced: AdvancedOptimizationConfig,

    /// Parallel evaluation settings
    #[serde(default)]
    pub parallel: ParallelEvaluationConfig,

    /// Memory management settings
    #[serde(default)]
    pub memory_management: MemoryManagementConfig,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            tail_call_optimization: default_enable_tco(),
            stack_based_evaluation: default_enable_stack_eval(),
            value_optimization: default_enable_value_optimization(),
            max_stack_depth: default_max_stack_depth(),
            env_pool_size: default_env_pool_size(),
            value_pool_size: default_value_pool_size(),
            advanced: AdvancedOptimizationConfig::default(),
            parallel: ParallelEvaluationConfig::default(),
            memory_management: MemoryManagementConfig::default(),
        }
    }
}

/// Advanced optimization configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdvancedOptimizationConfig {
    /// Enable function inlining for small functions
    #[serde(default = "default_enable_function_inlining")]
    pub function_inlining: bool,

    /// Maximum function size for inlining (number of expressions)
    #[serde(default = "default_max_inline_size")]
    pub max_inline_size: usize,

    /// Enable closure capture analysis optimization
    #[serde(default = "default_enable_closure_optimization")]
    pub closure_optimization: bool,

    /// Enable minimal capture analysis
    #[serde(default = "default_enable_minimal_capture")]
    pub minimal_capture: bool,

    /// Enable sophisticated tail call detection
    #[serde(default = "default_enable_advanced_tco")]
    pub advanced_tail_call_detection: bool,

    /// Enable pattern-based tail call recognition
    #[serde(default = "default_enable_pattern_tco")]
    pub pattern_based_tco: bool,

    /// Enable context-sensitive tail call analysis
    #[serde(default = "default_enable_context_tco")]
    pub context_sensitive_tco: bool,

    /// Enable nested function tail call optimization
    #[serde(default = "default_enable_nested_tco")]
    pub nested_function_tco: bool,
}

impl Default for AdvancedOptimizationConfig {
    fn default() -> Self {
        Self {
            function_inlining: default_enable_function_inlining(),
            max_inline_size: default_max_inline_size(),
            closure_optimization: default_enable_closure_optimization(),
            minimal_capture: default_enable_minimal_capture(),
            advanced_tail_call_detection: default_enable_advanced_tco(),
            pattern_based_tco: default_enable_pattern_tco(),
            context_sensitive_tco: default_enable_context_tco(),
            nested_function_tco: default_enable_nested_tco(),
        }
    }
}

/// Parallel evaluation configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParallelEvaluationConfig {
    /// Enable parallel expression evaluation
    #[serde(default = "default_enable_parallel_eval")]
    pub enabled: bool,

    /// Number of worker threads for parallel evaluation
    #[serde(default = "default_worker_threads")]
    pub worker_threads: usize,

    /// Enable work-stealing scheduler
    #[serde(default = "default_enable_work_stealing")]
    pub work_stealing: bool,

    /// Minimum expression complexity for parallel evaluation
    #[serde(default = "default_min_parallel_complexity")]
    pub min_complexity: usize,

    /// Enable adaptive parallelism based on workload
    #[serde(default = "default_enable_adaptive_parallelism")]
    pub adaptive_parallelism: bool,

    /// Enable thread-safe value sharing
    #[serde(default = "default_enable_thread_safe_values")]
    pub thread_safe_values: bool,
}

impl Default for ParallelEvaluationConfig {
    fn default() -> Self {
        Self {
            enabled: default_enable_parallel_eval(),
            worker_threads: default_worker_threads(),
            work_stealing: default_enable_work_stealing(),
            min_complexity: default_min_parallel_complexity(),
            adaptive_parallelism: default_enable_adaptive_parallelism(),
            thread_safe_values: default_enable_thread_safe_values(),
        }
    }
}

/// Memory management configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryManagementConfig {
    /// Enable generational garbage collection
    #[serde(default = "default_enable_generational_gc")]
    pub generational_gc: bool,

    /// Enable memory compaction strategies
    #[serde(default = "default_enable_memory_compaction")]
    pub memory_compaction: bool,

    /// Enable object pooling for common types
    #[serde(default = "default_enable_object_pooling")]
    pub object_pooling: bool,

    /// Young generation size (bytes)
    #[serde(default = "default_young_gen_size")]
    pub young_gen_size: usize,

    /// Old generation size (bytes)
    #[serde(default = "default_old_gen_size")]
    pub old_gen_size: usize,

    /// Garbage collection frequency (number of allocations)
    #[serde(default = "default_gc_frequency")]
    pub gc_frequency: usize,

    /// Enable memory defragmentation
    #[serde(default = "default_enable_defragmentation")]
    pub defragmentation: bool,

    /// Enable memory pre-allocation strategies
    #[serde(default = "default_enable_pre_allocation")]
    pub pre_allocation: bool,
}

impl Default for MemoryManagementConfig {
    fn default() -> Self {
        Self {
            generational_gc: default_enable_generational_gc(),
            memory_compaction: default_enable_memory_compaction(),
            object_pooling: default_enable_object_pooling(),
            young_gen_size: default_young_gen_size(),
            old_gen_size: default_old_gen_size(),
            gc_frequency: default_gc_frequency(),
            defragmentation: default_enable_defragmentation(),
            pre_allocation: default_enable_pre_allocation(),
        }
    }
}

/// Memory management configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryConfig {
    /// Enable memory monitoring
    #[serde(default = "default_enable_memory_monitoring")]
    pub monitoring: bool,

    /// Memory usage threshold for cache eviction (percentage)
    #[serde(default = "default_memory_threshold")]
    pub eviction_threshold_percent: f64,

    /// Maximum memory usage per evaluation (bytes)
    #[serde(default = "default_max_evaluation_memory")]
    pub max_evaluation_memory_bytes: usize,

    /// Garbage collection frequency (number of evaluations)
    #[serde(default = "default_gc_frequency")]
    pub gc_frequency: usize,
}

impl Default for MemoryConfig {
    fn default() -> Self {
        Self {
            monitoring: default_enable_memory_monitoring(),
            eviction_threshold_percent: default_memory_threshold(),
            max_evaluation_memory_bytes: default_max_evaluation_memory(),
            gc_frequency: default_gc_frequency(),
        }
    }
}

/// Debug and monitoring configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugConfig {
    /// Enable detailed logging
    #[serde(default = "default_enable_logging")]
    pub logging: bool,

    /// Enable performance profiling
    #[serde(default = "default_enable_profiling")]
    pub profiling: bool,

    /// Enable cache statistics collection
    #[serde(default = "default_enable_cache_stats")]
    pub cache_statistics: bool,

    /// Enable memory usage tracking
    #[serde(default = "default_enable_memory_tracking")]
    pub memory_tracking: bool,

    /// Log level for debug output
    #[serde(default = "default_log_level")]
    pub log_level: LogLevel,
}

impl Default for DebugConfig {
    fn default() -> Self {
        Self {
            logging: default_enable_logging(),
            profiling: default_enable_profiling(),
            cache_statistics: default_enable_cache_stats(),
            memory_tracking: default_enable_memory_tracking(),
            log_level: default_log_level(),
        }
    }
}

/// Log level for debug output.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
#[derive(Default)]
pub enum LogLevel {
    Error,
    Warn,
    #[default]
    Info,
    Debug,
    Trace,
}

/// Configuration manager for the evaluator.
#[derive(Debug)]
pub struct EvaluatorConfigManager {
    global_config: XdgConfig,
    project_config_path: Option<PathBuf>,
}

impl EvaluatorConfigManager {
    /// Create a new configuration manager.
    pub fn new() -> Result<Self, XdgError> {
        let global_config = XdgConfig::new("ligature", "eval.toml")?;
        Ok(Self {
            global_config,
            project_config_path: None,
        })
    }

    /// Set a project-specific configuration file.
    pub fn with_project_config(mut self, project_config_path: PathBuf) -> Self {
        self.project_config_path = Some(project_config_path);
        self
    }

    /// Load configuration with hierarchical override support.
    pub async fn load_config(&self) -> Result<EvaluatorConfig, ConfigError> {
        // Start with default configuration
        let mut config = EvaluatorConfig::default();

        // Load global configuration
        if let Some(global_config) = self.load_global_config().await? {
            config = self.merge_configs(config, global_config);
        }

        // Load project-specific configuration if available
        if let Some(project_config) = self.load_project_config().await? {
            config = self.merge_configs(config, project_config);
        }

        Ok(config)
    }

    /// Load global configuration from XDG directories.
    async fn load_global_config(&self) -> Result<Option<EvaluatorConfig>, ConfigError> {
        // Try TOML first
        if let Some(config) = self.global_config.load::<EvaluatorConfig>().await? {
            return Ok(Some(config));
        }

        // Try JSON
        let json_config = XdgConfig::new("ligature", "eval.json")?;
        if let Some(config) = json_config.load::<EvaluatorConfig>().await? {
            return Ok(Some(config));
        }

        // Try YAML
        let yaml_config = XdgConfig::new("ligature", "eval.yaml")?;
        if let Some(config) = yaml_config.load::<EvaluatorConfig>().await? {
            return Ok(Some(config));
        }

        Ok(None)
    }

    /// Load project-specific configuration.
    async fn load_project_config(&self) -> Result<Option<EvaluatorConfig>, ConfigError> {
        let project_config_path = match &self.project_config_path {
            Some(path) => path,
            None => return Ok(None),
        };

        if !project_config_path.exists() {
            return Ok(None);
        }

        let content = tokio::fs::read_to_string(project_config_path)
            .await
            .map_err(|e| ConfigError::ReadError {
                path: project_config_path.display().to_string(),
                source: e,
            })?;

        // Try to parse as TOML
        if let Ok(config) = toml::from_str::<EvaluatorConfig>(&content) {
            return Ok(Some(config));
        }

        // Try to parse as JSON
        if let Ok(config) = serde_json::from_str::<EvaluatorConfig>(&content) {
            return Ok(Some(config));
        }

        // Try to parse as YAML
        if let Ok(config) = serde_yaml::from_str::<EvaluatorConfig>(&content) {
            return Ok(Some(config));
        }

        Err(ConfigError::ParseError {
            path: project_config_path.display().to_string(),
            message: "Failed to parse configuration file as TOML, JSON, or YAML".to_string(),
        })
    }

    /// Merge two configurations, with the second taking precedence.
    fn merge_configs(
        &self,
        base: EvaluatorConfig,
        override_config: EvaluatorConfig,
    ) -> EvaluatorConfig {
        EvaluatorConfig {
            cache: self.merge_cache_configs(base.cache, override_config.cache),
            performance: self
                .merge_performance_configs(base.performance, override_config.performance),
            memory: self.merge_memory_configs(base.memory, override_config.memory),
            debug: self.merge_debug_configs(base.debug, override_config.debug),
        }
    }

    fn merge_cache_configs(&self, base: CacheConfig, override_config: CacheConfig) -> CacheConfig {
        CacheConfig {
            enabled: override_config.enabled,
            max_size: override_config.max_size,
            max_memory_bytes: override_config.max_memory_bytes,
            warming: self.merge_warming_configs(base.warming, override_config.warming),
            cacheable_expressions: self.merge_cacheable_expressions(
                base.cacheable_expressions,
                override_config.cacheable_expressions,
            ),
        }
    }

    fn merge_warming_configs(
        &self,
        _base: CacheWarmingConfig,
        override_config: CacheWarmingConfig,
    ) -> CacheWarmingConfig {
        CacheWarmingConfig {
            enabled: override_config.enabled,
            max_expressions: override_config.max_expressions,
            warm_on_module_load: override_config.warm_on_module_load,
        }
    }

    fn merge_cacheable_expressions(
        &self,
        _base: CacheableExpressions,
        override_config: CacheableExpressions,
    ) -> CacheableExpressions {
        CacheableExpressions {
            literals: override_config.literals,
            variables: override_config.variables,
            binary_ops: override_config.binary_ops,
            unary_ops: override_config.unary_ops,
            field_access: override_config.field_access,
            applications: override_config.applications,
            let_expressions: override_config.let_expressions,
            records: override_config.records,
            unions: override_config.unions,
            matches: override_config.matches,
            if_expressions: override_config.if_expressions,
        }
    }

    fn merge_performance_configs(
        &self,
        base: PerformanceConfig,
        override_config: PerformanceConfig,
    ) -> PerformanceConfig {
        PerformanceConfig {
            tail_call_optimization: override_config.tail_call_optimization,
            stack_based_evaluation: override_config.stack_based_evaluation,
            value_optimization: override_config.value_optimization,
            max_stack_depth: override_config.max_stack_depth,
            env_pool_size: override_config.env_pool_size,
            value_pool_size: override_config.value_pool_size,
            advanced: self
                .merge_advanced_optimization_configs(base.advanced, override_config.advanced),
            parallel: self
                .merge_parallel_evaluation_configs(base.parallel, override_config.parallel),
            memory_management: self.merge_memory_management_configs(
                base.memory_management,
                override_config.memory_management,
            ),
        }
    }

    fn merge_advanced_optimization_configs(
        &self,
        _base: AdvancedOptimizationConfig,
        override_config: AdvancedOptimizationConfig,
    ) -> AdvancedOptimizationConfig {
        AdvancedOptimizationConfig {
            function_inlining: override_config.function_inlining,
            max_inline_size: override_config.max_inline_size,
            closure_optimization: override_config.closure_optimization,
            minimal_capture: override_config.minimal_capture,
            advanced_tail_call_detection: override_config.advanced_tail_call_detection,
            pattern_based_tco: override_config.pattern_based_tco,
            context_sensitive_tco: override_config.context_sensitive_tco,
            nested_function_tco: override_config.nested_function_tco,
        }
    }

    fn merge_parallel_evaluation_configs(
        &self,
        _base: ParallelEvaluationConfig,
        override_config: ParallelEvaluationConfig,
    ) -> ParallelEvaluationConfig {
        ParallelEvaluationConfig {
            enabled: override_config.enabled,
            worker_threads: override_config.worker_threads,
            work_stealing: override_config.work_stealing,
            min_complexity: override_config.min_complexity,
            adaptive_parallelism: override_config.adaptive_parallelism,
            thread_safe_values: override_config.thread_safe_values,
        }
    }

    fn merge_memory_management_configs(
        &self,
        _base: MemoryManagementConfig,
        override_config: MemoryManagementConfig,
    ) -> MemoryManagementConfig {
        MemoryManagementConfig {
            generational_gc: override_config.generational_gc,
            memory_compaction: override_config.memory_compaction,
            object_pooling: override_config.object_pooling,
            young_gen_size: override_config.young_gen_size,
            old_gen_size: override_config.old_gen_size,
            gc_frequency: override_config.gc_frequency,
            defragmentation: override_config.defragmentation,
            pre_allocation: override_config.pre_allocation,
        }
    }

    fn merge_memory_configs(
        &self,
        _base: MemoryConfig,
        override_config: MemoryConfig,
    ) -> MemoryConfig {
        MemoryConfig {
            monitoring: override_config.monitoring,
            eviction_threshold_percent: override_config.eviction_threshold_percent,
            max_evaluation_memory_bytes: override_config.max_evaluation_memory_bytes,
            gc_frequency: override_config.gc_frequency,
        }
    }

    fn merge_debug_configs(&self, _base: DebugConfig, override_config: DebugConfig) -> DebugConfig {
        DebugConfig {
            logging: override_config.logging,
            profiling: override_config.profiling,
            cache_statistics: override_config.cache_statistics,
            memory_tracking: override_config.memory_tracking,
            log_level: override_config.log_level,
        }
    }

    /// Save the default configuration to a file.
    pub async fn save_default_config(&self, format: ConfigFormat) -> Result<PathBuf, ConfigError> {
        let config = EvaluatorConfig::default();

        match format {
            ConfigFormat::Toml => {
                let content =
                    toml::to_string(&config).map_err(|e| ConfigError::SerializeError {
                        source: Box::new(e),
                    })?;
                self.global_config
                    .save_to("eval.toml", &content)
                    .await
                    .map_err(|e| ConfigError::SaveError { source: e })?;
                Ok(PathBuf::from("eval.toml"))
            }
            ConfigFormat::Json => {
                let content = serde_json::to_string_pretty(&config).map_err(|e| {
                    ConfigError::SerializeError {
                        source: Box::new(e),
                    }
                })?;
                self.global_config
                    .save_to("eval.json", &content)
                    .await
                    .map_err(|e| ConfigError::SaveError { source: e })?;
                Ok(PathBuf::from("eval.json"))
            }
            ConfigFormat::Yaml => {
                let content =
                    serde_yaml::to_string(&config).map_err(|e| ConfigError::SerializeError {
                        source: Box::new(e),
                    })?;
                self.global_config
                    .save_to("eval.yaml", &content)
                    .await
                    .map_err(|e| ConfigError::SaveError { source: e })?;
                Ok(PathBuf::from("eval.yaml"))
            }
        }
    }
}

/// Supported configuration formats.
#[derive(Debug, Clone, Copy)]
pub enum ConfigFormat {
    Toml,
    Json,
    Yaml,
}

/// Configuration error types.
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("XDG config error: {0}")]
    XdgError(#[from] XdgError),

    #[error("Failed to read config file {path}: {source}")]
    ReadError {
        path: String,
        source: std::io::Error,
    },

    #[error("Failed to parse config file {path}: {message}")]
    ParseError { path: String, message: String },

    #[error("Failed to serialize config: {source}")]
    SerializeError {
        source: Box<dyn std::error::Error + Send + Sync>,
    },

    #[error("Failed to save config: {source}")]
    SaveError { source: XdgError },
}

// Default value functions
fn default_enable_caching() -> bool {
    true
}
fn default_cache_size() -> usize {
    1000
}
fn default_cache_memory() -> usize {
    1024 * 1024
} // 1MB
fn default_enable_warming() -> bool {
    false
}
fn default_warming_size() -> usize {
    100
}
fn default_warm_on_load() -> bool {
    false
}

fn default_cache_literals() -> bool {
    true
}
fn default_cache_variables() -> bool {
    true
}
fn default_cache_binary_ops() -> bool {
    true
}
fn default_cache_unary_ops() -> bool {
    true
}
fn default_cache_field_access() -> bool {
    true
}
fn default_cache_applications() -> bool {
    false
}
fn default_cache_let() -> bool {
    false
}
fn default_cache_records() -> bool {
    false
}
fn default_cache_unions() -> bool {
    false
}
fn default_cache_matches() -> bool {
    false
}
fn default_cache_if() -> bool {
    false
}

fn default_enable_tco() -> bool {
    true
}
fn default_enable_stack_eval() -> bool {
    true
}
fn default_enable_value_optimization() -> bool {
    true
}
fn default_max_stack_depth() -> usize {
    10000
}
fn default_env_pool_size() -> usize {
    100
}
fn default_value_pool_size() -> usize {
    1000
}

fn default_enable_memory_monitoring() -> bool {
    false
}
fn default_memory_threshold() -> f64 {
    80.0
}
fn default_max_evaluation_memory() -> usize {
    100 * 1024 * 1024
} // 100MB
fn default_gc_frequency() -> usize {
    1000
}

fn default_enable_logging() -> bool {
    false
}
fn default_enable_profiling() -> bool {
    false
}
fn default_enable_cache_stats() -> bool {
    true
}
fn default_enable_memory_tracking() -> bool {
    false
}
fn default_log_level() -> LogLevel {
    LogLevel::Info
}

fn default_enable_function_inlining() -> bool {
    true
}
fn default_max_inline_size() -> usize {
    10
}
fn default_enable_closure_optimization() -> bool {
    true
}
fn default_enable_minimal_capture() -> bool {
    false
}
fn default_enable_advanced_tco() -> bool {
    true
}
fn default_enable_pattern_tco() -> bool {
    true
}
fn default_enable_context_tco() -> bool {
    true
}
fn default_enable_nested_tco() -> bool {
    true
}

fn default_enable_parallel_eval() -> bool {
    false
}
fn default_worker_threads() -> usize {
    4
}
fn default_enable_work_stealing() -> bool {
    true
}
fn default_min_parallel_complexity() -> usize {
    10
}
fn default_enable_adaptive_parallelism() -> bool {
    true
}
fn default_enable_thread_safe_values() -> bool {
    true
}

fn default_enable_generational_gc() -> bool {
    true
}
fn default_enable_memory_compaction() -> bool {
    true
}
fn default_enable_object_pooling() -> bool {
    true
}
fn default_young_gen_size() -> usize {
    10 * 1024 * 1024
} // 10MB
fn default_old_gen_size() -> usize {
    90 * 1024 * 1024
} // 90MB
fn default_enable_defragmentation() -> bool {
    true
}
fn default_enable_pre_allocation() -> bool {
    true
}
