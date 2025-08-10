//! Main evaluator for the Ligature language.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, VecDeque};
use std::hash::{Hash, Hasher};
use std::path::PathBuf;

use ligature_ast::{BinaryOperator, Expr, ExprKind, Literal, Program, Span, Type, UnaryOperator};
use ligature_error::{StandardError, StandardResult};

use crate::advanced_optimizations::{
    AdvancedTailCallDetector, ClosureCaptureOptimizer, FunctionInliner, GenerationalGC,
    OptimizedEvaluator, ParallelEvaluator,
};
use crate::config::{ConfigFormat, EvaluatorConfig, EvaluatorConfigManager};
use crate::environment::EvaluationEnvironment;
use crate::resolver::ModuleResolver;
use crate::validation::{ValidationEngine, ValidationResult, ValidationStats};
use crate::value::{
    Value, ValueInterner, ValueInternerStats, ValueKind, ValueOptimizationStats, ValuePool,
};

/// Type alias for union components
type UnionComponents<'a> = (&'a str, Option<&'a Value>);

/// Cache key that includes both expression and environment state
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CacheKey {
    /// Hash of the expression structure
    expr_hash: u64,
    /// Hash of the relevant environment bindings
    env_hash: u64,
    /// Expression depth for cache priority
    depth: usize,
}

impl CacheKey {
    fn new(expr: &Expr, env: &EvaluationEnvironment, depth: usize) -> Self {
        let mut hasher = DefaultHasher::new();
        Self::hash_expr(expr, &mut hasher);
        let expr_hash = hasher.finish();

        let mut env_hasher = DefaultHasher::new();
        Self::hash_environment(env, &mut env_hasher);
        let env_hash = env_hasher.finish();

        Self {
            expr_hash,
            env_hash,
            depth,
        }
    }

    fn hash_expr(expr: &Expr, hasher: &mut DefaultHasher) {
        match &expr.kind {
            ExprKind::Literal(literal) => {
                hasher.write_u8(0);
                match literal {
                    Literal::Unit => hasher.write_u8(0),
                    Literal::Boolean(b) => {
                        hasher.write_u8(1);
                        hasher.write_u8(*b as u8);
                    }
                    Literal::String(s) => {
                        hasher.write_u8(2);
                        hasher.write(s.as_bytes());
                    }
                    Literal::Integer(i) => {
                        hasher.write_u8(3);
                        hasher.write_i64(*i);
                    }
                    Literal::Float(f) => {
                        hasher.write_u8(4);
                        hasher.write_u64(f.to_bits());
                    }
                    // List is not a valid Literal variant, but add for completeness
                    #[allow(unreachable_patterns)]
                    Literal::List(_) => hasher.write_u8(5),
                }
            }
            ExprKind::Variable(name) => {
                hasher.write_u8(1);
                hasher.write(name.as_bytes());
            }
            ExprKind::Application { function, argument } => {
                hasher.write_u8(2);
                Self::hash_expr(function, hasher);
                Self::hash_expr(argument, hasher);
            }
            ExprKind::Abstraction {
                parameter, body, ..
            } => {
                hasher.write_u8(3);
                hasher.write(parameter.as_bytes());
                Self::hash_expr(body, hasher);
            }
            ExprKind::Let { name, value, body } => {
                hasher.write_u8(4);
                hasher.write(name.as_bytes());
                Self::hash_expr(value, hasher);
                Self::hash_expr(body, hasher);
            }
            ExprKind::Record { fields } => {
                hasher.write_u8(5);
                hasher.write_usize(fields.len());
                for field in fields {
                    hasher.write(field.name.as_bytes());
                    Self::hash_expr(&field.value, hasher);
                }
            }
            ExprKind::FieldAccess { record, field } => {
                hasher.write_u8(6);
                Self::hash_expr(record, hasher);
                hasher.write(field.as_bytes());
            }
            ExprKind::Union { variant, value } => {
                hasher.write_u8(7);
                hasher.write(variant.as_bytes());
                if let Some(val) = value {
                    Self::hash_expr(val, hasher);
                } else {
                    hasher.write_u8(0);
                }
            }
            ExprKind::Match { scrutinee, cases } => {
                hasher.write_u8(8);
                Self::hash_expr(scrutinee, hasher);
                hasher.write_usize(cases.len());
                for case in cases {
                    // Hash pattern structure (simplified)
                    match &case.pattern {
                        ligature_ast::Pattern::Wildcard => hasher.write_u8(0),
                        ligature_ast::Pattern::Variable(name) => {
                            hasher.write_u8(1);
                            hasher.write(name.as_bytes());
                        }
                        ligature_ast::Pattern::Union { variant, value: _ } => {
                            hasher.write_u8(2);
                            hasher.write(variant.as_bytes());
                        }
                        _ => hasher.write_u8(255),
                    }
                    Self::hash_expr(&case.expression, hasher);
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                hasher.write_u8(9);
                Self::hash_expr(condition, hasher);
                Self::hash_expr(then_branch, hasher);
                Self::hash_expr(else_branch, hasher);
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                hasher.write_u8(10);
                hasher.write_u8(operator.clone() as u8);
                Self::hash_expr(left, hasher);
                Self::hash_expr(right, hasher);
            }
            ExprKind::UnaryOp { operator, operand } => {
                hasher.write_u8(11);
                hasher.write_u8(operator.clone() as u8);
                Self::hash_expr(operand, hasher);
            }
            ExprKind::Annotated { expression, .. } => {
                hasher.write_u8(12);
                Self::hash_expr(expression, hasher);
            }
        }
    }

    fn hash_environment(env: &EvaluationEnvironment, hasher: &mut DefaultHasher) {
        // Hash current bindings
        let bindings = env.current_bindings();
        hasher.write_usize(bindings.len());
        for (name, value) in bindings {
            hasher.write(name.as_bytes());
            // Hash value type and basic info (not full value to avoid recursion)
            match &value.kind {
                ValueKind::Unit => hasher.write_u8(0),
                ValueKind::Boolean(b) => {
                    hasher.write_u8(1);
                    hasher.write_u8(**b as u8);
                }
                ValueKind::String(s) => {
                    hasher.write_u8(2);
                    hasher.write(s.as_bytes());
                }
                ValueKind::Integer(i) => {
                    hasher.write_u8(3);
                    hasher.write_i64(**i);
                }
                ValueKind::Float(f) => {
                    hasher.write_u8(4);
                    hasher.write_u64((**f).to_bits());
                }
                _ => hasher.write_u8(255), // Complex types get a generic hash
            }
        }
    }
}

/// Cache entry with metadata for LRU eviction
#[derive(Debug, Clone)]
struct CacheEntry {
    value: Value,
    access_count: usize,
    last_access: std::time::Instant,
    size_estimate: usize,
}

impl CacheEntry {
    fn new(value: Value) -> Self {
        Self {
            value,
            access_count: 1,
            last_access: std::time::Instant::now(),
            size_estimate: 1, // Simplified size estimation
        }
    }

    fn access(&mut self) {
        self.access_count += 1;
        self.last_access = std::time::Instant::now();
    }

    #[allow(dead_code)]
    fn priority(&self) -> f64 {
        // Priority based on access count and recency
        let recency = self.last_access.elapsed().as_millis() as f64;
        self.access_count as f64 / (recency + 1.0)
    }
}

/// Advanced expression cache with LRU eviction and environment awareness
#[derive(Debug)]
struct ExpressionCache {
    /// Main cache storage
    entries: HashMap<CacheKey, CacheEntry>,
    /// LRU queue for eviction
    lru_queue: VecDeque<CacheKey>,
    /// Maximum cache size in entries
    max_size: usize,
    /// Current cache size
    current_size: usize,
    /// Maximum memory usage in bytes (estimated)
    max_memory: usize,
    /// Current memory usage
    current_memory: usize,
    /// Cache warming queue
    warming_queue: VecDeque<CacheKey>,
    /// Statistics
    stats: CacheStats,
}

impl ExpressionCache {
    fn new(max_size: usize, max_memory: usize) -> Self {
        Self {
            entries: HashMap::new(),
            lru_queue: VecDeque::new(),
            max_size,
            current_size: 0,
            max_memory,
            current_memory: 0,
            warming_queue: VecDeque::new(),
            stats: CacheStats::default(),
        }
    }

    fn get(&mut self, key: &CacheKey) -> Option<Value> {
        if let Some(entry) = self.entries.get_mut(key) {
            entry.access();
            self.stats.hits += 1;

            // Move to front of LRU queue
            if let Some(pos) = self.lru_queue.iter().position(|k| k == key) {
                self.lru_queue.remove(pos);
            }
            self.lru_queue.push_front(key.clone());

            Some(entry.value.clone())
        } else {
            self.stats.misses += 1;
            None
        }
    }

    fn put(&mut self, key: CacheKey, value: Value) {
        let size_estimate = self.estimate_value_size(&value);

        // Check if we need to evict entries
        while (self.current_size >= self.max_size
            || self.current_memory + size_estimate > self.max_memory)
            && !self.entries.is_empty()
        {
            self.evict_lru_entry();
        }

        let entry = CacheEntry::new(value);
        self.entries.insert(key.clone(), entry);
        self.lru_queue.push_front(key);
        self.current_size += 1;
        self.current_memory += size_estimate;
    }

    fn evict_lru_entry(&mut self) {
        if let Some(key) = self.lru_queue.pop_back() {
            if let Some(entry) = self.entries.remove(&key) {
                self.current_memory -= entry.size_estimate;
                self.current_size -= 1;
                self.stats.evictions += 1;
            }
        }
    }

    #[allow(dead_code)]
    #[allow(clippy::type_complexity)]
    fn warm_cache(&mut self, expressions: Vec<(&Expr, &EvaluationEnvironment, usize)>) {
        for (expr, env, depth) in expressions {
            let key = CacheKey::new(expr, env, depth);
            self.warming_queue.push_back(key);
        }
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.lru_queue.clear();
        self.warming_queue.clear();
        self.current_size = 0;
        self.current_memory = 0;
        self.stats.reset();
    }

    fn stats(&self) -> &CacheStats {
        &self.stats
    }

    fn stats_mut(&mut self) -> &mut CacheStats {
        &mut self.stats
    }

    fn size(&self) -> usize {
        self.current_size
    }

    fn memory_usage(&self) -> usize {
        self.current_memory
    }

    fn estimate_value_size(&self, value: &Value) -> usize {
        // Estimate memory usage of a value
        match &value.kind {
            ValueKind::Unit => 8,
            ValueKind::Boolean(_) => 16,
            ValueKind::String(s) => 24 + s.len(),
            ValueKind::Integer(_) => 16,
            ValueKind::Float(_) => 16,
            ValueKind::Record(fields) => 24 + fields.len() * 32,
            ValueKind::List(elements) => 24 + elements.len() * 16,
            ValueKind::Function { .. } => 48,
            ValueKind::Closure { .. } => 64,
            ValueKind::Union { .. } => 32,
            ValueKind::Module { .. } => 48,
        }
    }
}

/// Statistics for cache performance monitoring.
#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    /// Total number of cache hits
    pub hits: usize,
    /// Total number of cache misses
    pub misses: usize,
    /// Total number of cache evictions
    pub evictions: usize,
    /// Number of tail call optimizations performed
    pub tail_calls: usize,
    /// Number of stack-based evaluations performed
    pub stack_evals: usize,
    /// Number of environment pool reuses
    pub env_pool_reuses: usize,
    /// Number of value pool acquisitions
    pub value_pool_acquisitions: usize,
    /// Number of value pool releases
    pub value_pool_releases: usize,
    /// Value interner statistics
    pub value_interner_stats: Option<ValueInternerStats>,
    /// Cache warming statistics
    pub warming_hits: usize,
    pub warming_misses: usize,
    /// Expression complexity statistics
    pub simple_expressions: usize,
    pub complex_expressions: usize,
    /// Environment dependency statistics
    pub env_dependent: usize,
    pub env_independent: usize,
}

impl CacheStats {
    /// Get the cache hit rate as a percentage.
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            (self.hits as f64 / total as f64) * 100.0
        }
    }

    /// Get the value pool utilization rate as a percentage.
    pub fn value_pool_utilization(&self) -> f64 {
        if let Some(stats) = &self.value_interner_stats {
            let total =
                stats.string_count + stats.integer_count + stats.float_count + stats.boolean_count;
            if total == 0 {
                0.0
            } else {
                (total as f64 / 1000.0) * 100.0 // Assuming 1000 as max capacity
            }
        } else {
            0.0
        }
    }

    /// Get warming hit rate
    pub fn warming_hit_rate(&self) -> f64 {
        let total = self.warming_hits + self.warming_misses;
        if total == 0 {
            0.0
        } else {
            (self.warming_hits as f64 / total as f64) * 100.0
        }
    }

    /// Reset all statistics.
    pub fn reset(&mut self) {
        self.hits = 0;
        self.misses = 0;
        self.evictions = 0;
        self.tail_calls = 0;
        self.stack_evals = 0;
        self.env_pool_reuses = 0;
        self.value_pool_acquisitions = 0;
        self.value_pool_releases = 0;
        self.value_interner_stats = None;
        self.warming_hits = 0;
        self.warming_misses = 0;
        self.simple_expressions = 0;
        self.complex_expressions = 0;
        self.env_dependent = 0;
        self.env_independent = 0;
    }
}

/// Strategy for resolving import binding conflicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportConflictStrategy {
    /// Report binding conflicts as errors.
    Error,
    /// Warn about binding conflicts but continue.
    Warn,
    /// Override existing bindings with new ones.
    Override,
    /// Skip conflicting bindings.
    Skip,
}

/// Call frame for stack-based evaluation.
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct CallFrame {
    /// The expression being evaluated
    expr: Expr,
    /// Current environment for this frame
    environment: EvaluationEnvironment,
    /// Arguments passed to this function call
    arguments: Vec<Value>,
    /// Whether this is a tail call
    is_tail_call: bool,
}

/// Environment pool for reducing cloning overhead.
#[derive(Debug)]
struct EnvironmentPool {
    /// Pool of available environments
    available: VecDeque<EvaluationEnvironment>,
    /// Maximum pool size
    max_size: usize,
    /// Current pool size
    current_size: usize,
}

impl EnvironmentPool {
    /// Create a new environment pool.
    fn new(max_size: usize) -> Self {
        Self {
            available: VecDeque::new(),
            max_size,
            current_size: 0,
        }
    }

    /// Get an environment from the pool or create a new one.
    fn acquire(&mut self, parent: Option<EvaluationEnvironment>) -> EvaluationEnvironment {
        if let Some(mut env) = self.available.pop_front() {
            // Reuse existing environment
            env.reset_with_parent(parent);
            env
        } else {
            // Create new environment
            self.current_size += 1;
            match parent {
                Some(parent_env) => EvaluationEnvironment::with_parent(parent_env),
                None => EvaluationEnvironment::new(),
            }
        }
    }

    /// Return an environment to the pool.
    fn release(&mut self, mut env: EvaluationEnvironment) {
        if self.available.len() < self.max_size {
            env.clear();
            self.available.push_back(env);
        } else {
            // Pool is full, drop the environment
            self.current_size -= 1;
        }
    }

    /// Get pool statistics.
    fn stats(&self) -> (usize, usize) {
        (self.available.len(), self.current_size)
    }
}

/// Main evaluator for the Ligature language with optimized function call architecture.
pub struct Evaluator {
    pub environment: EvaluationEnvironment,
    module_resolver: ModuleResolver,
    conflict_strategy: ImportConflictStrategy,
    /// Advanced expression cache with environment awareness
    expression_cache: ExpressionCache,
    /// Environment pool for reducing cloning overhead
    env_pool: EnvironmentPool,
    /// Call stack for stack-based evaluation
    #[allow(dead_code)]
    call_stack: Vec<CallFrame>,
    /// Maximum call stack depth
    max_stack_depth: usize,
    /// Whether to enable tail call optimization
    enable_tco: bool,
    /// Whether to enable stack-based evaluation for simple functions
    enable_stack_eval: bool,
    /// Value interner for caching frequently used values
    value_interner: ValueInterner,
    /// Value pool for frequently used values
    value_pool: ValuePool,
    /// Whether to enable value optimization
    enable_value_optimization: bool,
    /// Whether to enable advanced caching
    enable_caching: bool,
    /// Expression depth tracking for cache keys
    current_depth: usize,
    /// Configuration for the evaluator
    config: EvaluatorConfig,
    /// Advanced tail call detector
    advanced_tail_call_detector: AdvancedTailCallDetector,
    /// Function inliner
    function_inliner: FunctionInliner,
    /// Closure capture optimizer
    closure_capture_optimizer: ClosureCaptureOptimizer,
    /// Parallel evaluator
    parallel_evaluator: Option<ParallelEvaluator>,
    /// Generational garbage collector
    generational_gc: Option<GenerationalGC>,
    /// Optimized evaluator for function calls
    optimized_evaluator: OptimizedEvaluator,
    /// Runtime validation engine for constraint-based validation
    validation_engine: ValidationEngine,
}

impl Evaluator {
    /// Create a new evaluator.
    pub fn new() -> Self {
        let config = EvaluatorConfig::default();
        Self {
            environment: EvaluationEnvironment::new(),
            module_resolver: ModuleResolver::new(),
            conflict_strategy: ImportConflictStrategy::Skip,
            expression_cache: ExpressionCache::new(1000, 1024 * 1024), // 1000 entries, 1MB memory
            env_pool: EnvironmentPool::new(100), // Pool up to 100 environments
            call_stack: Vec::new(),
            max_stack_depth: 10000, // Prevent stack overflow
            enable_tco: true,
            enable_stack_eval: true,
            value_interner: ValueInterner::new(),
            value_pool: ValuePool::new(1000), // Pool up to 1000 values
            enable_value_optimization: true,
            enable_caching: true,
            current_depth: 0,
            config: config.clone(),
            advanced_tail_call_detector: AdvancedTailCallDetector::new(),
            function_inliner: FunctionInliner::new(),
            closure_capture_optimizer: ClosureCaptureOptimizer::new(),
            parallel_evaluator: if config.performance.parallel.enabled {
                Some(ParallelEvaluator::new(4)) // Use 4 worker threads
            } else {
                None
            },
            generational_gc: if config.performance.memory_management.generational_gc {
                Some(GenerationalGC::new())
            } else {
                None
            },
            optimized_evaluator: OptimizedEvaluator::new(),
            validation_engine: ValidationEngine::new(),
        }
    }

    /// Create a new evaluator with configuration.
    pub fn with_config(config: EvaluatorConfig) -> Self {
        Self {
            environment: EvaluationEnvironment::new(),
            module_resolver: ModuleResolver::new(),
            conflict_strategy: ImportConflictStrategy::Skip,
            expression_cache: ExpressionCache::new(
                config.cache.max_size,
                config.cache.max_memory_bytes,
            ),
            env_pool: EnvironmentPool::new(config.performance.env_pool_size),
            call_stack: Vec::new(),
            max_stack_depth: config.performance.max_stack_depth,
            enable_tco: config.performance.tail_call_optimization,
            enable_stack_eval: config.performance.stack_based_evaluation,
            value_interner: ValueInterner::new(),
            value_pool: ValuePool::new(config.performance.value_pool_size),
            enable_value_optimization: config.performance.value_optimization,
            enable_caching: config.cache.enabled,
            current_depth: 0,
            config: config.clone(),
            advanced_tail_call_detector: AdvancedTailCallDetector::new(),
            function_inliner: FunctionInliner::new(),
            closure_capture_optimizer: ClosureCaptureOptimizer::new(),
            parallel_evaluator: if config.performance.parallel.enabled {
                Some(ParallelEvaluator::new(4)) // Use 4 worker threads
            } else {
                None
            },
            generational_gc: if config.performance.memory_management.generational_gc {
                Some(GenerationalGC::new())
            } else {
                None
            },
            optimized_evaluator: OptimizedEvaluator::new(),
            validation_engine: ValidationEngine::new(),
        }
    }

    /// Create a new evaluator with configuration loaded from files.
    pub async fn with_config_from_files(
        project_config_path: Option<PathBuf>,
    ) -> StandardResult<Self> {
        let config_manager = EvaluatorConfigManager::new()?;
        let config_manager = if let Some(path) = project_config_path {
            config_manager.with_project_config(path)
        } else {
            config_manager
        };

        let config = config_manager.load_config().await?;
        Ok(Self::with_config(config))
    }

    /// Load configuration from files and apply it.
    pub async fn load_config(
        &mut self,
        project_config_path: Option<PathBuf>,
    ) -> StandardResult<()> {
        let config_manager = EvaluatorConfigManager::new()?;
        let config_manager = if let Some(path) = project_config_path {
            config_manager.with_project_config(path)
        } else {
            config_manager
        };

        let config = config_manager.load_config().await?;
        self.apply_config(config);
        Ok(())
    }

    /// Apply configuration to the evaluator.
    pub fn apply_config(&mut self, config: EvaluatorConfig) {
        self.config = config.clone();

        // Apply cache configuration
        self.enable_caching = config.cache.enabled;
        self.expression_cache =
            ExpressionCache::new(config.cache.max_size, config.cache.max_memory_bytes);

        // Apply performance configuration
        self.enable_tco = config.performance.tail_call_optimization;
        self.enable_stack_eval = config.performance.stack_based_evaluation;
        self.enable_value_optimization = config.performance.value_optimization;
        self.max_stack_depth = config.performance.max_stack_depth;

        // Recreate pools with new sizes
        self.env_pool = EnvironmentPool::new(config.performance.env_pool_size);
        self.value_pool = ValuePool::new(config.performance.value_pool_size);
    }

    /// Get the current configuration.
    pub fn config(&self) -> &EvaluatorConfig {
        &self.config
    }

    /// Update the configuration and apply changes.
    pub fn update_config(&mut self, config: EvaluatorConfig) {
        self.apply_config(config);
    }

    /// Save the current configuration to a file.
    pub async fn save_config(&self, format: ConfigFormat) -> StandardResult<PathBuf> {
        let config_manager = EvaluatorConfigManager::new()?;
        config_manager.save_default_config(format).await
    }

    /// Create a new evaluator with a module resolver.
    pub fn with_resolver(module_resolver: ModuleResolver) -> Self {
        let config = EvaluatorConfig::default();
        Self {
            environment: EvaluationEnvironment::new(),
            module_resolver,
            conflict_strategy: ImportConflictStrategy::Skip,
            expression_cache: ExpressionCache::new(1000, 1024 * 1024),
            env_pool: EnvironmentPool::new(100),
            call_stack: Vec::new(),
            max_stack_depth: 10000,
            enable_tco: true,
            enable_stack_eval: true,
            value_interner: ValueInterner::new(),
            value_pool: ValuePool::new(1000),
            enable_value_optimization: true,
            enable_caching: true,
            current_depth: 0,
            config: config.clone(),
            advanced_tail_call_detector: AdvancedTailCallDetector::new(),
            function_inliner: FunctionInliner::new(),
            closure_capture_optimizer: ClosureCaptureOptimizer::new(),
            parallel_evaluator: None,
            generational_gc: None,
            optimized_evaluator: OptimizedEvaluator::new(),
            validation_engine: ValidationEngine::new(),
        }
    }

    /// Create a new evaluator with a specific conflict resolution strategy.
    pub fn with_conflict_strategy(conflict_strategy: ImportConflictStrategy) -> Self {
        let config = EvaluatorConfig::default();
        Self {
            environment: EvaluationEnvironment::new(),
            module_resolver: ModuleResolver::new(),
            conflict_strategy,
            expression_cache: ExpressionCache::new(1000, 1024 * 1024),
            env_pool: EnvironmentPool::new(100),
            call_stack: Vec::new(),
            max_stack_depth: 10000,
            enable_tco: true,
            enable_stack_eval: true,
            value_interner: ValueInterner::new(),
            value_pool: ValuePool::new(1000),
            enable_value_optimization: true,
            enable_caching: true,
            current_depth: 0,
            config: config.clone(),
            advanced_tail_call_detector: AdvancedTailCallDetector::new(),
            function_inliner: FunctionInliner::new(),
            closure_capture_optimizer: ClosureCaptureOptimizer::new(),
            parallel_evaluator: None,
            generational_gc: None,
            optimized_evaluator: OptimizedEvaluator::new(),
            validation_engine: ValidationEngine::new(),
        }
    }

    /// Enable or disable tail call optimization.
    pub fn set_tail_call_optimization(&mut self, enable: bool) {
        self.enable_tco = enable;
    }

    /// Enable or disable stack-based evaluation.
    pub fn set_stack_based_evaluation(&mut self, enable: bool) {
        self.enable_stack_eval = enable;
    }

    /// Set the maximum call stack depth.
    pub fn set_max_stack_depth(&mut self, depth: usize) {
        self.max_stack_depth = depth;
    }

    /// Get environment pool statistics.
    pub fn env_pool_stats(&self) -> (usize, usize) {
        self.env_pool.stats()
    }

    /// Set whether to enable value optimization.
    pub fn set_value_optimization(&mut self, enable: bool) {
        self.enable_value_optimization = enable;
    }

    /// Get value pool statistics.
    pub fn value_pool_stats(&self) -> (usize, usize) {
        self.value_pool.stats()
    }

    /// Get value interner statistics.
    pub fn value_interner_stats(&self) -> ValueInternerStats {
        self.value_interner.stats()
    }

    /// Update value optimization statistics.
    pub fn update_value_optimization_stats(&mut self) {
        let interner_stats = self.value_interner.stats();
        self.expression_cache.stats_mut().value_interner_stats = Some(interner_stats);
    }

    /// Invalidate the evaluation cache when environment changes.
    fn invalidate_cache(&mut self) {
        self.expression_cache.clear();
    }

    /// Get cache statistics.
    pub fn cache_stats(&self) -> &CacheStats {
        self.expression_cache.stats()
    }

    /// Set the cache size limit.
    pub fn set_cache_size_limit(&mut self, limit: usize) {
        // This would need to be implemented in ExpressionCache
        // For now, we'll create a new cache with the new limit
        let current_stats = self.expression_cache.stats().clone();
        self.expression_cache = ExpressionCache::new(limit, 1024 * 1024);
        // Restore stats
        *self.expression_cache.stats_mut() = current_stats;
    }

    /// Get the current cache size limit.
    pub fn cache_size_limit(&self) -> usize {
        self.expression_cache.max_size
    }

    /// Get the current cache size.
    pub fn cache_size(&self) -> usize {
        self.expression_cache.size()
    }

    /// Clear the cache and reset statistics.
    pub fn clear_cache(&mut self) {
        self.expression_cache.clear();
    }

    /// Enable or disable caching.
    pub fn set_caching(&mut self, enable: bool) {
        self.enable_caching = enable;
    }

    /// Get cache memory usage.
    pub fn cache_memory_usage(&self) -> usize {
        self.expression_cache.memory_usage()
    }

    /// Set the conflict resolution strategy.
    pub fn set_conflict_strategy(&mut self, strategy: ImportConflictStrategy) {
        self.conflict_strategy = strategy;
    }

    /// Add a search path to the module resolver.
    pub fn add_search_path(&mut self, path: std::path::PathBuf) {
        self.module_resolver.add_search_path(path);
    }

    /// Add a register path to the module resolver.
    pub fn add_register_path(&mut self, path: std::path::PathBuf) {
        self.module_resolver.add_register_path(path);
    }

    /// Get a reference to the module resolver.
    pub fn module_resolver(&self) -> &ModuleResolver {
        &self.module_resolver
    }

    /// Get a mutable reference to the module resolver.
    pub fn module_resolver_mut(&mut self) -> &mut ModuleResolver {
        &mut self.module_resolver
    }

    /// Evaluate a complete program.
    pub fn evaluate_program(&mut self, program: &Program) -> StandardResult<Value> {
        for declaration in &program.declarations {
            self.evaluate_declaration(declaration)?;
        }
        Ok(Value::unit(Span::default()))
    }

    /// Evaluate a complete module.
    pub fn evaluate_module(&mut self, module: &ligature_ast::Program) -> StandardResult<Value> {
        for declaration in &module.declarations {
            self.evaluate_declaration(declaration)?;
        }

        let module_env = self.environment.clone();
        Ok(Value::module(
            "module".to_string(),
            module_env,
            Span::default(),
        ))
    }

    /// Evaluate a single expression.
    pub fn evaluate_expression(&mut self, expr: &Expr) -> StandardResult<Value> {
        self.evaluate_expression_internal(expr)
    }

    /// Evaluate a declaration.
    fn evaluate_declaration(
        &mut self,
        declaration: &ligature_ast::Declaration,
    ) -> StandardResult<()> {
        match &declaration.kind {
            ligature_ast::DeclarationKind::Value(value_decl) => {
                let value = self.evaluate_expression(&value_decl.value)?;
                self.environment.bind(value_decl.name.clone(), value);
                self.invalidate_cache();
            }
            ligature_ast::DeclarationKind::TypeAlias(_) => {}
            ligature_ast::DeclarationKind::TypeConstructor(_) => {}
            ligature_ast::DeclarationKind::Import(_) => {}
            ligature_ast::DeclarationKind::Export(_) => {}
            ligature_ast::DeclarationKind::TypeClass(_) => {}
            ligature_ast::DeclarationKind::Instance(_) => {}
        }
        Ok(())
    }

    /// Evaluate an import statement.
    #[allow(dead_code)]
    fn evaluate_import(&mut self, import: &ligature_ast::Import) -> StandardResult<()> {
        let module_value = self.module_resolver.resolve_module(&import.path)?;
        let module_name = import.alias.as_ref().unwrap_or(&import.path);

        self.environment
            .import_module(module_name.clone(), module_value.clone());

        if let Some(ref items) = import.items {
            self.import_selective_bindings(
                &import.path,
                &module_value,
                items,
                import.alias.as_ref(),
            )?;
        } else if import.alias.is_none() {
            self.import_module_bindings(&import.path, &module_value)?;
        }

        self.invalidate_cache();
        Ok(())
    }

    /// Import selective bindings from a module.
    #[allow(dead_code)]
    fn import_selective_bindings(
        &mut self,
        module_path: &str,
        module_value: &Value,
        items: &[ligature_ast::ImportItem],
        alias: Option<&String>,
    ) -> StandardResult<()> {
        if let Some((_, module_env)) = module_value.as_module() {
            for item in items {
                if let Some(value) = module_env.lookup(&item.name) {
                    let import_name = item.alias.as_ref().unwrap_or(&item.name);

                    if let Some(alias_name) = alias {
                        let prefixed_name = format!("{alias_name}.{import_name}");
                        self.handle_import_conflict(
                            &prefixed_name,
                            &value,
                            module_path,
                            &item.name,
                        )?;
                    } else {
                        self.handle_import_conflict(import_name, &value, module_path, &item.name)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Import all exported bindings from a module into the current environment.
    #[allow(dead_code)]
    fn import_module_bindings(
        &mut self,
        module_path: &str,
        module_value: &Value,
    ) -> StandardResult<()> {
        if let Some((_, module_env)) = module_value.as_module() {
            let bindings = module_env.current_bindings();
            for (name, value) in bindings {
                self.handle_import_conflict(name, value, module_path, name)?;
            }
        }
        Ok(())
    }

    /// Handle import binding conflicts according to the current strategy.
    pub fn handle_import_conflict(
        &mut self,
        name: &str,
        value: &Value,
        module_path: &str,
        original_name: &str,
    ) -> StandardResult<()> {
        if self.environment.is_bound(name) {
            match self.conflict_strategy {
                ImportConflictStrategy::Error => {
                    return Err(StandardError::Internal(format!(
                        "Import conflict: '{original_name}' from module '{module_path}' conflicts \
                         with existing binding"
                    )));
                }
                ImportConflictStrategy::Warn => {
                    return Ok(());
                }
                ImportConflictStrategy::Override => {
                    self.environment.bind(name.to_string(), value.clone());
                }
                ImportConflictStrategy::Skip => {
                    return Ok(());
                }
            }
        } else {
            self.environment.bind(name.to_string(), value.clone());
        }
        Ok(())
    }

    /// Internal expression evaluation implementation with caching and optimizations.
    fn evaluate_expression_internal(&mut self, expr: &Expr) -> StandardResult<Value> {
        // Check cache first if enabled
        if self.enable_caching {
            let key = CacheKey::new(expr, &self.environment, self.current_depth);
            if let Some(cached_value) = self.expression_cache.get(&key) {
                return Ok(cached_value);
            }
        }

        let result = match &expr.kind {
            ExprKind::Literal(literal) => self.evaluate_literal(literal),
            ExprKind::Variable(name) => self.evaluate_variable(name),
            ExprKind::Application { function, argument } => {
                self.evaluate_application_optimized(function, argument)
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type: _,
                body,
            } => self.evaluate_abstraction(parameter, body),
            ExprKind::Let { name, value, body } => self.evaluate_let(name, value, body),
            ExprKind::Record { fields } => self.evaluate_record(fields),
            ExprKind::FieldAccess { record, field } => self.evaluate_field_access(record, field),
            ExprKind::Union { variant, value } => {
                self.evaluate_union(variant, value.as_ref().map(|v| &**v))
            }
            ExprKind::Match { scrutinee, cases } => self.evaluate_match(scrutinee, cases),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.evaluate_if(condition, then_branch, else_branch),
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => self.evaluate_binary_op(operator, left, right),
            ExprKind::UnaryOp { operator, operand } => self.evaluate_unary_op(operator, operand),
            ExprKind::Annotated {
                expression,
                type_annotation: _,
            } => self.evaluate_expression_internal(expression),
        };

        if let Ok(ref value) = result {
            self.cache_result(expr, value);
        }

        result
    }

    /// Optimized function application with environment pooling and tail call optimization.
    fn evaluate_application_optimized(
        &mut self,
        function: &Expr,
        argument: &Expr,
    ) -> StandardResult<Value> {
        // Fast path for simple function applications
        if self.enable_stack_eval {
            // Check if this is a simple function application that can be optimized
            if let ExprKind::Abstraction {
                parameter, body, ..
            } = &function.kind
            {
                if self.is_simple_function(body) {
                    // Direct evaluation without caching or complex environment setup
                    let argument_value = self.evaluate_expression_internal(argument)?;
                    return self.evaluate_simple_function_direct(parameter, body, argument_value);
                }
            }
        }

        // Check cache first
        if self.enable_caching {
            let cache_key = CacheKey::new(
                &Expr {
                    kind: ExprKind::Application {
                        function: Box::new(function.clone()),
                        argument: Box::new(argument.clone()),
                    },
                    span: function.span.clone(),
                },
                &self.environment,
                self.current_depth,
            );

            if let Some(cached_value) = self.expression_cache.get(&cache_key) {
                return Ok(cached_value);
            }
        }

        // Evaluate function expression
        let function_value = self.evaluate_expression_internal(function)?;

        // Evaluate argument expression
        let argument_value = self.evaluate_expression_internal(argument)?;

        // Apply function with optimizations
        let result = match &function_value.kind {
            ValueKind::Function { parameter, body } => {
                self.apply_function_optimized(parameter, body, argument_value, false)?
            }
            ValueKind::Closure {
                parameter,
                body,
                environment,
            } => {
                self.apply_closure_optimized(parameter, body, environment, argument_value, false)?
            }
            _ => {
                return Err(StandardError::Internal(
                    "Invalid expression type for function application".to_string(),
                ));
            }
        };

        // Cache the result
        if self.enable_caching {
            let cache_key = CacheKey::new(
                &Expr {
                    kind: ExprKind::Application {
                        function: Box::new(function.clone()),
                        argument: Box::new(argument.clone()),
                    },
                    span: function.span.clone(),
                },
                &self.environment,
                self.current_depth,
            );
            self.expression_cache.put(cache_key, result.clone());
        }

        Ok(result)
    }

    /// Apply a function with true optimizations that reduce overhead.
    fn apply_function_optimized(
        &mut self,
        parameter: &str,
        body: &Expr,
        argument_value: Value,
        is_tail_call: bool,
    ) -> StandardResult<Value> {
        // Check for tail call optimization
        if is_tail_call && self.enable_tco && self.is_tail_call_candidate(body) {
            self.expression_cache.stats_mut().tail_calls += 1;
            return self.perform_tail_call_optimization(parameter, body, argument_value);
        }

        // For simple functions, use direct evaluation without environment cloning
        if self.enable_stack_eval && self.is_simple_function(body) {
            self.expression_cache.stats_mut().stack_evals += 1;
            return self.evaluate_simple_function_direct(parameter, body, argument_value);
        }

        // For regular functions, use the most efficient approach: minimal environment setup
        // Instead of creating a new environment, just add the binding to the current one
        // This is much faster than environment cloning
        self.environment.bind(parameter.to_string(), argument_value);
        self.evaluate_expression_internal(body)
    }

    /// Apply a closure with true optimizations that reduce overhead.
    fn apply_closure_optimized(
        &mut self,
        parameter: &str,
        body: &Expr,
        captured_env: &EvaluationEnvironment,
        argument_value: Value,
        is_tail_call: bool,
    ) -> StandardResult<Value> {
        // Check for tail call optimization
        if is_tail_call && self.enable_tco && self.is_tail_call_candidate(body) {
            self.expression_cache.stats_mut().tail_calls += 1;
            return self.perform_tail_call_optimization_with_env(
                parameter,
                body,
                captured_env,
                argument_value,
            );
        }

        // For simple functions, use direct evaluation
        if self.enable_stack_eval && self.is_simple_function(body) {
            self.expression_cache.stats_mut().stack_evals += 1;
            return self.evaluate_simple_function_direct_with_env(
                parameter,
                body,
                captured_env,
                argument_value,
            );
        }

        // For regular closures, use the most efficient approach: minimal environment setup
        // Create a new environment with the captured environment as parent
        let mut new_env = EvaluationEnvironment::with_parent(captured_env.clone());
        new_env.bind(parameter.to_string(), argument_value);

        // Store original environment
        let original_env = std::mem::replace(&mut self.environment, new_env);

        // Evaluate function body
        let result = self.evaluate_expression_internal(body);

        // Restore original environment
        self.environment = original_env;

        result
    }

    /// Check if an expression is a candidate for tail call optimization.
    #[allow(clippy::only_used_in_recursion)]
    fn is_tail_call_candidate(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Application { .. } => true,
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.is_tail_call_candidate(then_branch) || self.is_tail_call_candidate(else_branch)
            }
            ExprKind::Let { body, .. } => self.is_tail_call_candidate(body),
            _ => false,
        }
    }

    /// Check if a function body is simple enough for stack-based evaluation.
    #[allow(clippy::only_used_in_recursion)]
    fn is_simple_function(&self, body: &Expr) -> bool {
        match &body.kind {
            ExprKind::Literal(_) | ExprKind::Variable(_) => true,
            ExprKind::BinaryOp { left, right, .. } => {
                self.is_simple_function(left) && self.is_simple_function(right)
            }
            ExprKind::UnaryOp { operand, .. } => self.is_simple_function(operand),
            ExprKind::FieldAccess { record, .. } => self.is_simple_function(record),
            _ => false,
        }
    }

    /// Perform tail call optimization.
    fn perform_tail_call_optimization(
        &mut self,
        parameter: &str,
        body: &Expr,
        argument_value: Value,
    ) -> StandardResult<Value> {
        // Instead of creating a new environment, update the current one
        self.environment.bind(parameter.to_string(), argument_value);

        // Evaluate the body in the current environment
        self.evaluate_expression_internal(body)
    }

    /// Perform tail call optimization with captured environment.
    fn perform_tail_call_optimization_with_env(
        &mut self,
        parameter: &str,
        body: &Expr,
        captured_env: &EvaluationEnvironment,
        argument_value: Value,
    ) -> StandardResult<Value> {
        // Create a new environment based on the captured one
        let mut new_env = self.env_pool.acquire(Some(captured_env.clone()));
        new_env.bind(parameter.to_string(), argument_value);

        // Replace current environment and evaluate
        std::mem::swap(&mut self.environment, &mut new_env);
        let result = self.evaluate_expression_internal(body);

        // Restore original environment and return the captured one to pool
        std::mem::swap(&mut self.environment, &mut new_env);
        self.env_pool.release(new_env);

        result
    }

    /// Evaluate a simple function using stack-based evaluation.
    fn evaluate_simple_function_direct(
        &mut self,
        parameter: &str,
        body: &Expr,
        argument_value: Value,
    ) -> StandardResult<Value> {
        // For simple functions, directly substitute the parameter value
        // This avoids environment manipulation overhead entirely
        match &body.kind {
            ExprKind::Variable(name) if name == parameter => {
                // Direct parameter access - return the argument value
                Ok(argument_value)
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                // For binary operations, directly evaluate with parameter substitution
                let left_val = if let ExprKind::Variable(name) = &left.kind {
                    if name == parameter {
                        argument_value.clone()
                    } else {
                        // Look up in current environment
                        self.environment
                            .lookup(name)
                            .ok_or(StandardError::Internal(
                                "Left operand evaluation failed".to_string(),
                            ))?
                    }
                } else {
                    self.evaluate_expression_internal(left)?
                };

                let right_val = if let ExprKind::Variable(name) = &right.kind {
                    if name == parameter {
                        argument_value
                    } else {
                        // Look up in current environment
                        self.environment
                            .lookup(name)
                            .ok_or(StandardError::Internal(
                                "Right operand evaluation failed".to_string(),
                            ))?
                    }
                } else {
                    self.evaluate_expression_internal(right)?
                };

                Ok(left_val
                    .apply_binary_op(operator, &right_val)
                    .map_err(|_e| {
                        StandardError::Internal("Function body evaluation failed".to_string())
                    })?)
            }
            _ => {
                // For complex expressions, use minimal environment setup
                // Add parameter to current environment temporarily
                self.environment.bind(parameter.to_string(), argument_value);
                self.evaluate_expression_internal(body)
            }
        }
    }

    /// Evaluate a simple function using direct evaluation with captured environment.
    fn evaluate_simple_function_direct_with_env(
        &mut self,
        parameter: &str,
        body: &Expr,
        captured_env: &EvaluationEnvironment,
        argument_value: Value,
    ) -> StandardResult<Value> {
        // For simple functions with captured environment, use direct evaluation
        // This avoids creating new evaluator instances
        match &body.kind {
            ExprKind::Variable(name) if name == parameter => {
                // Direct parameter access - return the argument value
                Ok(argument_value)
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                // Evaluate left and right sides with parameter substitution
                let left_val = if let ExprKind::Variable(name) = &left.kind {
                    if name == parameter {
                        argument_value.clone()
                    } else {
                        // Look up in captured environment
                        captured_env.lookup(name).ok_or(StandardError::Internal(
                            "Variable not found in captured environment".to_string(),
                        ))?
                    }
                } else {
                    // Create temporary evaluator for complex expressions
                    let mut temp_evaluator = Evaluator::new();
                    temp_evaluator.environment = captured_env.clone();
                    temp_evaluator.evaluate_expression_internal(left)?
                };

                let right_val = if let ExprKind::Variable(name) = &right.kind {
                    if name == parameter {
                        argument_value
                    } else {
                        // Look up in captured environment
                        captured_env.lookup(name).ok_or(StandardError::Internal(
                            "Variable not found in captured environment".to_string(),
                        ))?
                    }
                } else {
                    // Create temporary evaluator for complex expressions
                    let mut temp_evaluator = Evaluator::new();
                    temp_evaluator.environment = captured_env.clone();
                    temp_evaluator.evaluate_expression_internal(right)?
                };

                left_val
                    .apply_binary_op(operator, &right_val)
                    .map_err(|_e| {
                        StandardError::Internal("Function body evaluation failed".to_string())
                    })
            }
            _ => {
                // Fallback to regular evaluation with minimal environment setup
                let mut temp_env = EvaluationEnvironment::with_parent(captured_env.clone());
                temp_env.bind(parameter.to_string(), argument_value);

                let original_env = std::mem::replace(&mut self.environment, temp_env);
                let result = self.evaluate_expression_internal(body);
                self.environment = original_env;
                result
            }
        }
    }

    /// Cache a successful evaluation result.
    fn cache_result(&mut self, expr: &Expr, value: &Value) {
        if self.enable_caching && self.should_cache_expression(expr) {
            let key = CacheKey::new(expr, &self.environment, self.current_depth);
            self.expression_cache.put(key, value.clone());
        }
    }

    /// Determine if an expression should be cached.
    fn should_cache_expression(&self, expr: &Expr) -> bool {
        if !self.enable_caching {
            return false;
        }

        let cacheable = &self.config.cache.cacheable_expressions;

        match &expr.kind {
            ExprKind::Literal(_) => cacheable.literals,
            ExprKind::Variable(_) => cacheable.variables,
            ExprKind::BinaryOp { .. } => cacheable.binary_ops,
            ExprKind::UnaryOp { .. } => cacheable.unary_ops,
            ExprKind::FieldAccess { .. } => cacheable.field_access,
            ExprKind::Application { .. } => cacheable.applications,
            ExprKind::Abstraction { .. } => false, // Never cache abstractions
            ExprKind::Let { .. } => cacheable.let_expressions,
            ExprKind::Record { .. } => cacheable.records,
            ExprKind::Union { .. } => cacheable.unions,
            ExprKind::Match { .. } => cacheable.matches,
            ExprKind::If { .. } => cacheable.if_expressions,
            ExprKind::Annotated { .. } => false, // Never cache annotations
        }
    }

    /// Evaluate a literal with value interning optimization.
    fn evaluate_literal(&mut self, literal: &Literal) -> StandardResult<Value> {
        if !self.enable_value_optimization {
            return Ok(Value::from(literal.clone()));
        }

        match literal {
            Literal::Unit => Ok(Value::unit(Span::default())),
            Literal::Boolean(value) => {
                let interned_value = self.value_interner.get_boolean(*value);
                Ok(Value::boolean(*interned_value, Span::default()))
            }
            Literal::String(value) => {
                let interned_string = self.value_interner.intern_string(value.clone());
                Ok(Value::new(
                    ValueKind::String(interned_string),
                    Span::default(),
                ))
            }
            Literal::Integer(value) => {
                let interned_value = self.value_interner.intern_integer(*value);
                Ok(Value::integer(*interned_value, Span::default()))
            }
            Literal::Float(value) => {
                let interned_value = self.value_interner.intern_float(*value);
                Ok(Value::float(*interned_value, Span::default()))
            }
            Literal::List(elements) => {
                // Evaluate list elements and create an interned list
                let mut evaluated_elements = Vec::with_capacity(elements.len());
                for element in elements {
                    let evaluated = self.evaluate_expression_internal(element)?;
                    evaluated_elements.push(evaluated);
                }
                Ok(Value::list_interned(
                    evaluated_elements,
                    Span::default(),
                    &mut self.value_interner,
                ))
            }
        }
    }

    /// Evaluate a variable with optimized lookup.
    fn evaluate_variable(&self, name: &str) -> StandardResult<Value> {
        if let Some(value) = self.environment.lookup_ref(name) {
            return Ok(value.clone());
        }

        self.environment
            .lookup(name)
            .ok_or_else(|| StandardError::Internal(format!("Variable '{name}' not found")))
    }

    /// Evaluate a lambda abstraction.
    fn evaluate_abstraction(&mut self, parameter: &str, body: &Expr) -> StandardResult<Value> {
        Ok(Value::closure(
            parameter.to_string(),
            body.clone(),
            self.environment.clone(),
            Span::default(),
        ))
    }

    /// Evaluate a let expression with optimized environment handling.
    fn evaluate_let(&mut self, name: &str, value: &Expr, body: &Expr) -> StandardResult<Value> {
        let value_result = self.evaluate_expression_internal(value)?;

        self.environment
            .with_binding(name.to_string(), value_result, |env| {
                let mut let_evaluator = Evaluator {
                    environment: env.clone(),
                    module_resolver: self.module_resolver.clone(),
                    conflict_strategy: self.conflict_strategy,
                    expression_cache: ExpressionCache::new(100, 1024 * 1024),
                    env_pool: EnvironmentPool::new(50),
                    call_stack: Vec::new(),
                    max_stack_depth: self.max_stack_depth,
                    enable_tco: self.enable_tco,
                    enable_stack_eval: self.enable_stack_eval,
                    value_interner: self.value_interner.clone(),
                    value_pool: ValuePool::new(100),
                    enable_value_optimization: self.enable_value_optimization,
                    enable_caching: self.enable_caching,
                    current_depth: self.current_depth + 1,
                    config: self.config.clone(),
                    advanced_tail_call_detector: self.advanced_tail_call_detector.clone(),
                    function_inliner: self.function_inliner.clone(),
                    closure_capture_optimizer: self.closure_capture_optimizer.clone(),
                    parallel_evaluator: self.parallel_evaluator.clone(),
                    generational_gc: self.generational_gc.clone(),
                    optimized_evaluator: self.optimized_evaluator.clone(),
                    validation_engine: ValidationEngine::new(),
                };
                let_evaluator.evaluate_expression_internal(body)
            })
    }

    /// Evaluate a record expression with optimized field evaluation.
    fn evaluate_record(&mut self, fields: &[ligature_ast::RecordField]) -> StandardResult<Value> {
        let mut field_values = HashMap::with_capacity(fields.len());

        for field in fields {
            let value = self.evaluate_expression_internal(&field.value)?;
            field_values.insert(field.name.clone(), value);
        }

        if self.enable_value_optimization {
            Ok(Value::record_interned(
                field_values,
                Span::default(),
                &mut self.value_interner,
            ))
        } else {
            Ok(Value::record(field_values, Span::default()))
        }
    }

    /// Evaluate a field access expression with optimized record access.
    fn evaluate_field_access(&mut self, record: &Expr, field: &str) -> StandardResult<Value> {
        let record_value = self.evaluate_expression_internal(record)?;

        match &record_value.kind {
            ValueKind::Record(fields) => fields.get(field).cloned().ok_or(StandardError::Internal(
                "Record evaluation failed".to_string(),
            )),
            _ => Err(StandardError::Internal(
                "Record field access failed".to_string(),
            )),
        }
    }

    /// Evaluate a union expression.
    fn evaluate_union(&mut self, variant: &str, value: Option<&Expr>) -> StandardResult<Value> {
        let evaluated_value = if let Some(value_expr) = value {
            Some(self.evaluate_expression_internal(value_expr)?)
        } else {
            None
        };

        Ok(Value::union(
            variant.to_string(),
            evaluated_value,
            Span::default(),
        ))
    }

    /// Evaluate a match expression with optimized pattern matching.
    fn evaluate_match(
        &mut self,
        scrutinee: &Expr,
        cases: &[ligature_ast::MatchCase],
    ) -> StandardResult<Value> {
        let scrutinee_value = self.evaluate_expression_internal(scrutinee)?;

        for case in cases {
            let mut bindings = HashMap::new();
            if self.pattern_matches_with_bindings(&case.pattern, &scrutinee_value, &mut bindings)? {
                let mut new_env = self.environment.clone();
                for (name, value) in bindings {
                    new_env.bind(name, value);
                }

                let mut new_evaluator = Evaluator {
                    environment: new_env,
                    module_resolver: self.module_resolver.clone(),
                    conflict_strategy: self.conflict_strategy,
                    expression_cache: ExpressionCache::new(50, 1024 * 1024),
                    env_pool: EnvironmentPool::new(50),
                    call_stack: Vec::new(),
                    max_stack_depth: self.max_stack_depth,
                    enable_tco: self.enable_tco,
                    enable_stack_eval: self.enable_stack_eval,
                    value_interner: self.value_interner.clone(),
                    value_pool: ValuePool::new(50),
                    enable_value_optimization: self.enable_value_optimization,
                    enable_caching: self.enable_caching,
                    current_depth: self.current_depth + 1,
                    config: self.config.clone(),
                    advanced_tail_call_detector: self.advanced_tail_call_detector.clone(),
                    function_inliner: self.function_inliner.clone(),
                    closure_capture_optimizer: self.closure_capture_optimizer.clone(),
                    parallel_evaluator: self.parallel_evaluator.clone(),
                    generational_gc: self.generational_gc.clone(),
                    optimized_evaluator: self.optimized_evaluator.clone(),
                    validation_engine: ValidationEngine::new(),
                };

                if let Some(guard) = &case.guard {
                    let guard_value = new_evaluator.evaluate_expression_internal(guard)?;
                    match guard_value.as_boolean() {
                        Some(true) => {
                            return new_evaluator.evaluate_expression_internal(&case.expression);
                        }
                        Some(false) => {
                            continue;
                        }
                        None => {
                            return Err(StandardError::Internal(
                                "Guard evaluation failed".to_string(),
                            ));
                        }
                    }
                } else {
                    return new_evaluator.evaluate_expression_internal(&case.expression);
                }
            }
        }

        Err(StandardError::Internal(
            "Pattern matching failed".to_string(),
        ))
    }

    /// Evaluate an if expression with optimized condition evaluation.
    fn evaluate_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> StandardResult<Value> {
        let condition_value = self.evaluate_expression_internal(condition)?;

        match condition_value.as_boolean() {
            Some(true) => self.evaluate_expression_internal(then_branch),
            Some(false) => self.evaluate_expression_internal(else_branch),
            None => Err(StandardError::Internal(
                "Condition evaluation failed".to_string(),
            )),
        }
    }

    /// Evaluate a binary operation with optimized arithmetic.
    fn evaluate_binary_op(
        &mut self,
        operator: &BinaryOperator,
        left: &Expr,
        right: &Expr,
    ) -> StandardResult<Value> {
        let left_value = self.evaluate_expression_internal(left)?;
        let right_value = self.evaluate_expression_internal(right)?;

        left_value
            .apply_binary_op(operator, &right_value)
            .map_err(|_e| StandardError::Internal("Binary operation evaluation failed".to_string()))
    }

    /// Evaluate a unary operation.
    fn evaluate_unary_op(
        &mut self,
        operator: &UnaryOperator,
        operand: &Expr,
    ) -> StandardResult<Value> {
        let operand_value = self.evaluate_expression_internal(operand)?;

        operand_value
            .apply_unary_op(operator)
            .map_err(|_e| StandardError::Internal("Unary operation evaluation failed".to_string()))
    }

    /// Check if a pattern matches a value.
    pub fn pattern_matches(
        &self,
        pattern: &ligature_ast::Pattern,
        value: &Value,
    ) -> StandardResult<bool> {
        self.pattern_matches_with_bindings(pattern, value, &mut HashMap::new())
    }

    /// Extract union components from a value.
    pub fn extract_union_components<'a>(&self, value: &'a Value) -> Option<UnionComponents<'a>> {
        if let ValueKind::Union {
            variant,
            value: union_value,
        } = &value.kind
        {
            Some((variant, union_value.as_ref().map(|v| v.as_ref())))
        } else {
            None
        }
    }

    /// Check if a pattern matches a value and extract bindings.
    pub fn pattern_matches_with_bindings(
        &self,
        pattern: &ligature_ast::Pattern,
        value: &Value,
        bindings: &mut HashMap<String, Value>,
    ) -> StandardResult<bool> {
        match pattern {
            ligature_ast::Pattern::Wildcard => Ok(true),
            ligature_ast::Pattern::Variable(name) => {
                bindings.insert(name.clone(), value.clone());
                Ok(true)
            }
            ligature_ast::Pattern::Literal(literal) => {
                let literal_value = Value::from(literal.clone());
                Ok(value == &literal_value)
            }
            ligature_ast::Pattern::Record { fields } => {
                if let ValueKind::Record(record_fields) = &value.kind {
                    for pattern_field in fields {
                        if let Some(record_value) = record_fields.get(&pattern_field.name) {
                            if !self.pattern_matches_with_bindings(
                                &pattern_field.pattern,
                                record_value,
                                bindings,
                            )? {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            ligature_ast::Pattern::Union {
                variant,
                value: pattern_value,
            } => {
                if let Some((value_variant, value_payload)) = self.extract_union_components(value) {
                    if value_variant == variant {
                        if let Some(pattern_val) = pattern_value {
                            if let Some(value_val) = value_payload {
                                self.pattern_matches_with_bindings(pattern_val, value_val, bindings)
                            } else {
                                Ok(false)
                            }
                        } else {
                            Ok(value_payload.is_none())
                        }
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            ligature_ast::Pattern::List { elements } => {
                if let ValueKind::List(list_elements) = &value.kind {
                    if elements.len() != list_elements.len() {
                        return Ok(false);
                    }
                    for (pattern_elem, list_elem) in elements.iter().zip(list_elements.iter()) {
                        if !self.pattern_matches_with_bindings(pattern_elem, list_elem, bindings)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Get comprehensive value optimization statistics.
    pub fn value_optimization_stats(&self) -> ValueOptimizationStats {
        let interner_stats = self.value_interner.stats();
        let (pool_available, pool_max) = self.value_pool.stats();

        ValueOptimizationStats {
            interner: interner_stats,
            pool_utilization: if pool_max > 0 {
                pool_available as f64 / pool_max as f64
            } else {
                0.0
            },
            pool_available,
            pool_max,
            optimization_enabled: self.enable_value_optimization,
            total_memory_saved: self.estimate_memory_savings(),
        }
    }

    /// Estimate memory savings from value optimization.
    fn estimate_memory_savings(&self) -> usize {
        let interner_stats = self.value_interner.stats();

        // Estimate savings from string interning
        let string_savings = interner_stats.string_count.saturating_sub(1) * 24; // Approximate string overhead

        // Estimate savings from integer interning
        let integer_savings = interner_stats.integer_count.saturating_sub(1) * 8; // Approximate integer overhead

        // Estimate savings from float interning
        let float_savings = interner_stats.float_count.saturating_sub(1) * 8; // Approximate float overhead

        // Estimate savings from boolean interning
        let boolean_savings = interner_stats.boolean_count.saturating_sub(2) * 8; // Only 2 unique booleans

        // Estimate savings from list interning
        let list_savings = interner_stats.list_count.saturating_sub(1) * 32; // Approximate list overhead

        string_savings + integer_savings + float_savings + boolean_savings + list_savings
    }

    /// Validate a value against a type using the runtime validation engine
    pub fn validate_value(
        &mut self,
        value: &Value,
        type_: &Type,
    ) -> StandardResult<ValidationResult> {
        self.validation_engine.validate_value(value, type_)
    }

    /// Get validation engine statistics
    pub fn validation_stats(&self) -> ValidationStats {
        self.validation_engine.stats()
    }

    /// Enable or disable validation caching
    pub fn set_validation_caching(&mut self, enable: bool) {
        self.validation_engine.set_caching(enable);
    }

    /// Clear validation cache
    pub fn clear_validation_cache(&mut self) {
        self.validation_engine.clear_cache();
    }
}

impl Default for Evaluator {
    fn default() -> Self {
        Self::new()
    }
}
