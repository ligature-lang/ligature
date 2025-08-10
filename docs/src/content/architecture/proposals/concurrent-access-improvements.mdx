# Concurrent Access Improvements Proposal

## Overview

This proposal outlines improvements to Ligature's concurrent access patterns, focusing on replacing thread-unsafe data structures with concurrent alternatives, particularly using `dashmap` for high-performance concurrent hash maps. These improvements will enable better parallel evaluation, concurrent type checking, and improved performance for large configurations.

## Problem Statement

### Current Limitations

Ligature's current implementation has several concurrency-related limitations:

1. **Thread-Unsafe Data Structures**: Many core data structures use `HashMap` and `IndexMap` which are not thread-safe
2. **Sequential Evaluation**: The evaluator processes expressions sequentially, limiting performance
3. **Blocking Operations**: Type checking and validation operations block the main thread
4. **Memory Contention**: Shared state access creates potential bottlenecks
5. **No Parallel Processing**: Large configurations cannot be processed in parallel

### Performance Impact

- **Single-threaded Bottlenecks**: All operations must be processed sequentially
- **Memory Allocation Contention**: Frequent allocations in hot paths
- **Cache Invalidation**: Shared mutable state reduces cache efficiency
- **Scalability Limits**: Performance doesn't scale with available cores

## Design Philosophy

### Core Principles

1. **Lock-Free Operations**: Use lock-free data structures where possible
2. **Minimal Contention**: Reduce shared state and contention points
3. **Scalable Performance**: Performance should scale with available cores
4. **Backward Compatibility**: Existing single-threaded code continues to work
5. **Graceful Degradation**: Fall back to sequential processing when needed

### Concurrency Models

1. **Shared-Nothing**: Each thread has its own isolated state
2. **Read-Mostly**: Optimize for concurrent reads with minimal writes
3. **Work Stealing**: Distribute work dynamically across threads
4. **Async/Await**: Use async patterns for I/O-bound operations

## Proposed Solution

### 1. DashMap Integration

#### Core Data Structure Replacements

```rust
// Before: Thread-unsafe HashMap
use std::collections::HashMap;

pub struct TypeEnvironment {
    bindings: HashMap<String, Type>,
    type_aliases: HashMap<String, TypeAlias>,
    type_classes: HashMap<String, TypeClassDeclaration>,
    instances: HashMap<String, Vec<InstanceDeclaration>>,
}

// After: Thread-safe DashMap
use dashmap::DashMap;

pub struct ConcurrentTypeEnvironment {
    bindings: DashMap<String, Type>,
    type_aliases: DashMap<String, TypeAlias>,
    type_classes: DashMap<String, TypeClassDeclaration>,
    instances: DashMap<String, Vec<InstanceDeclaration>>,
}
```

#### Implementation Strategy

```rust
use dashmap::DashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct ConcurrentEvaluator {
    // Thread-safe caches
    expression_cache: DashMap<CacheKey, CacheEntry>,
    type_cache: DashMap<TypeKey, Type>,
    value_cache: DashMap<ValueKey, Value>,

    // Shared state with fine-grained locking
    environment: Arc<RwLock<EvaluationEnvironment>>,
    module_resolver: Arc<RwLock<ModuleResolver>>,

    // Work queues for parallel processing
    work_queue: Arc<WorkQueue>,
    result_collector: Arc<ResultCollector>,
}

impl ConcurrentEvaluator {
    pub async fn evaluate_parallel(&self, program: &Program) -> AstResult<Value> {
        // Split program into parallelizable chunks
        let chunks = self.split_program(program);

        // Process chunks in parallel
        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                let evaluator = self.clone();
                tokio::spawn(async move {
                    evaluator.evaluate_chunk(chunk).await
                })
            })
            .collect();

        // Collect results
        let results = futures::future::join_all(handles).await;

        // Combine results
        self.combine_results(results)
    }

    pub async fn evaluate_chunk(&self, chunk: ProgramChunk) -> AstResult<Value> {
        // Each thread gets its own isolated evaluator
        let mut local_evaluator = LocalEvaluator::new();

        // Process chunk with local state
        for declaration in chunk.declarations {
            local_evaluator.evaluate_declaration(&declaration)?;
        }

        // Merge results back to shared state
        self.merge_results(local_evaluator.results()).await
    }
}
```

### 2. Parallel Evaluation Engine

#### Work Distribution

```rust
pub struct WorkQueue {
    tasks: Arc<dashmap::DashMap<TaskId, Task>>,
    workers: Vec<Worker>,
    scheduler: Arc<Scheduler>,
}

pub struct Task {
    id: TaskId,
    expression: Expr,
    priority: Priority,
    dependencies: Vec<TaskId>,
    status: TaskStatus,
}

pub enum TaskStatus {
    Pending,
    Running,
    Completed(Value),
    Failed(Error),
}

impl WorkQueue {
    pub async fn submit(&self, task: Task) -> TaskId {
        let task_id = TaskId::new();

        // Insert task into queue
        self.tasks.insert(task_id, task);

        // Notify scheduler
        self.scheduler.notify_new_task(task_id).await;

        task_id
    }

    pub async fn get_result(&self, task_id: TaskId) -> AstResult<Value> {
        loop {
            if let Some(task) = self.tasks.get(&task_id) {
                match &task.status {
                    TaskStatus::Completed(value) => return Ok(value.clone()),
                    TaskStatus::Failed(error) => return Err(error.clone()),
                    _ => {
                        // Wait for completion
                        tokio::time::sleep(Duration::from_millis(1)).await;
                    }
                }
            }
        }
    }
}
```

#### Worker Pool

```rust
pub struct Worker {
    id: WorkerId,
    task_queue: Arc<WorkQueue>,
    local_cache: LocalCache,
    evaluator: LocalEvaluator,
}

impl Worker {
    pub async fn run(&mut self) {
        loop {
            // Get next task
            if let Some(task) = self.task_queue.get_next_task().await {
                // Process task with local evaluator
                let result = self.evaluator.evaluate_expression(&task.expression).await;

                // Update task status
                self.task_queue.complete_task(task.id, result).await;
            } else {
                // No tasks available, yield
                tokio::task::yield_now().await;
            }
        }
    }
}
```

### 3. Concurrent Type Checking

#### Parallel Type Inference

```rust
pub struct ConcurrentTypeChecker {
    type_cache: DashMap<TypeKey, Type>,
    constraint_solver: Arc<RwLock<ConstraintSolver>>,
    workers: Vec<TypeCheckerWorker>,
}

impl ConcurrentTypeChecker {
    pub async fn check_program_parallel(&self, program: &Program) -> AstResult<()> {
        // Split program into independent modules
        let modules = self.split_into_modules(program);

        // Check modules in parallel
        let handles: Vec<_> = modules
            .into_iter()
            .map(|module| {
                let checker = self.clone();
                tokio::spawn(async move {
                    checker.check_module(module).await
                })
            })
            .collect();

        // Wait for all modules to complete
        let results = futures::future::join_all(handles).await;

        // Check for errors
        for result in results {
            result??; // Propagate any errors
        }

        Ok(())
    }

    pub async fn check_module(&self, module: Module) -> AstResult<()> {
        // Each worker gets its own type environment
        let mut local_checker = LocalTypeChecker::new();

        // Check declarations in parallel where possible
        let declaration_handles: Vec<_> = module
            .declarations
            .into_iter()
            .map(|declaration| {
                let checker = local_checker.clone();
                tokio::spawn(async move {
                    checker.check_declaration(&declaration).await
                })
            })
            .collect();

        // Wait for all declarations to complete
        let results = futures::future::join_all(declaration_handles).await;

        // Check for errors
        for result in results {
            result??;
        }

        Ok(())
    }
}
```

### 4. Concurrent Caching

#### Thread-Safe Caches

```rust
pub struct ConcurrentCache {
    expression_cache: DashMap<CacheKey, CacheEntry>,
    type_cache: DashMap<TypeKey, Type>,
    value_cache: DashMap<ValueKey, Value>,
    stats: Arc<RwLock<CacheStats>>,
}

impl ConcurrentCache {
    pub fn get_expression(&self, key: &CacheKey) -> Option<Value> {
        if let Some(entry) = self.expression_cache.get(key) {
            // Update access statistics
            entry.access();
            Some(entry.value.clone())
        } else {
            None
        }
    }

    pub fn put_expression(&self, key: CacheKey, value: Value) {
        let entry = CacheEntry::new(value);
        self.expression_cache.insert(key, entry);

        // Update statistics
        if let Ok(mut stats) = self.stats.try_write() {
            stats.insertions += 1;
        }
    }

    pub async fn evict_lru(&mut self) {
        // Find least recently used entries across all caches
        let mut lru_entries = Vec::new();

        // Collect LRU entries from expression cache
        for entry in self.expression_cache.iter() {
            lru_entries.push((entry.key().clone(), entry.value().last_access));
        }

        // Sort by access time
        lru_entries.sort_by_key(|(_, access_time)| *access_time);

        // Remove oldest entries
        let to_remove = lru_entries.len().saturating_sub(self.max_size);
        for (key, _) in lru_entries.into_iter().take(to_remove) {
            self.expression_cache.remove(&key);
        }
    }
}
```

### 5. Async Evaluation

#### Async Evaluation Engine

```rust
pub struct AsyncEvaluator {
    runtime: tokio::runtime::Runtime,
    work_queue: Arc<WorkQueue>,
    cache: Arc<ConcurrentCache>,
    config: AsyncEvaluatorConfig,
}

pub struct AsyncEvaluatorConfig {
    pub max_concurrent_tasks: usize,
    pub worker_threads: usize,
    pub cache_size: usize,
    pub timeout: Duration,
}

impl AsyncEvaluator {
    pub fn new(config: AsyncEvaluatorConfig) -> Self {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(config.worker_threads)
            .enable_all()
            .build()
            .unwrap();

        let work_queue = Arc::new(WorkQueue::new());
        let cache = Arc::new(ConcurrentCache::new(config.cache_size));

        Self {
            runtime,
            work_queue,
            cache,
            config,
        }
    }

    pub async fn evaluate_program(&self, program: &Program) -> AstResult<Value> {
        // Split program into parallelizable tasks
        let tasks = self.create_tasks(program);

        // Submit tasks to work queue
        let task_ids: Vec<_> = tasks
            .into_iter()
            .map(|task| self.work_queue.submit(task).await)
            .collect();

        // Wait for all tasks to complete with timeout
        let timeout = tokio::time::timeout(self.config.timeout, async {
            let results: Vec<_> = task_ids
                .into_iter()
                .map(|id| self.work_queue.get_result(id).await)
                .collect();

            futures::future::join_all(results).await
        })
        .await
        .map_err(|_| AstError::EvaluationTimeout)?;

        // Combine results
        self.combine_results(timeout)
    }

    pub async fn evaluate_expression(&self, expression: &Expr) -> AstResult<Value> {
        // Check cache first
        let cache_key = CacheKey::from_expression(expression);
        if let Some(cached_value) = self.cache.get_expression(&cache_key) {
            return Ok(cached_value);
        }

        // Evaluate expression
        let value = self.evaluate_expression_internal(expression).await?;

        // Cache result
        self.cache.put_expression(cache_key, value.clone());

        Ok(value)
    }
}
```

## Implementation Strategy

### Phase 1: DashMap Integration (Immediate - 2-3 weeks)

#### Goals

- Replace thread-unsafe data structures with DashMap
- Implement basic concurrent access patterns
- Add thread-safe caching

#### Implementation Tasks

1. **Add Dependencies**

```toml
[dependencies]
dashmap = "5.5"
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"
```

2. **Replace Core Data Structures**

```rust
// Replace HashMap with DashMap in key components
pub struct ConcurrentTypeEnvironment {
    bindings: DashMap<String, Type>,
    type_aliases: DashMap<String, TypeAlias>,
    type_classes: DashMap<String, TypeClassDeclaration>,
    instances: DashMap<String, Vec<InstanceDeclaration>>,
}

pub struct ConcurrentCache {
    expression_cache: DashMap<CacheKey, CacheEntry>,
    type_cache: DashMap<TypeKey, Type>,
    value_cache: DashMap<ValueKey, Value>,
}
```

3. **Update Access Patterns**

```rust
impl ConcurrentTypeEnvironment {
    pub fn bind(&self, name: String, type_: Type) {
        self.bindings.insert(name, type_);
    }

    pub fn lookup(&self, name: &str) -> Option<Type> {
        self.bindings.get(name).map(|entry| entry.clone())
    }

    pub fn remove(&self, name: &str) -> Option<Type> {
        self.bindings.remove(name).map(|(_, type_)| type_)
    }
}
```

### Phase 2: Parallel Evaluation (Short-term - 4-6 weeks)

#### Goals

- Implement parallel evaluation engine
- Add work distribution and task scheduling
- Implement worker pools

#### Implementation Tasks

1. **Work Queue Implementation**

```rust
pub struct WorkQueue {
    tasks: DashMap<TaskId, Task>,
    workers: Vec<Worker>,
    scheduler: Arc<Scheduler>,
}

impl WorkQueue {
    pub async fn submit(&self, task: Task) -> TaskId {
        let task_id = TaskId::new();
        self.tasks.insert(task_id, task);
        self.scheduler.notify_new_task(task_id).await;
        task_id
    }

    pub async fn get_result(&self, task_id: TaskId) -> AstResult<Value> {
        // Implementation for waiting for task completion
    }
}
```

2. **Worker Pool Implementation**

```rust
pub struct WorkerPool {
    workers: Vec<Worker>,
    work_queue: Arc<WorkQueue>,
}

impl WorkerPool {
    pub async fn start(&self) {
        let handles: Vec<_> = self.workers
            .iter()
            .map(|worker| {
                let work_queue = self.work_queue.clone();
                tokio::spawn(async move {
                    worker.run(work_queue).await
                })
            })
            .collect();

        futures::future::join_all(handles).await;
    }
}
```

### Phase 3: Concurrent Type Checking (Medium-term - 6-8 weeks)

#### Goals

- Implement parallel type checking
- Add concurrent constraint solving
- Implement module-level parallelism

#### Implementation Tasks

1. **Parallel Type Inference**

```rust
pub struct ConcurrentTypeChecker {
    type_cache: DashMap<TypeKey, Type>,
    constraint_solver: Arc<RwLock<ConstraintSolver>>,
    workers: Vec<TypeCheckerWorker>,
}

impl ConcurrentTypeChecker {
    pub async fn check_program_parallel(&self, program: &Program) -> AstResult<()> {
        // Split program into modules and check in parallel
    }
}
```

2. **Concurrent Constraint Solving**

```rust
pub struct ConcurrentConstraintSolver {
    constraints: DashMap<ConstraintId, Constraint>,
    solutions: DashMap<SolutionId, Solution>,
    workers: Vec<ConstraintSolverWorker>,
}

impl ConcurrentConstraintSolver {
    pub async fn solve_parallel(&self) -> AstResult<Vec<Solution>> {
        // Solve constraints in parallel
    }
}
```

### Phase 4: Async Evaluation (Long-term - 8-12 weeks)

#### Goals

- Implement full async evaluation engine
- Add async I/O operations
- Implement async caching and persistence

#### Implementation Tasks

1. **Async Evaluation Engine**

```rust
pub struct AsyncEvaluator {
    runtime: tokio::runtime::Runtime,
    work_queue: Arc<WorkQueue>,
    cache: Arc<ConcurrentCache>,
    config: AsyncEvaluatorConfig,
}

impl AsyncEvaluator {
    pub async fn evaluate_program(&self, program: &Program) -> AstResult<Value> {
        // Full async evaluation implementation
    }
}
```

2. **Async I/O Operations**

```rust
pub struct AsyncModuleResolver {
    file_cache: DashMap<PathBuf, Module>,
    network_client: reqwest::Client,
}

impl AsyncModuleResolver {
    pub async fn resolve_module(&self, path: &str) -> AstResult<Module> {
        // Async module resolution with caching
    }
}
```

## Configuration and Usage

### Basic Usage

```rust
// Create concurrent evaluator
let config = AsyncEvaluatorConfig {
    max_concurrent_tasks: 16,
    worker_threads: 8,
    cache_size: 10000,
    timeout: Duration::from_secs(30),
};

let evaluator = AsyncEvaluator::new(config);

// Evaluate program asynchronously
let result = evaluator.evaluate_program(&program).await?;
```

### Advanced Usage

```rust
// Custom work distribution
let work_queue = Arc::new(WorkQueue::new());

// Submit tasks manually
let task_id = work_queue.submit(Task {
    expression: complex_expression,
    priority: Priority::High,
    dependencies: vec![],
    status: TaskStatus::Pending,
}).await;

// Wait for completion
let result = work_queue.get_result(task_id).await?;

// Parallel type checking
let type_checker = ConcurrentTypeChecker::new();
let result = type_checker.check_program_parallel(&program).await?;
```

### CLI Integration

```bash
# Run with parallel evaluation
ligature eval --parallel --workers 8 config.lig

# Run with async evaluation
ligature eval --async --timeout 30s large-config.lig

# Run with concurrent type checking
ligature typecheck --parallel --workers 4 config.lig
```

## Testing Strategy

### Unit Tests

```rust
#[tokio::test]
async fn test_concurrent_evaluation() {
    let evaluator = AsyncEvaluator::new(AsyncEvaluatorConfig::default());
    let program = create_test_program();

    let result = evaluator.evaluate_program(&program).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_concurrent_type_checking() {
    let checker = ConcurrentTypeChecker::new();
    let program = create_test_program();

    let result = checker.check_program_parallel(&program).await;
    assert!(result.is_ok());
}
```

### Performance Tests

```rust
#[tokio::test]
async fn test_parallel_performance() {
    let large_program = create_large_program();

    // Sequential evaluation
    let start = std::time::Instant::now();
    let sequential_result = sequential_evaluator.evaluate(&large_program);
    let sequential_time = start.elapsed();

    // Parallel evaluation
    let start = std::time::Instant::now();
    let parallel_result = parallel_evaluator.evaluate(&large_program).await;
    let parallel_time = start.elapsed();

    // Verify results are equivalent
    assert_eq!(sequential_result, parallel_result);

    // Verify performance improvement
    assert!(parallel_time < sequential_time);
    println!("Speedup: {:.2}x", sequential_time.as_secs_f64() / parallel_time.as_secs_f64());
}
```

### Stress Tests

```rust
#[tokio::test]
async fn test_concurrent_stress() {
    let evaluator = AsyncEvaluator::new(AsyncEvaluatorConfig::default());

    // Submit many concurrent tasks
    let handles: Vec<_> = (0..1000)
        .map(|i| {
            let evaluator = evaluator.clone();
            let program = create_test_program(i);
            tokio::spawn(async move {
                evaluator.evaluate_program(&program).await
            })
        })
        .collect();

    // Wait for all to complete
    let results = futures::future::join_all(handles).await;

    // Verify all succeeded
    for result in results {
        assert!(result.is_ok());
    }
}
```

## Migration Strategy

### Backward Compatibility

1. **Default Behavior**: Existing code continues to use sequential evaluation
2. **Gradual Migration**: Users can opt into concurrent features incrementally
3. **Feature Flags**: Enable/disable concurrent features via configuration
4. **Fallback Mechanisms**: Automatic fallback to sequential processing if needed

### Migration Path

1. **Phase 1**: Add DashMap without changing public APIs
2. **Phase 2**: Add parallel evaluation as optional feature
3. **Phase 3**: Add concurrent type checking
4. **Phase 4**: Add full async evaluation engine

### Migration Examples

```rust
// Before: Sequential evaluation
let evaluator = Evaluator::new();
let result = evaluator.evaluate_program(&program)?;

// After: Concurrent evaluation (optional)
let evaluator = ConcurrentEvaluator::new();
let result = evaluator.evaluate_program(&program).await?;

// Before: Sequential type checking
let checker = TypeChecker::new();
let result = checker.check_program(&program)?;

// After: Concurrent type checking (optional)
let checker = ConcurrentTypeChecker::new();
let result = checker.check_program_parallel(&program).await?;
```

## Risks and Mitigations

### 1. Complexity Increase

**Risk**: Concurrent code is more complex and harder to debug
**Mitigation**:

- Comprehensive testing with race condition detection
- Clear documentation and examples
- Gradual introduction with fallback options
- Debugging tools and logging

### 2. Memory Overhead

**Risk**: Concurrent data structures may use more memory
**Mitigation**:

- Efficient memory management
- Configurable cache sizes
- Memory monitoring and limits
- Garbage collection for unused entries

### 3. Thread Safety Issues

**Risk**: Race conditions and data races
**Mitigation**:

- Use of proven concurrent data structures (DashMap)
- Comprehensive testing with tools like `loom`
- Clear documentation of thread safety guarantees
- Static analysis tools

### 4. Performance Degradation

**Risk**: Overhead may outweigh benefits for small programs
**Mitigation**:

- Automatic detection of when to use parallel processing
- Configurable thresholds
- Performance monitoring and metrics
- Fallback to sequential processing

## Success Metrics

### Technical Metrics

1. **Performance**: Speedup for large configurations
2. **Scalability**: Performance scaling with core count
3. **Memory Usage**: Memory overhead of concurrent structures
4. **Throughput**: Number of expressions processed per second

### User Experience Metrics

1. **Adoption**: Number of users enabling concurrent features
2. **Satisfaction**: User feedback on performance improvements
3. **Reliability**: Reduction in evaluation timeouts
4. **Usability**: Ease of enabling concurrent features

## Conclusion

This proposal provides a comprehensive approach to improving Ligature's concurrent access patterns using DashMap and other modern concurrent programming techniques. The gradual introduction ensures backward compatibility while enabling significant performance improvements for large configurations.

The key benefits include:

1. **Improved Performance**: Parallel processing of large configurations
2. **Better Scalability**: Performance that scales with available cores
3. **Thread Safety**: Robust concurrent data structures
4. **Backward Compatibility**: Existing code continues to work
5. **Configurable**: Users can choose appropriate concurrency levels

The implementation strategy provides a clear path forward with measurable milestones and comprehensive testing to ensure reliability and performance.

## References

1. [DashMap Documentation](https://docs.rs/dashmap/)
2. [Tokio Runtime](https://tokio.rs/)
3. [Rust Async Book](https://rust-lang.github.io/async-book/)
4. [Concurrent Programming in Rust](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
5. [Lock-Free Programming](https://en.wikipedia.org/wiki/Lock-free_programming)
