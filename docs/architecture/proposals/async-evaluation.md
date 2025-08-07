# Async Evaluation Proposal

## Overview

This proposal outlines a comprehensive approach to implementing async evaluation in Ligature to handle large configurations efficiently. Async evaluation will enable non-blocking I/O operations, parallel processing, and better resource management for complex configuration scenarios.

## Problem Statement

### Current Evaluation Limitations

Ligature's current evaluation model has several limitations for large configurations:

1. **Blocking Operations**: All evaluation is synchronous and blocking
2. **Sequential Processing**: Expressions are evaluated one at a time
3. **No I/O Support**: Cannot handle file I/O, network requests, or external data sources
4. **Memory Constraints**: Large configurations may consume excessive memory
5. **No Progress Reporting**: No way to track evaluation progress for long-running operations

### Use Cases Requiring Async Evaluation

1. **Large Configuration Files**: Processing multi-megabyte configuration files
2. **External Data Sources**: Fetching configuration from APIs, databases, or cloud services
3. **Parallel Processing**: Evaluating independent configuration sections concurrently
4. **Real-time Updates**: Handling configuration changes during runtime
5. **Resource Management**: Efficient handling of memory and CPU resources

## Design Philosophy

### Core Principles

1. **Non-blocking**: Evaluation should not block the main thread
2. **Composable**: Async operations should compose naturally
3. **Efficient**: Minimal overhead for async operations
4. **Observable**: Progress and status should be observable
5. **Resilient**: Graceful handling of failures and timeouts

### Async Patterns

1. **Future-based**: Use Rust's async/await syntax
2. **Stream-based**: Handle large datasets as streams
3. **Parallel**: Execute independent operations concurrently
4. **Lazy**: Defer evaluation until needed
5. **Cancellable**: Allow cancellation of long-running operations

## Proposed Solution

### 1. Async Evaluation Engine

#### Core Async Types

```rust
use tokio::sync::{mpsc, oneshot};
use futures::{Stream, StreamExt};
use std::pin::Pin;
use std::future::Future;

// Main async evaluator
pub struct AsyncEvaluator {
    runtime: tokio::runtime::Runtime,
    work_queue: Arc<WorkQueue>,
    cache: Arc<AsyncCache>,
    config: AsyncEvaluatorConfig,
}

pub struct AsyncEvaluatorConfig {
    pub max_concurrent_tasks: usize,
    pub worker_threads: usize,
    pub cache_size: usize,
    pub timeout: Duration,
    pub enable_progress: bool,
}

// Async evaluation result
pub type AsyncResult<T> = Result<T, AsyncError>;

#[derive(Debug, thiserror::Error)]
pub enum AsyncError {
    #[error("Evaluation timeout: {message}")]
    Timeout { message: String, duration: Duration },

    #[error("Evaluation cancelled")]
    Cancelled,

    #[error("Resource exhausted: {message}")]
    ResourceExhausted { message: String },

    #[error("I/O error: {message}")]
    Io { message: String, #[source] source: std::io::Error },

    #[error("Network error: {message}")]
    Network { message: String, #[source] source: Box<dyn std::error::Error + Send + Sync> },

    #[error("Evaluation error: {message}")]
    Evaluation { message: String, #[source] source: Box<dyn std::error::Error + Send + Sync> },
}

// Progress reporting
#[derive(Debug, Clone)]
pub struct EvaluationProgress {
    pub completed: usize,
    pub total: usize,
    pub current_operation: String,
    pub estimated_remaining: Duration,
}

// Async expression types
pub enum AsyncExpr {
    Sync(Expr),
    Async(Box<dyn Future<Output = AsyncResult<Value>> + Send>),
    Stream(Box<dyn Stream<Item = AsyncResult<Value>> + Send>),
    Parallel(Vec<AsyncExpr>),
    WithTimeout(Box<AsyncExpr>, Duration),
    WithRetry(Box<AsyncExpr>, RetryConfig),
}

pub struct RetryConfig {
    pub max_attempts: usize,
    pub backoff: BackoffStrategy,
    pub retry_condition: Box<dyn Fn(&AsyncError) -> bool + Send + Sync>,
}

pub enum BackoffStrategy {
    Fixed(Duration),
    Exponential { initial: Duration, multiplier: f64, max: Duration },
    Jittered { base: Duration, jitter: f64 },
}
```

#### Async Evaluation Implementation

```rust
impl AsyncEvaluator {
    pub fn new(config: AsyncEvaluatorConfig) -> Self {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(config.worker_threads)
            .enable_all()
            .build()
            .unwrap();

        let work_queue = Arc::new(WorkQueue::new());
        let cache = Arc::new(AsyncCache::new(config.cache_size));

        Self {
            runtime,
            work_queue,
            cache,
            config,
        }
    }

    pub async fn evaluate_program(&self, program: &Program) -> AsyncResult<Value> {
        // Split program into async tasks
        let tasks = self.create_async_tasks(program);

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
        .map_err(|_| AsyncError::Timeout {
            message: "Evaluation exceeded timeout".to_string(),
            duration: self.config.timeout,
        })?;

        // Combine results
        self.combine_results(timeout)
    }

    pub async fn evaluate_expression(&self, expr: &AsyncExpr) -> AsyncResult<Value> {
        match expr {
            AsyncExpr::Sync(sync_expr) => {
                // Evaluate synchronous expression
                let value = self.evaluate_sync_expression(sync_expr)?;
                Ok(value)
            }
            AsyncExpr::Async(async_future) => {
                // Evaluate async expression
                async_future.await
            }
            AsyncExpr::Stream(stream) => {
                // Handle stream evaluation
                self.evaluate_stream(stream).await
            }
            AsyncExpr::Parallel(exprs) => {
                // Evaluate expressions in parallel
                self.evaluate_parallel(exprs).await
            }
            AsyncExpr::WithTimeout(expr, timeout) => {
                // Evaluate with timeout
                tokio::time::timeout(*timeout, self.evaluate_expression(expr))
                    .await
                    .map_err(|_| AsyncError::Timeout {
                        message: "Expression evaluation timeout".to_string(),
                        duration: *timeout,
                    })?
            }
            AsyncExpr::WithRetry(expr, retry_config) => {
                // Evaluate with retry logic
                self.evaluate_with_retry(expr, retry_config).await
            }
        }
    }

    async fn evaluate_parallel(&self, exprs: &[AsyncExpr]) -> AsyncResult<Value> {
        let futures: Vec<_> = exprs
            .iter()
            .map(|expr| self.evaluate_expression(expr))
            .collect();

        let results = futures::future::join_all(futures).await;

        // Check for errors
        let mut values = Vec::new();
        for result in results {
            values.push(result?);
        }

        // Combine parallel results
        self.combine_parallel_results(values)
    }

    async fn evaluate_stream(&self, stream: &mut Box<dyn Stream<Item = AsyncResult<Value>> + Send>) -> AsyncResult<Value> {
        let mut values = Vec::new();

        while let Some(result) = stream.next().await {
            values.push(result?);
        }

        // Combine stream results
        self.combine_stream_results(values)
    }

    async fn evaluate_with_retry(&self, expr: &AsyncExpr, config: &RetryConfig) -> AsyncResult<Value> {
        let mut attempt = 0;
        let mut backoff = config.backoff.clone();

        loop {
            match self.evaluate_expression(expr).await {
                Ok(value) => return Ok(value),
                Err(error) => {
                    attempt += 1;

                    if attempt >= config.max_attempts {
                        return Err(error);
                    }

                    if !(config.retry_condition)(&error) {
                        return Err(error);
                    }

                    // Wait before retry
                    let delay = backoff.next_delay(attempt);
                    tokio::time::sleep(delay).await;
                }
            }
        }
    }
}
```

### 2. Async I/O Operations

#### File and Network Operations

```rust
pub struct AsyncIoOperations {
    http_client: reqwest::Client,
    file_cache: Arc<AsyncCache>,
}

impl AsyncIoOperations {
    pub fn new() -> Self {
        let http_client = reqwest::Client::new();
        let file_cache = Arc::new(AsyncCache::new(1000));

        Self {
            http_client,
            file_cache,
        }
    }

    pub async fn read_file(&self, path: &Path) -> AsyncResult<String> {
        // Check cache first
        if let Some(cached) = self.file_cache.get(path).await {
            return Ok(cached);
        }

        // Read file asynchronously
        let content = tokio::fs::read_to_string(path)
            .await
            .map_err(|e| AsyncError::Io {
                message: format!("Failed to read file: {}", path.display()),
                source: e,
            })?;

        // Cache the result
        self.file_cache.put(path, content.clone()).await;

        Ok(content)
    }

    pub async fn fetch_url(&self, url: &str) -> AsyncResult<String> {
        let response = self.http_client
            .get(url)
            .timeout(Duration::from_secs(30))
            .send()
            .await
            .map_err(|e| AsyncError::Network {
                message: format!("Failed to fetch URL: {}", url),
                source: Box::new(e),
            })?;

        let content = response
            .text()
            .await
            .map_err(|e| AsyncError::Network {
                message: format!("Failed to read response from: {}", url),
                source: Box::new(e),
            })?;

        Ok(content)
    }

    pub async fn read_json_file(&self, path: &Path) -> AsyncResult<serde_json::Value> {
        let content = self.read_file(path).await?;

        serde_json::from_str(&content)
            .map_err(|e| AsyncError::Evaluation {
                message: format!("Failed to parse JSON from: {}", path.display()),
                source: Box::new(e),
            })
    }

    pub async fn fetch_json(&self, url: &str) -> AsyncResult<serde_json::Value> {
        let content = self.fetch_url(url).await?;

        serde_json::from_str(&content)
            .map_err(|e| AsyncError::Evaluation {
                message: format!("Failed to parse JSON from: {}", url),
                source: Box::new(e),
            })
    }
}
```

### 3. Stream-Based Processing

#### Large Data Processing

```rust
use tokio::sync::mpsc;
use futures::stream::{self, StreamExt};

pub struct StreamProcessor {
    buffer_size: usize,
    chunk_size: usize,
}

impl StreamProcessor {
    pub fn new(buffer_size: usize, chunk_size: usize) -> Self {
        Self {
            buffer_size,
            chunk_size,
        }
    }

    pub async fn process_large_file(&self, path: &Path) -> AsyncResult<Value> {
        let file = tokio::fs::File::open(path)
            .await
            .map_err(|e| AsyncError::Io {
                message: format!("Failed to open file: {}", path.display()),
                source: e,
            })?;

        let reader = tokio::io::BufReader::new(file);
        let lines = tokio::io::AsyncBufReadExt::lines(reader);

        let processed_lines = lines
            .map(|line_result| {
                line_result
                    .map_err(|e| AsyncError::Io {
                        message: "Failed to read line".to_string(),
                        source: e,
                    })
                    .and_then(|line| self.process_line(&line))
            })
            .chunks(self.chunk_size)
            .map(|chunk| {
                let chunk: Vec<_> = chunk.collect();
                self.process_chunk(chunk)
            });

        // Process stream
        let mut results = Vec::new();
        tokio::pin!(processed_lines);

        while let Some(result) = processed_lines.next().await {
            results.push(result?);
        }

        // Combine results
        self.combine_results(results)
    }

    pub async fn process_stream<T>(&self, stream: impl Stream<Item = T> + Send) -> AsyncResult<Value>
    where
        T: Send + 'static,
    {
        let processed = stream
            .map(|item| self.process_item(item))
            .chunks(self.chunk_size)
            .map(|chunk| {
                let chunk: Vec<_> = chunk.collect();
                self.process_chunk(chunk)
            });

        // Process stream
        let mut results = Vec::new();
        tokio::pin!(processed);

        while let Some(result) = processed.next().await {
            results.push(result?);
        }

        // Combine results
        self.combine_results(results)
    }

    fn process_line(&self, line: &str) -> AsyncResult<Value> {
        // Process individual line
        // This would be customized based on the specific use case
        Ok(Value::String(line.to_string()))
    }

    fn process_chunk(&self, chunk: Vec<AsyncResult<Value>>) -> AsyncResult<Value> {
        // Process chunk of results
        let mut values = Vec::new();
        for result in chunk {
            values.push(result?);
        }

        Ok(Value::List(values))
    }

    fn process_item<T>(&self, item: T) -> AsyncResult<Value> {
        // Process individual item
        // This would be customized based on the specific use case
        Ok(Value::String(format!("{:?}", item)))
    }

    fn combine_results(&self, results: Vec<AsyncResult<Value>>) -> AsyncResult<Value> {
        // Combine all results
        let mut values = Vec::new();
        for result in results {
            values.push(result?);
        }

        Ok(Value::List(values))
    }
}
```

### 4. Progress Reporting

#### Evaluation Progress Tracking

```rust
use tokio::sync::broadcast;

pub struct ProgressTracker {
    sender: broadcast::Sender<EvaluationProgress>,
    receiver: broadcast::Receiver<EvaluationProgress>,
}

impl ProgressTracker {
    pub fn new() -> Self {
        let (sender, receiver) = broadcast::channel(100);

        Self {
            sender,
            receiver,
        }
    }

    pub fn subscribe(&self) -> broadcast::Receiver<EvaluationProgress> {
        self.sender.subscribe()
    }

    pub async fn report_progress(&self, progress: EvaluationProgress) {
        let _ = self.sender.send(progress);
    }

    pub async fn track_evaluation<F, T>(&self, total: usize, f: F) -> AsyncResult<T>
    where
        F: Future<Output = AsyncResult<T>> + Send,
    {
        let mut completed = 0;
        let start_time = std::time::Instant::now();

        // Create a future that reports progress
        let tracked_future = async {
            let result = f.await;

            // Report final progress
            let progress = EvaluationProgress {
                completed: total,
                total,
                current_operation: "Completed".to_string(),
                estimated_remaining: Duration::ZERO,
            };

            self.report_progress(progress).await;

            result
        };

        // Execute with progress reporting
        tracked_future.await
    }
}

// Progress-aware evaluator
pub struct ProgressAwareEvaluator {
    evaluator: AsyncEvaluator,
    progress_tracker: ProgressTracker,
}

impl ProgressAwareEvaluator {
    pub fn new(config: AsyncEvaluatorConfig) -> Self {
        let evaluator = AsyncEvaluator::new(config);
        let progress_tracker = ProgressTracker::new();

        Self {
            evaluator,
            progress_tracker,
        }
    }

    pub async fn evaluate_with_progress(&self, program: &Program) -> AsyncResult<Value> {
        let total_operations = self.count_operations(program);

        self.progress_tracker
            .track_evaluation(total_operations, async {
                self.evaluator.evaluate_program(program).await
            })
            .await
    }

    pub fn subscribe_to_progress(&self) -> broadcast::Receiver<EvaluationProgress> {
        self.progress_tracker.subscribe()
    }

    fn count_operations(&self, program: &Program) -> usize {
        // Count total operations for progress tracking
        program.declarations.len()
    }
}
```

### 5. Resource Management

#### Memory and CPU Management

```rust
use tokio::sync::Semaphore;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct ResourceManager {
    memory_limit: usize,
    cpu_limit: usize,
    memory_usage: AtomicUsize,
    cpu_semaphore: Arc<Semaphore>,
}

impl ResourceManager {
    pub fn new(memory_limit: usize, cpu_limit: usize) -> Self {
        Self {
            memory_limit,
            cpu_limit,
            memory_usage: AtomicUsize::new(0),
            cpu_semaphore: Arc::new(Semaphore::new(cpu_limit)),
        }
    }

    pub async fn with_memory_limit<F, T>(&self, limit: usize, f: F) -> AsyncResult<T>
    where
        F: Future<Output = AsyncResult<T>> + Send,
    {
        let current_usage = self.memory_usage.load(Ordering::Relaxed);

        if current_usage + limit > self.memory_limit {
            return Err(AsyncError::ResourceExhausted {
                message: format!("Memory limit exceeded: {} + {} > {}",
                               current_usage, limit, self.memory_limit),
            });
        }

        // Reserve memory
        self.memory_usage.fetch_add(limit, Ordering::Relaxed);

        let result = f.await;

        // Release memory
        self.memory_usage.fetch_sub(limit, Ordering::Relaxed);

        result
    }

    pub async fn with_cpu_limit<F, T>(&self, f: F) -> AsyncResult<T>
    where
        F: Future<Output = AsyncResult<T>> + Send,
    {
        let _permit = self.cpu_semaphore
            .acquire()
            .await
            .map_err(|_| AsyncError::ResourceExhausted {
                message: "CPU limit exceeded".to_string(),
            })?;

        f.await
    }

    pub fn current_memory_usage(&self) -> usize {
        self.memory_usage.load(Ordering::Relaxed)
    }

    pub fn current_cpu_usage(&self) -> usize {
        self.cpu_limit - self.cpu_semaphore.available_permits()
    }
}

// Resource-aware evaluator
pub struct ResourceAwareEvaluator {
    evaluator: AsyncEvaluator,
    resource_manager: Arc<ResourceManager>,
}

impl ResourceAwareEvaluator {
    pub fn new(config: AsyncEvaluatorConfig, memory_limit: usize, cpu_limit: usize) -> Self {
        let evaluator = AsyncEvaluator::new(config);
        let resource_manager = Arc::new(ResourceManager::new(memory_limit, cpu_limit));

        Self {
            evaluator,
            resource_manager,
        }
    }

    pub async fn evaluate_with_resources(&self, program: &Program) -> AsyncResult<Value> {
        let estimated_memory = self.estimate_memory_usage(program);

        self.resource_manager
            .with_memory_limit(estimated_memory, async {
                self.resource_manager
                    .with_cpu_limit(async {
                        self.evaluator.evaluate_program(program).await
                    })
                    .await
            })
            .await
    }

    fn estimate_memory_usage(&self, program: &Program) -> usize {
        // Estimate memory usage based on program size
        program.declarations.len() * 1024 // Rough estimate
    }
}
```

## Implementation Strategy

### Phase 1: Basic Async Support (Immediate - 2-3 weeks)

#### Goals

- Add tokio dependency
- Implement basic async evaluator
- Add async result types

#### Implementation Tasks

1. **Add Dependencies**

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"
reqwest = { version = "0.11", features = ["json"] }
serde_json = "1.0"
```

2. **Basic Async Types**

```rust
use tokio::sync::{mpsc, oneshot};
use futures::{Stream, StreamExt};

pub type AsyncResult<T> = Result<T, AsyncError>;

#[derive(Debug, thiserror::Error)]
pub enum AsyncError {
    #[error("Evaluation timeout: {message}")]
    Timeout { message: String, duration: Duration },

    #[error("Evaluation cancelled")]
    Cancelled,

    #[error("I/O error: {message}")]
    Io { message: String, #[source] source: std::io::Error },
}
```

3. **Basic Async Evaluator**

```rust
pub struct AsyncEvaluator {
    runtime: tokio::runtime::Runtime,
    config: AsyncEvaluatorConfig,
}

impl AsyncEvaluator {
    pub fn new(config: AsyncEvaluatorConfig) -> Self {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(config.worker_threads)
            .enable_all()
            .build()
            .unwrap();

        Self { runtime, config }
    }

    pub async fn evaluate_program(&self, program: &Program) -> AsyncResult<Value> {
        // Basic async evaluation implementation
        let result = self.evaluate_sync_program(program)?;
        Ok(result)
    }
}
```

### Phase 2: Async I/O Operations (Short-term - 4-6 weeks)

#### Goals

- Implement async file operations
- Add network request support
- Implement caching

#### Implementation Tasks

1. **Async I/O Operations**

```rust
pub struct AsyncIoOperations {
    http_client: reqwest::Client,
    file_cache: Arc<AsyncCache>,
}

impl AsyncIoOperations {
    pub async fn read_file(&self, path: &Path) -> AsyncResult<String> {
        tokio::fs::read_to_string(path)
            .await
            .map_err(|e| AsyncError::Io {
                message: format!("Failed to read file: {}", path.display()),
                source: e,
            })
    }

    pub async fn fetch_url(&self, url: &str) -> AsyncResult<String> {
        let response = self.http_client
            .get(url)
            .timeout(Duration::from_secs(30))
            .send()
            .await
            .map_err(|e| AsyncError::Network {
                message: format!("Failed to fetch URL: {}", url),
                source: Box::new(e),
            })?;

        response.text().await
            .map_err(|e| AsyncError::Network {
                message: format!("Failed to read response from: {}", url),
                source: Box::new(e),
            })
    }
}
```

2. **Async Cache**

```rust
pub struct AsyncCache {
    cache: Arc<dashmap::DashMap<String, String>>,
    max_size: usize,
}

impl AsyncCache {
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: Arc::new(dashmap::DashMap::new()),
            max_size,
        }
    }

    pub async fn get(&self, key: &str) -> Option<String> {
        self.cache.get(key).map(|entry| entry.clone())
    }

    pub async fn put(&self, key: String, value: String) {
        if self.cache.len() >= self.max_size {
            // Evict oldest entries
            self.evict_oldest();
        }

        self.cache.insert(key, value);
    }
}
```

### Phase 3: Stream Processing (Medium-term - 6-8 weeks)

#### Goals

- Implement stream-based processing
- Add parallel evaluation
- Implement progress tracking

#### Implementation Tasks

1. **Stream Processor**

```rust
pub struct StreamProcessor {
    buffer_size: usize,
    chunk_size: usize,
}

impl StreamProcessor {
    pub async fn process_large_file(&self, path: &Path) -> AsyncResult<Value> {
        let file = tokio::fs::File::open(path).await?;
        let reader = tokio::io::BufReader::new(file);
        let lines = tokio::io::AsyncBufReadExt::lines(reader);

        let processed_lines = lines
            .map(|line_result| {
                line_result
                    .map_err(|e| AsyncError::Io {
                        message: "Failed to read line".to_string(),
                        source: e,
                    })
                    .and_then(|line| self.process_line(&line))
            })
            .chunks(self.chunk_size);

        // Process stream
        let mut results = Vec::new();
        tokio::pin!(processed_lines);

        while let Some(chunk) = processed_lines.next().await {
            results.push(self.process_chunk(chunk).await?);
        }

        self.combine_results(results)
    }
}
```

2. **Progress Tracking**

```rust
pub struct ProgressTracker {
    sender: broadcast::Sender<EvaluationProgress>,
    receiver: broadcast::Receiver<EvaluationProgress>,
}

impl ProgressTracker {
    pub async fn report_progress(&self, progress: EvaluationProgress) {
        let _ = self.sender.send(progress);
    }

    pub fn subscribe(&self) -> broadcast::Receiver<EvaluationProgress> {
        self.sender.subscribe()
    }
}
```

### Phase 4: Advanced Features (Long-term - 8-12 weeks)

#### Goals

- Implement resource management
- Add retry logic
- Implement advanced caching

#### Implementation Tasks

1. **Resource Manager**

```rust
pub struct ResourceManager {
    memory_limit: usize,
    cpu_limit: usize,
    memory_usage: AtomicUsize,
    cpu_semaphore: Arc<Semaphore>,
}

impl ResourceManager {
    pub async fn with_memory_limit<F, T>(&self, limit: usize, f: F) -> AsyncResult<T>
    where
        F: Future<Output = AsyncResult<T>> + Send,
    {
        // Check memory limit
        let current_usage = self.memory_usage.load(Ordering::Relaxed);

        if current_usage + limit > self.memory_limit {
            return Err(AsyncError::ResourceExhausted {
                message: "Memory limit exceeded".to_string(),
            });
        }

        // Reserve and release memory
        self.memory_usage.fetch_add(limit, Ordering::Relaxed);
        let result = f.await;
        self.memory_usage.fetch_sub(limit, Ordering::Relaxed);

        result
    }
}
```

2. **Retry Logic**

```rust
pub async fn evaluate_with_retry<F>(f: F, config: &RetryConfig) -> AsyncResult<Value>
where
    F: Future<Output = AsyncResult<Value>> + Send,
{
    let mut attempt = 0;
    let mut backoff = config.backoff.clone();

    loop {
        match f.await {
            Ok(value) => return Ok(value),
            Err(error) => {
                attempt += 1;

                if attempt >= config.max_attempts {
                    return Err(error);
                }

                if !(config.retry_condition)(&error) {
                    return Err(error);
                }

                let delay = backoff.next_delay(attempt);
                tokio::time::sleep(delay).await;
            }
        }
    }
}
```

## Configuration and Usage

### Basic Usage

```rust
use ligature_async::AsyncEvaluator;

#[tokio::main]
async fn main() -> Result<()> {
    let config = AsyncEvaluatorConfig {
        max_concurrent_tasks: 16,
        worker_threads: 8,
        cache_size: 10000,
        timeout: Duration::from_secs(30),
        enable_progress: true,
    };

    let evaluator = AsyncEvaluator::new(config);

    let program = parse_program("large_config.lig")?;
    let result = evaluator.evaluate_program(&program).await?;

    println!("Result: {:?}", result);
    Ok(())
}
```

### Advanced Usage

```rust
use ligature_async::{AsyncEvaluator, ProgressTracker, ResourceManager};

#[tokio::main]
async fn main() -> Result<()> {
    let config = AsyncEvaluatorConfig::default();
    let evaluator = AsyncEvaluator::new(config);

    let progress_tracker = ProgressTracker::new();
    let resource_manager = Arc::new(ResourceManager::new(1024 * 1024 * 1024, 8)); // 1GB, 8 cores

    // Subscribe to progress updates
    let mut progress_receiver = progress_tracker.subscribe();

    tokio::spawn(async move {
        while let Ok(progress) = progress_receiver.recv().await {
            println!("Progress: {}/{} - {}",
                    progress.completed, progress.total, progress.current_operation);
        }
    });

    // Evaluate with resource limits
    let result = resource_manager
        .with_memory_limit(1024 * 1024 * 100, async { // 100MB limit
            evaluator.evaluate_program(&program).await
        })
        .await?;

    println!("Result: {:?}", result);
    Ok(())
}
```

### CLI Integration

```rust
use clap::Parser;

#[derive(Parser)]
struct Cli {
    #[arg(short, long)]
    file: PathBuf,

    #[arg(short, long, default_value = "8")]
    workers: usize,

    #[arg(short, long, default_value = "30")]
    timeout: u64,

    #[arg(short, long)]
    progress: bool,
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    let config = AsyncEvaluatorConfig {
        max_concurrent_tasks: cli.workers * 2,
        worker_threads: cli.workers,
        cache_size: 10000,
        timeout: Duration::from_secs(cli.timeout),
        enable_progress: cli.progress,
    };

    let evaluator = AsyncEvaluator::new(config);

    let source = tokio::fs::read_to_string(&cli.file).await?;
    let program = parse_program(&source)?;

    let result = evaluator.evaluate_program(&program).await?;
    println!("{:?}", result);

    Ok(())
}
```

## Testing Strategy

### Unit Tests

```rust
#[tokio::test]
async fn test_async_evaluation() {
    let config = AsyncEvaluatorConfig::default();
    let evaluator = AsyncEvaluator::new(config);

    let program = create_test_program();
    let result = evaluator.evaluate_program(&program).await;

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_async_io_operations() {
    let io_ops = AsyncIoOperations::new();

    // Test file reading
    let content = io_ops.read_file(Path::new("test.lig")).await;
    assert!(content.is_ok());

    // Test URL fetching (with mock server)
    let content = io_ops.fetch_url("http://localhost:8080/test").await;
    assert!(content.is_ok());
}
```

### Integration Tests

```rust
#[tokio::test]
async fn test_large_file_processing() {
    let processor = StreamProcessor::new(1024, 100);

    // Create large test file
    let test_file = create_large_test_file(1024 * 1024); // 1MB

    let result = processor.process_large_file(&test_file).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_progress_tracking() {
    let tracker = ProgressTracker::new();
    let mut receiver = tracker.subscribe();

    let progress = EvaluationProgress {
        completed: 5,
        total: 10,
        current_operation: "Processing".to_string(),
        estimated_remaining: Duration::from_secs(5),
    };

    tracker.report_progress(progress.clone()).await;

    let received = receiver.recv().await.unwrap();
    assert_eq!(received.completed, 5);
    assert_eq!(received.total, 10);
}
```

### Performance Tests

```rust
#[tokio::test]
async fn test_async_performance() {
    let config = AsyncEvaluatorConfig {
        max_concurrent_tasks: 16,
        worker_threads: 8,
        cache_size: 10000,
        timeout: Duration::from_secs(30),
        enable_progress: false,
    };

    let evaluator = AsyncEvaluator::new(config);
    let large_program = create_large_program();

    let start = std::time::Instant::now();
    let result = evaluator.evaluate_program(&large_program).await;
    let duration = start.elapsed();

    assert!(result.is_ok());
    assert!(duration < Duration::from_secs(10));
}
```

## Migration Strategy

### Backward Compatibility

1. **Optional Feature**: Async evaluation is additive and doesn't affect existing code
2. **Gradual Migration**: Users can opt into async features incrementally
3. **Feature Flags**: Enable/disable async features via configuration
4. **Fallback Support**: Automatic fallback to synchronous evaluation

### Migration Path

1. **Phase 1**: Add async support without changing public APIs
2. **Phase 2**: Add async variants of existing functions
3. **Phase 3**: Deprecate synchronous versions for large configurations
4. **Phase 4**: Make async the default for large configurations

### Migration Examples

```rust
// Before: Synchronous evaluation
let evaluator = Evaluator::new();
let result = evaluator.evaluate_program(&program)?;

// After: Async evaluation (optional)
let evaluator = AsyncEvaluator::new(config);
let result = evaluator.evaluate_program(&program).await?;

// Before: Synchronous file reading
let content = std::fs::read_to_string(&path)?;

// After: Async file reading
let content = tokio::fs::read_to_string(&path).await?;
```

## Risks and Mitigations

### 1. Complexity Increase

**Risk**: Async code is more complex and harder to debug
**Mitigation**:

- Comprehensive testing and documentation
- Clear async patterns and conventions
- Gradual introduction with fallback options
- Debugging tools and logging

### 2. Performance Overhead

**Risk**: Async overhead may not be worth it for small configurations
**Mitigation**:

- Automatic detection of when to use async
- Configurable thresholds
- Performance monitoring and metrics
- Fallback to synchronous processing

### 3. Resource Management

**Risk**: Async operations may consume excessive resources
**Mitigation**:

- Resource limits and monitoring
- Efficient async implementations
- Memory and CPU management
- Graceful degradation

### 4. Error Handling

**Risk**: Async errors may be more complex to handle
**Mitigation**:

- Comprehensive error types
- Clear error messages and context
- Error recovery strategies
- Proper error propagation

## Success Metrics

### Technical Metrics

1. **Performance**: Speedup for large configurations
2. **Resource Usage**: Memory and CPU efficiency
3. **Scalability**: Performance scaling with configuration size
4. **Reliability**: Success rate of async operations

### User Experience Metrics

1. **Response Time**: Time to first result
2. **Progress Visibility**: User satisfaction with progress reporting
3. **Resource Efficiency**: User satisfaction with resource usage
4. **Error Handling**: User satisfaction with error messages

## Conclusion

This proposal provides a comprehensive approach to implementing async evaluation in Ligature. The gradual introduction ensures minimal disruption while providing significant benefits for large configuration processing.

The key benefits include:

1. **Better Performance**: Non-blocking evaluation for large configurations
2. **I/O Support**: Async file and network operations
3. **Resource Efficiency**: Better memory and CPU management
4. **Progress Tracking**: Visibility into long-running operations
5. **Scalability**: Performance that scales with configuration size

The implementation strategy provides a clear path forward with measurable milestones and comprehensive testing to ensure effectiveness and reliability.

## References

1. [Tokio Documentation](https://tokio.rs/)
2. [Rust Async Book](https://rust-lang.github.io/async-book/)
3. [Futures Documentation](https://docs.rs/futures/)
4. [Async Programming Patterns](https://en.wikipedia.org/wiki/Asynchronous_programming)
5. [Stream Processing](https://en.wikipedia.org/wiki/Stream_processing)
