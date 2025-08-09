//! Parallel evaluation for the Ligature language.
//!
//! This module provides parallel evaluation capabilities including
//! work distribution, task scheduling, and concurrent execution.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use dashmap::DashMap;
#[allow(unused_imports)]
use ligature_ast::{Expr, Program, Span, Type};
use ligature_error::{StandardError, StandardResult};
use uuid::Uuid;

use crate::environment::EvaluationEnvironment;
use crate::value::Value;

/// Unique identifier for a task
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(Uuid);

impl TaskId {
    /// Create a new task ID
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

impl Default for TaskId {
    fn default() -> Self {
        Self::new()
    }
}

/// Status of a task
#[derive(Debug, Clone)]
pub enum TaskStatus {
    /// Task is pending execution
    Pending,
    /// Task is currently running
    Running,
    /// Task completed successfully
    Completed(Value),
    /// Task failed with an error
    Failed(String),
}

/// A task to be executed
#[derive(Debug, Clone)]
pub struct Task {
    /// Unique identifier for this task
    pub id: TaskId,
    /// The expression to evaluate
    pub expression: Expr,
    /// The environment for evaluation
    pub environment: EvaluationEnvironment,
    /// Task priority (higher = more important)
    pub priority: u32,
    /// Dependencies on other tasks
    pub dependencies: Vec<TaskId>,
    /// Current status
    pub status: TaskStatus,
}

impl Task {
    /// Create a new task
    pub fn new(expression: Expr, environment: EvaluationEnvironment) -> Self {
        Self {
            id: TaskId::new(),
            expression,
            environment,
            priority: 0,
            dependencies: Vec::new(),
            status: TaskStatus::Pending,
        }
    }

    /// Set the priority of this task
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }

    /// Add a dependency to this task
    pub fn with_dependency(mut self, dependency: TaskId) -> Self {
        self.dependencies.push(dependency);
        self
    }

    /// Check if this task is ready to execute
    pub fn is_ready(&self, completed_tasks: &DashMap<TaskId, TaskStatus>) -> bool {
        self.dependencies.iter().all(|dep_id| {
            if let Some(status) = completed_tasks.get(dep_id) {
                matches!(*status, TaskStatus::Completed(_))
            } else {
                false
            }
        })
    }
}

/// A work queue for managing tasks
#[derive(Debug)]
pub struct WorkQueue {
    /// Pending tasks
    pending: DashMap<TaskId, Task>,
    /// Completed tasks
    completed: DashMap<TaskId, TaskStatus>,
    /// Task priorities
    priorities: DashMap<TaskId, u32>,
    /// Shutdown flag
    shutdown: Arc<AtomicBool>,
}

impl WorkQueue {
    /// Create a new work queue
    pub fn new() -> Self {
        Self {
            pending: DashMap::new(),
            completed: DashMap::new(),
            priorities: DashMap::new(),
            shutdown: Arc::new(AtomicBool::new(false)),
        }
    }
}

impl Default for WorkQueue {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkQueue {
    /// Submit a task to the queue
    pub async fn submit(&self, task: Task) -> TaskId {
        let task_id = task.id;
        self.priorities.insert(task_id, task.priority);
        self.pending.insert(task_id, task);
        task_id
    }

    /// Get the next task to execute
    pub async fn get_next_task(&self) -> Option<Task> {
        // Find the highest priority task that's ready
        let mut best_task: Option<(TaskId, u32)> = None;

        for entry in self.pending.iter() {
            let task = entry.value();
            if task.is_ready(&self.completed) {
                let priority = self.priorities.get(&task.id).map(|p| *p).unwrap_or(0);

                if let Some((_, best_priority)) = best_task {
                    if priority > best_priority {
                        best_task = Some((task.id, priority));
                    }
                } else {
                    best_task = Some((task.id, priority));
                }
            }
        }

        if let Some((task_id, _)) = best_task {
            self.pending.remove(&task_id).map(|(_, task)| task)
        } else {
            None
        }
    }

    /// Mark a task as completed
    pub async fn complete_task(&self, task_id: TaskId, result: StandardResult<Value>) {
        let status = match result {
            Ok(value) => TaskStatus::Completed(value),
            Err(error) => TaskStatus::Failed(error.to_string()),
        };

        self.completed.insert(task_id, status);
    }

    /// Check if all tasks are completed
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// Get the number of pending tasks
    pub fn len(&self) -> usize {
        self.pending.len()
    }

    /// Signal shutdown
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::Relaxed);
    }

    /// Check if shutdown is requested
    pub fn is_shutdown(&self) -> bool {
        self.shutdown.load(Ordering::Relaxed)
    }
}

/// A worker for executing tasks
#[derive(Debug)]
pub struct Worker {
    /// Worker ID
    pub id: usize,
    /// Reference to the work queue
    queue: Arc<WorkQueue>,
    /// Evaluation environment
    environment: EvaluationEnvironment,
}

impl Worker {
    /// Create a new worker
    pub fn new(id: usize, queue: Arc<WorkQueue>, environment: EvaluationEnvironment) -> Self {
        Self {
            id,
            queue,
            environment,
        }
    }

    /// Run the worker loop
    pub async fn run(&self) {
        loop {
            // Check for shutdown
            if self.queue.is_shutdown() {
                break;
            }

            if let Some(task) = self.queue.get_next_task().await {
                // Extract task ID before moving the task
                let task_id = task.id;

                // Process task
                let result = self.process_task(task).await;

                // Mark task as completed
                self.queue.complete_task(task_id, result).await;
            } else {
                // No tasks available, wait a bit
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    /// Process a single task
    async fn process_task(&self, task: Task) -> StandardResult<Value> {
        // Simple evaluation (in a real implementation, this would use the full evaluator)
        match task.status {
            TaskStatus::Pending => {
                // Evaluate the expression
                self.evaluate_expression(&task.expression, &task.environment)
                    .await
            }
            TaskStatus::Running => {
                Err(StandardError::Internal("Task is already running".to_string()).into())
            }
            TaskStatus::Completed(value) => Ok(value),
            TaskStatus::Failed(error) => Err(StandardError::Internal(error.to_string())),
        }
    }

    /// Evaluate an expression
    async fn evaluate_expression(
        &self,
        expr: &Expr,
        env: &EvaluationEnvironment,
    ) -> StandardResult<Value> {
        match &expr.kind {
            ligature_ast::ExprKind::Literal(literal) => {
                match literal {
                    ligature_ast::Literal::Integer(i) => Ok(Value::integer(*i, expr.span.clone())),
                    ligature_ast::Literal::Float(f) => Ok(Value::float(*f, expr.span.clone())),
                    ligature_ast::Literal::String(s) => {
                        Ok(Value::string(s.clone(), expr.span.clone()))
                    }
                    ligature_ast::Literal::Boolean(b) => Ok(Value::boolean(*b, expr.span.clone())),
                    ligature_ast::Literal::Unit => Ok(Value::unit(expr.span.clone())),
                    ligature_ast::Literal::List(_) => {
                        // Simplified list evaluation
                        Ok(Value::list(Vec::new(), expr.span.clone()))
                    }
                }
            }
            ligature_ast::ExprKind::Variable(name) => env.lookup(name).ok_or_else(|| {
                StandardError::Internal(format!("Variable '{}' not found", name)).into()
            }),
            _ => {
                // Simplified evaluation for other expression types
                Err(
                    StandardError::Internal("Expression type not yet implemented".to_string())
                        .into(),
                )
            }
        }
    }
}

/// Configuration for the parallel evaluator
#[derive(Debug, Clone)]
pub struct ParallelEvaluatorConfig {
    /// Number of worker threads
    pub num_workers: usize,
    /// Maximum number of tasks in the queue
    pub max_queue_size: usize,
    /// Task timeout
    pub task_timeout: Duration,
    /// Whether to enable task prioritization
    pub enable_prioritization: bool,
}

impl Default for ParallelEvaluatorConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus::get(),
            max_queue_size: 1000,
            task_timeout: Duration::from_secs(30),
            enable_prioritization: true,
        }
    }
}

/// A parallel evaluator for Ligature programs
#[derive(Debug)]
pub struct ParallelEvaluator {
    /// Work queue
    work_queue: Arc<WorkQueue>,
    /// Workers
    workers: Vec<Worker>,
    /// Configuration
    config: ParallelEvaluatorConfig,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ParallelEvaluator {
    /// Create a new parallel evaluator
    pub fn new(config: ParallelEvaluatorConfig) -> Self {
        let work_queue = Arc::new(WorkQueue::new());
        let mut workers = Vec::new();

        for i in 0..config.num_workers {
            let worker = Worker::new(i, Arc::clone(&work_queue), EvaluationEnvironment::new());
            workers.push(worker);
        }

        Self {
            work_queue,
            workers,
            config,
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Evaluate a program in parallel
    pub async fn evaluate_program(&self, program: &Program) -> StandardResult<Vec<Value>> {
        // Create tasks for each declaration
        let mut task_handles = Vec::new();

        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                let task = Task::new(value_decl.value.clone(), EvaluationEnvironment::new());

                let task_id = self.work_queue.submit(task).await;
                task_handles.push(task_id);
            }
        }

        // Start workers
        let worker_handles: Vec<_> = self
            .workers
            .iter()
            .map(|worker| {
                let worker = worker.clone();
                tokio::spawn(async move {
                    worker.run().await;
                })
            })
            .collect();

        // Wait for all tasks to complete with timeout
        let timeout = self.config.task_timeout;
        match tokio::time::timeout(timeout, async {
            loop {
                if self.work_queue.is_empty() {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        {
            Ok(_) => {
                // Signal shutdown to workers
                self.work_queue.shutdown();

                // Wait for workers to complete
                for handle in worker_handles {
                    let _ = handle.await;
                }

                // Collect results
                let mut results = Vec::new();
                for task_id in task_handles {
                    if let Some(status) = self.work_queue.completed.get(&task_id) {
                        match &*status {
                            TaskStatus::Completed(value) => results.push(value.clone()),
                            TaskStatus::Failed(error) => {
                                return Err(StandardError::Internal(error.to_string()));
                            }
                            _ => {
                                return Err(StandardError::Internal(
                                    "Task not completed".to_string(),
                                )
                                .into());
                            }
                        }
                    }
                }

                Ok(results)
            }
            Err(_) => {
                // Signal shutdown to workers on timeout
                self.work_queue.shutdown();

                // Wait for workers to complete
                for handle in worker_handles {
                    let _ = handle.await;
                }

                Err(StandardError::Internal("Parallel evaluation timed out".to_string()).into())
            }
        }
    }

    /// Get evaluator statistics
    pub fn stats(&self) -> std::collections::HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }
}

impl Clone for Worker {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            queue: Arc::clone(&self.queue),
            environment: self.environment.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::{Expr, ExprKind, Literal, Span};

    use super::*;

    #[tokio::test]
    async fn test_work_queue() {
        let queue = WorkQueue::new();

        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };

        let task = Task::new(expr, EvaluationEnvironment::new());
        let task_id = queue.submit(task).await;

        assert_eq!(queue.len(), 1);
        assert!(!queue.is_empty());

        if let Some(_task) = queue.get_next_task().await {
            let result = Value::integer(42, Span::default());
            queue.complete_task(task_id, Ok(result)).await;
        }

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
    }

    #[tokio::test]
    async fn test_parallel_evaluator() {
        let config = ParallelEvaluatorConfig {
            num_workers: 2,
            max_queue_size: 100,
            task_timeout: Duration::from_secs(5),
            enable_prioritization: true,
        };

        let evaluator = ParallelEvaluator::new(config);

        let program = Program {
            declarations: vec![ligature_ast::Declaration::value(
                "x".to_string(),
                Some(Type::integer(Span::default())),
                Expr {
                    kind: ExprKind::Literal(Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            )],
        };

        let results = evaluator.evaluate_program(&program).await;
        assert!(results.is_ok());
    }
}
