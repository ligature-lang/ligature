//! Concurrent type checker for Ligature.
//!
//! This module provides parallel type checking capabilities including
//! concurrent type inference, constraint solving, and module-level parallelism.

use std::sync::Arc;
use std::time::Duration;

use dashmap::DashMap;
use futures::future::join_all;
use ligature_ast::{AstError, AstResult, Expr, Module, Program, Span, Type, TypeKind};
use uuid::Uuid;

use crate::concurrent::ConcurrentTypeEnvironment;

/// Unique identifier for a constraint
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstraintId(Uuid);

impl ConstraintId {
    /// Create a new constraint ID
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

impl Default for ConstraintId {
    fn default() -> Self {
        Self::new()
    }
}

/// A type constraint to be solved
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Unique identifier for this constraint
    pub id: ConstraintId,
    /// Left-hand side of the constraint
    pub left: Type,
    /// Right-hand side of the constraint
    pub right: Type,
    /// Source expression for this constraint
    pub source: Option<Expr>,
    /// Whether this constraint has been solved
    pub solved: bool,
}

impl Constraint {
    /// Create a new constraint
    pub fn new(left: Type, right: Type) -> Self {
        Self {
            id: ConstraintId::new(),
            left,
            right,
            source: None,
            solved: false,
        }
    }

    /// Create a constraint with source expression
    pub fn with_source(mut self, source: Expr) -> Self {
        self.source = Some(source);
        self
    }

    /// Check if this constraint is solved
    pub fn is_solved(&self) -> bool {
        self.solved
    }

    /// Mark this constraint as solved
    pub fn mark_solved(&mut self) {
        self.solved = true;
    }
}

/// A solution to a type constraint
#[derive(Debug, Clone)]
pub struct Solution {
    /// The constraint this solution applies to
    pub constraint_id: ConstraintId,
    /// The substitution that solves the constraint
    pub substitution: TypeSubstitution,
    /// Whether this solution is valid
    pub valid: bool,
}

/// A type substitution (mapping from type variables to types)
#[derive(Debug, Clone)]
pub struct TypeSubstitution {
    /// The substitution map
    pub substitutions: std::collections::HashMap<String, Type>,
}

impl TypeSubstitution {
    /// Create a new empty substitution
    pub fn new() -> Self {
        Self {
            substitutions: std::collections::HashMap::new(),
        }
    }

    /// Add a substitution
    pub fn add(&mut self, var: String, type_: Type) {
        self.substitutions.insert(var, type_);
    }

    /// Apply this substitution to a type
    pub fn apply(&self, type_: &Type) -> Type {
        match &type_.kind {
            TypeKind::Variable(name) => {
                if let Some(substituted_type) = self.substitutions.get(name) {
                    substituted_type.clone()
                } else {
                    type_.clone()
                }
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => Type::function(self.apply(parameter), self.apply(return_type), type_.span),
            TypeKind::Record { fields } => {
                let new_fields = fields
                    .iter()
                    .map(|field| ligature_ast::TypeField {
                        name: field.name.clone(),
                        type_: self.apply(&field.type_),
                        span: field.span,
                    })
                    .collect();
                Type::record(new_fields, type_.span)
            }
            TypeKind::Union { variants } => {
                let new_variants = variants
                    .iter()
                    .map(|variant| ligature_ast::TypeVariant {
                        name: variant.name.clone(),
                        type_: variant.type_.as_ref().map(|t| self.apply(t)),
                        span: variant.span,
                    })
                    .collect();
                Type::union(new_variants, type_.span)
            }
            TypeKind::List(element_type) => Type::list(self.apply(element_type), type_.span),
            _ => type_.clone(),
        }
    }

    /// Compose this substitution with another
    pub fn compose(&self, other: &TypeSubstitution) -> TypeSubstitution {
        let mut result = TypeSubstitution::new();

        // Add all substitutions from self
        for (var, type_) in &self.substitutions {
            result.add(var.clone(), other.apply(type_));
        }

        // Add substitutions from other that aren't in self
        for (var, type_) in &other.substitutions {
            if !self.substitutions.contains_key(var) {
                result.add(var.clone(), type_.clone());
            }
        }

        result
    }
}

impl Default for TypeSubstitution {
    fn default() -> Self {
        Self::new()
    }
}

/// Concurrent constraint solver
#[derive(Debug, Clone)]
pub struct ConcurrentConstraintSolver {
    /// All constraints to be solved
    constraints: Arc<DashMap<ConstraintId, Constraint>>,
    /// Solutions found
    solutions: Arc<DashMap<ConstraintId, Solution>>,
    /// Workers for solving constraints
    workers: Vec<ConstraintSolverWorker>,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

/// Worker for solving constraints
#[derive(Debug, Clone)]
pub struct ConstraintSolverWorker {
    /// Worker ID
    pub id: usize,
    /// Reference to the constraint solver's data
    constraints: Arc<DashMap<ConstraintId, Constraint>>,
    solutions: Arc<DashMap<ConstraintId, Solution>>,
    stats: Arc<DashMap<String, usize>>,
}

impl ConstraintSolverWorker {
    /// Create a new worker
    pub fn new(id: usize, solver: Arc<ConcurrentConstraintSolver>) -> Self {
        Self {
            id,
            constraints: Arc::clone(&solver.constraints),
            solutions: Arc::clone(&solver.solutions),
            stats: Arc::clone(&solver.stats),
        }
    }

    /// Run the worker
    pub async fn run(&self) {
        println!("Worker {} starting", self.id);
        loop {
            // Get next constraint to solve
            if let Some((constraint_id, constraint)) = self.get_next_constraint().await {
                println!(
                    "Worker {} processing constraint {:?}",
                    self.id, constraint_id
                );
                // Solve the constraint
                let solution = self.solve_constraint(&constraint).await;

                // Store the solution
                self.solutions.insert(constraint_id.clone(), solution);

                // Remove the solved constraint
                self.constraints.remove(&constraint_id);

                // Update statistics
                self.stats
                    .entry("constraints_solved".to_string())
                    .and_modify(|count| *count += 1)
                    .or_insert(1);
            } else {
                println!("Worker {} found no constraints, exiting", self.id);
                // No more constraints, exit
                break;
            }
        }
    }

    /// Get the next constraint to solve
    async fn get_next_constraint(&self) -> Option<(ConstraintId, Constraint)> {
        self.constraints
            .iter()
            .next()
            .map(|entry| (entry.key().clone(), entry.clone()))
    }

    /// Solve a single constraint
    async fn solve_constraint(&self, constraint: &Constraint) -> Solution {
        // Simple unification-based constraint solving
        let substitution = self.unify(&constraint.left, &constraint.right);

        Solution {
            constraint_id: constraint.id.clone(),
            substitution,
            valid: true,
        }
    }

    /// Unify two types
    #[allow(clippy::only_used_in_recursion)]
    fn unify(&self, left: &Type, right: &Type) -> TypeSubstitution {
        let mut substitution = TypeSubstitution::new();

        match (&left.kind, &right.kind) {
            (TypeKind::Variable(name), _) => {
                substitution.add(name.clone(), right.clone());
            }
            (_, TypeKind::Variable(name)) => {
                substitution.add(name.clone(), left.clone());
            }
            (TypeKind::Integer, TypeKind::Integer)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::String, TypeKind::String)
            | (TypeKind::Float, TypeKind::Float)
            | (TypeKind::Unit, TypeKind::Unit) => {
                // Types are already unified
            }
            (
                TypeKind::Function {
                    parameter: p1,
                    return_type: r1,
                },
                TypeKind::Function {
                    parameter: p2,
                    return_type: r2,
                },
            ) => {
                let param_sub = self.unify(p1, p2);
                let return_sub = self.unify(r1, r2);
                substitution = param_sub.compose(&return_sub);
            }
            _ => {
                // Types cannot be unified
                substitution = TypeSubstitution::new();
            }
        }

        substitution
    }
}

impl ConcurrentConstraintSolver {
    /// Create a new concurrent constraint solver
    pub fn new(num_workers: usize) -> Self {
        let mut solver = Self {
            constraints: Arc::new(DashMap::new()),
            solutions: Arc::new(DashMap::new()),
            workers: Vec::new(),
            stats: Arc::new(DashMap::new()),
        };

        // Create workers after the solver is created
        for i in 0..num_workers {
            solver
                .workers
                .push(ConstraintSolverWorker::new(i, Arc::new(solver.clone())));
        }

        solver
    }

    /// Add a constraint to be solved
    pub fn add_constraint(&self, constraint: Constraint) {
        self.constraints.insert(constraint.id.clone(), constraint);
    }

    /// Solve all constraints in parallel
    pub async fn solve_parallel(&self) -> AstResult<Vec<Solution>> {
        let mut handles = Vec::new();

        // Start all workers
        for worker in &self.workers {
            let worker = worker.clone();
            handles.push(tokio::spawn(async move {
                worker.run().await;
            }));
        }

        // Wait for all workers to complete or timeout
        let timeout = Duration::from_secs(30);
        match tokio::time::timeout(timeout, join_all(handles)).await {
            Ok(_) => {
                // Collect all solutions
                let solutions: Vec<Solution> =
                    self.solutions.iter().map(|entry| entry.clone()).collect();
                Ok(solutions)
            }
            Err(_) => Err(AstError::InternalError {
                message: "Constraint solving timed out".to_string(),
                span: Span::default(),
            }),
        }
    }

    /// Get solver statistics
    pub fn stats(&self) -> std::collections::HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }
}

/// Concurrent type checker
#[derive(Debug, Clone)]
pub struct ConcurrentTypeChecker {
    /// Type environment
    type_environment: Arc<ConcurrentTypeEnvironment>,
    /// Constraint solver
    constraint_solver: Arc<ConcurrentConstraintSolver>,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ConcurrentTypeChecker {
    /// Create a new concurrent type checker
    pub fn new(num_workers: usize) -> Self {
        let constraint_solver = ConcurrentConstraintSolver::new(num_workers);

        Self {
            type_environment: Arc::new(ConcurrentTypeEnvironment::new()),
            constraint_solver: Arc::new(constraint_solver),
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Type check a program in parallel
    pub async fn check_program_parallel(&self, program: &Program) -> AstResult<()> {
        // Split program into modules for parallel processing
        let modules = self.split_into_modules(program);

        // Process modules in parallel
        let mut handles = Vec::new();
        for module in modules {
            let checker = self.clone();
            handles.push(tokio::spawn(
                async move { checker.check_module(module).await },
            ));
        }

        // Wait for all modules to be checked
        let results = join_all(handles).await;

        // Check for any errors
        for result in results {
            match result {
                Ok(Ok(())) => {}
                Ok(Err(error)) => return Err(error),
                Err(join_error) => {
                    return Err(AstError::InternalError {
                        message: format!("Task join error: {join_error}"),
                        span: Span::default(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Type check a module
    pub async fn check_module(&self, module: Module) -> AstResult<()> {
        // Check imports first
        for _import in &module.imports {
            // Handle imports (simplified)
        }

        // Check declarations in parallel
        let mut handles = Vec::new();
        for declaration in &module.declarations {
            let checker = self.clone();
            let decl = declaration.clone();
            handles.push(tokio::spawn(async move {
                checker.check_declaration(&decl).await
            }));
        }

        // Wait for all declarations to be checked
        let results = join_all(handles).await;

        // Check for any errors
        for result in results {
            match result {
                Ok(Ok(())) => {}
                Ok(Err(error)) => return Err(error),
                Err(join_error) => {
                    return Err(AstError::InternalError {
                        message: format!("Task join error: {join_error}"),
                        span: Span::default(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Type check a declaration
    pub async fn check_declaration(
        &self,
        declaration: &ligature_ast::Declaration,
    ) -> AstResult<()> {
        match &declaration.kind {
            ligature_ast::DeclarationKind::Value(value_decl) => {
                // Infer type of the value
                let inferred_type = self.infer_expression_type(&value_decl.value).await?;

                // Check type annotation if present
                if let Some(annotation) = &value_decl.type_annotation {
                    let constraint = Constraint::new(inferred_type.clone(), annotation.clone());
                    self.constraint_solver.add_constraint(constraint);
                }

                // Add to environment
                let final_type = value_decl
                    .type_annotation
                    .as_ref()
                    .unwrap_or(&inferred_type);
                self.type_environment
                    .bind(value_decl.name.clone(), final_type.clone());

                Ok(())
            }
            ligature_ast::DeclarationKind::Import(_) => {
                // Handle imports (simplified)
                Ok(())
            }
            _ => {
                // Handle other declaration types (simplified)
                Ok(())
            }
        }
    }

    /// Infer the type of an expression
    pub async fn infer_expression_type(&self, expr: &Expr) -> AstResult<Type> {
        match &expr.kind {
            ligature_ast::ExprKind::Literal(literal) => {
                match literal {
                    ligature_ast::Literal::Integer(_) => Ok(Type::integer(expr.span)),
                    ligature_ast::Literal::Float(_) => Ok(Type::float(expr.span)),
                    ligature_ast::Literal::String(_) => Ok(Type::string(expr.span)),
                    ligature_ast::Literal::Boolean(_) => Ok(Type::bool(expr.span)),
                    ligature_ast::Literal::Unit => Ok(Type::unit(expr.span)),
                    ligature_ast::Literal::List(_) => {
                        // Simplified list type inference
                        Ok(Type::list(
                            Type::variable("a".to_string(), expr.span),
                            expr.span,
                        ))
                    }
                }
            }
            ligature_ast::ExprKind::Variable(name) => self
                .type_environment
                .lookup(name)
                .ok_or_else(|| AstError::UndefinedIdentifier {
                    name: name.clone(),
                    span: expr.span,
                }),
            ligature_ast::ExprKind::Application { function, argument } => {
                let function_type = Box::pin(self.infer_expression_type(function)).await?;

                // Check if function type is actually a function
                if !function_type.is_function() {
                    return Err(AstError::InvalidExpression { span: expr.span });
                }

                // Extract parameter and return types
                if let Some((param_type, return_type)) = function_type.as_function() {
                    // Check argument type matches parameter type
                    let arg_type = Box::pin(self.infer_expression_type(argument)).await?;
                    let constraint = Constraint::new(arg_type, param_type.clone());
                    self.constraint_solver.add_constraint(constraint);

                    Ok(return_type.clone())
                } else {
                    Err(AstError::InvalidExpression { span: expr.span })
                }
            }
            ligature_ast::ExprKind::Abstraction {
                parameter: _,
                body,
                parameter_type,
            } => {
                let param_type = parameter_type
                    .as_ref()
                    .map(|t| t.as_ref().clone())
                    .unwrap_or_else(|| Type::variable("a".to_string(), expr.span));

                let body_type = Box::pin(self.infer_expression_type(body)).await?;

                Ok(Type::function(param_type, body_type, expr.span))
            }
            ligature_ast::ExprKind::FieldAccess { record, field } => {
                let record_type = Box::pin(self.infer_expression_type(record)).await?;

                // Check if it's a record type
                if !record_type.is_record() {
                    return Err(AstError::InvalidExpression { span: expr.span });
                }

                // Find the field type
                if let Some(fields) = record_type.as_record() {
                    for field_info in fields {
                        if field_info.name == *field {
                            return Ok(field_info.type_.clone());
                        }
                    }
                    Err(AstError::InvalidExpression { span: expr.span })
                } else {
                    Err(AstError::InvalidExpression { span: expr.span })
                }
            }
            ligature_ast::ExprKind::Match { scrutinee, cases } => {
                if cases.is_empty() {
                    return Err(AstError::InvalidExpression { span: expr.span });
                }

                // Infer type of scrutinee
                let _scrutinee_type = Box::pin(self.infer_expression_type(scrutinee)).await?;

                // Infer types of all case expressions
                let mut case_types = Vec::new();
                for case in cases {
                    let case_type = Box::pin(self.infer_expression_type(&case.expression)).await?;
                    case_types.push(case_type);
                }

                // All case types should be the same (simplified)
                if let Some(first_type) = case_types.first() {
                    Ok(first_type.clone())
                } else {
                    Err(AstError::InvalidExpression { span: expr.span })
                }
            }
            _ => {
                // Handle other expression types (simplified)
                Ok(Type::variable("a".to_string(), expr.span))
            }
        }
    }

    /// Split a program into modules for parallel processing
    fn split_into_modules(&self, program: &Program) -> Vec<Module> {
        // Simplified: treat each declaration as a separate module
        program
            .declarations
            .iter()
            .map(|decl| Module {
                name: format!("module_{}", decl.span.start),
                imports: Vec::new(),
                declarations: vec![decl.clone()],
                span: decl.span,
            })
            .collect()
    }

    /// Get type checker statistics
    pub fn stats(&self) -> std::collections::HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::{Expr, ExprKind, Literal, Span};

    use super::*;

    #[tokio::test]
    async fn test_constraint_solver() {
        let solver = ConcurrentConstraintSolver::new(2);
        let constraint = Constraint::new(
            Type::integer(Span::default()),
            Type::integer(Span::default()),
        );
        solver.add_constraint(constraint);

        // Debug: check if constraint was added
        println!("Constraints count: {}", solver.constraints.len());

        let solutions = solver.solve_parallel().await.unwrap();
        println!("Solutions count: {}", solutions.len());
        assert!(!solutions.is_empty());
    }

    #[tokio::test]
    async fn test_concurrent_type_checker() {
        let checker = ConcurrentTypeChecker::new(2);

        // Test simple integer literal
        let int_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };

        let inferred_type = checker.infer_expression_type(&int_expr).await;
        assert!(inferred_type.is_ok());
        assert_eq!(inferred_type.unwrap(), Type::integer(Span::default()));
    }

    #[tokio::test]
    async fn test_type_inference() {
        let checker = ConcurrentTypeChecker::new(2);

        // Test integer literal
        let int_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        assert_eq!(
            checker.infer_expression_type(&int_expr).await.unwrap(),
            Type::integer(Span::default())
        );

        // Test boolean literal
        let bool_expr = Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        };
        assert_eq!(
            checker.infer_expression_type(&bool_expr).await.unwrap(),
            Type::bool(Span::default())
        );
    }
}
