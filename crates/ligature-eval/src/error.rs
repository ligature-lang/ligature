//! Error types for the Ligature evaluation engine.

use ligature_ast::{LigatureError, Span};
use ligature_error::{ErrorContextBuilder, StandardError, StandardResult};
use thiserror::Error;

/// Main result type for evaluation operations using the new error handling.
pub type EvaluationResult<T> = StandardResult<T>;

/// Errors that can occur during evaluation.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum EvaluationError {
    #[error("Runtime error: {message}")]
    RuntimeError { message: String, span: Span },

    #[error("Division by zero")]
    DivisionByZero { span: Span },

    #[error("Type error: expected {expected}, found {found}")]
    TypeError {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Pattern match failure")]
    PatternMatchFailure { span: Span },

    #[error("Unbound variable: {name}")]
    UnboundVariable { name: String, span: Span },

    #[error("Invalid function application")]
    InvalidFunctionApplication { span: Span },

    #[error("Evaluation stack overflow")]
    StackOverflow { span: Span },

    #[error("Recursion limit exceeded")]
    RecursionLimitExceeded { span: Span },

    #[error("Memory allocation failed")]
    MemoryAllocationFailed { span: Span },

    #[error("Invalid operation: {operation} on {operand_type}")]
    InvalidOperation {
        operation: String,
        operand_type: String,
        span: Span,
    },

    #[error("Index out of bounds: index {index}, length {length}")]
    IndexOutOfBounds {
        index: usize,
        length: usize,
        span: Span,
    },

    #[error("Field not found: {field} in {record_type}")]
    FieldNotFound {
        field: String,
        record_type: String,
        span: Span,
    },

    #[error("Variant not found: {variant} in {union_type}")]
    VariantNotFound {
        variant: String,
        union_type: String,
        span: Span,
    },

    #[error("Evaluation timeout")]
    Timeout { span: Span },

    #[error("External function error: {message}")]
    ExternalFunctionError { message: String, span: Span },
}

impl EvaluationError {
    /// Get the span associated with this error.
    pub fn span(&self) -> Span {
        match self {
            EvaluationError::RuntimeError { span, .. } => span.clone(),
            EvaluationError::DivisionByZero { span } => span.clone(),
            EvaluationError::TypeError { span, .. } => span.clone(),
            EvaluationError::PatternMatchFailure { span } => span.clone(),
            EvaluationError::UnboundVariable { span, .. } => span.clone(),
            EvaluationError::InvalidFunctionApplication { span } => span.clone(),
            EvaluationError::StackOverflow { span } => span.clone(),
            EvaluationError::RecursionLimitExceeded { span } => span.clone(),
            EvaluationError::MemoryAllocationFailed { span } => span.clone(),
            EvaluationError::InvalidOperation { span, .. } => span.clone(),
            EvaluationError::IndexOutOfBounds { span, .. } => span.clone(),
            EvaluationError::FieldNotFound { span, .. } => span.clone(),
            EvaluationError::VariantNotFound { span, .. } => span.clone(),
            EvaluationError::Timeout { span } => span.clone(),
            EvaluationError::ExternalFunctionError { span, .. } => span.clone(),
        }
    }

    /// Convert to a LigatureError with rich context using the new error context system.
    pub fn into_ligature_error(self) -> LigatureError {
        let mut context_builder = ErrorContextBuilder::new().span(self.span());

        match &self {
            EvaluationError::RuntimeError { message, .. } => {
                context_builder = context_builder
                    .context("Runtime evaluation error")
                    .suggestion("Check the expression for logical errors")
                    .suggestion("Verify all variables are properly bound");
                context_builder.build_evaluation_error(message)
            }
            EvaluationError::DivisionByZero { .. } => {
                context_builder = context_builder
                    .context("Division by zero error")
                    .suggestion("Add a check for zero before division")
                    .suggestion("Use conditional logic to handle zero cases");
                context_builder.build_evaluation_error("Division by zero")
            }
            EvaluationError::TypeError {
                expected, found, ..
            } => {
                context_builder = context_builder
                    .context("Type mismatch during evaluation")
                    .metadata("expected_type", expected.clone())
                    .metadata("found_type", found.clone())
                    .suggestion("Check the types of your variables and expressions")
                    .suggestion("Ensure function arguments match expected types");
                context_builder.build_type_error(
                    format!("Type error: expected {expected}, found {found}"),
                    Some(expected.clone()),
                    Some(found.clone()),
                )
            }
            EvaluationError::PatternMatchFailure { .. } => {
                context_builder = context_builder
                    .context("Pattern match failure")
                    .suggestion("Check that your pattern covers all possible cases")
                    .suggestion("Add a catch-all pattern if needed");
                context_builder.build_evaluation_error("Pattern match failure")
            }
            EvaluationError::UnboundVariable { name, .. } => {
                context_builder = context_builder
                    .context("Unbound variable error")
                    .metadata("variable_name", name.clone())
                    .suggestion("Check that the variable is properly defined")
                    .suggestion("Verify the variable is in scope")
                    .suggestion("Check for typos in variable names");
                context_builder.build_evaluation_error(format!("Unbound variable: {name}"))
            }
            EvaluationError::InvalidFunctionApplication { .. } => {
                context_builder = context_builder
                    .context("Invalid function application")
                    .suggestion(
                        "Check that you're applying a function to the correct number of arguments",
                    )
                    .suggestion("Verify the function expression evaluates to a function");
                context_builder.build_evaluation_error("Invalid function application")
            }
            EvaluationError::StackOverflow { .. } => {
                context_builder = context_builder
                    .context("Evaluation stack overflow")
                    .suggestion("Check for infinite recursion")
                    .suggestion("Consider using tail call optimization")
                    .suggestion("Simplify deeply nested expressions");
                context_builder.build_evaluation_error("Evaluation stack overflow")
            }
            EvaluationError::RecursionLimitExceeded { .. } => {
                context_builder = context_builder
                    .context("Recursion limit exceeded")
                    .suggestion("Check for infinite recursion in your functions")
                    .suggestion("Consider using iterative approaches")
                    .suggestion("Increase recursion limit if appropriate");
                context_builder.build_evaluation_error("Recursion limit exceeded")
            }
            EvaluationError::MemoryAllocationFailed { .. } => {
                context_builder = context_builder
                    .context("Memory allocation failed")
                    .suggestion("Check for memory leaks in your program")
                    .suggestion("Consider using more efficient data structures")
                    .suggestion("Simplify complex expressions");
                context_builder.build_evaluation_error("Memory allocation failed")
            }
            EvaluationError::InvalidOperation {
                operation,
                operand_type,
                ..
            } => {
                context_builder = context_builder
                    .context("Invalid operation")
                    .metadata("operation", operation.clone())
                    .metadata("operand_type", operand_type.clone())
                    .suggestion("Check that the operation is valid for the given type")
                    .suggestion("Verify operand types before performing operations");
                context_builder.build_evaluation_error(format!(
                    "Invalid operation: {operation} on {operand_type}"
                ))
            }
            EvaluationError::IndexOutOfBounds { index, length, .. } => {
                context_builder = context_builder
                    .context("Index out of bounds")
                    .metadata("index", index.to_string())
                    .metadata("length", length.to_string())
                    .suggestion("Check that your index is within the valid range")
                    .suggestion("Verify the length of your collection before indexing");
                context_builder.build_evaluation_error(format!(
                    "Index out of bounds: index {index}, length {length}"
                ))
            }
            EvaluationError::FieldNotFound {
                field, record_type, ..
            } => {
                context_builder = context_builder
                    .context("Field not found")
                    .metadata("field_name", field.clone())
                    .metadata("record_type", record_type.clone())
                    .suggestion("Check that the field name is spelled correctly")
                    .suggestion("Verify the record has the expected structure");
                context_builder
                    .build_evaluation_error(format!("Field not found: {field} in {record_type}"))
            }
            EvaluationError::VariantNotFound {
                variant,
                union_type,
                ..
            } => {
                context_builder = context_builder
                    .context("Variant not found")
                    .metadata("variant_name", variant.clone())
                    .metadata("union_type", union_type.clone())
                    .suggestion("Check that the variant name is spelled correctly")
                    .suggestion("Verify the union type has the expected variants");
                context_builder
                    .build_evaluation_error(format!("Variant not found: {variant} in {union_type}"))
            }
            EvaluationError::Timeout { .. } => {
                context_builder = context_builder
                    .context("Evaluation timeout")
                    .suggestion("Check for infinite loops or very complex expressions")
                    .suggestion("Consider breaking down complex evaluations")
                    .suggestion("Increase timeout if appropriate");
                context_builder.build_evaluation_error("Evaluation timeout")
            }
            EvaluationError::ExternalFunctionError { message, .. } => {
                context_builder = context_builder
                    .context("External function error")
                    .suggestion("Check the external function implementation")
                    .suggestion("Verify function arguments and return types");
                context_builder
                    .build_evaluation_error(format!("External function error: {message}"))
            }
        }
    }

    /// Add context to this error using the new error context system.
    pub fn with_context(self, context: &str) -> LigatureError {
        let mut context_builder = ErrorContextBuilder::new()
            .span(self.span())
            .context(context);

        // Add additional context based on error type
        match &self {
            EvaluationError::UnboundVariable { name, .. } => {
                context_builder = context_builder.metadata("variable_name", name.clone());
            }
            EvaluationError::TypeError {
                expected, found, ..
            } => {
                context_builder = context_builder
                    .metadata("expected_type", expected.clone())
                    .metadata("found_type", found.clone());
            }
            EvaluationError::IndexOutOfBounds { index, length, .. } => {
                context_builder = context_builder
                    .metadata("index", index.to_string())
                    .metadata("length", length.to_string());
            }
            _ => {}
        }

        context_builder.build_evaluation_error(self.to_string())
    }

    /// Get suggestions for fixing this error.
    pub fn get_suggestions(&self) -> Vec<String> {
        match self {
            EvaluationError::RuntimeError { .. } => vec![
                "Check the expression for logical errors".to_string(),
                "Verify all variables are properly bound".to_string(),
            ],
            EvaluationError::DivisionByZero { .. } => vec![
                "Add a check for zero before division".to_string(),
                "Use conditional logic to handle zero cases".to_string(),
            ],
            EvaluationError::TypeError { .. } => vec![
                "Check the types of your variables and expressions".to_string(),
                "Ensure function arguments match expected types".to_string(),
            ],
            EvaluationError::PatternMatchFailure { .. } => vec![
                "Check that your pattern covers all possible cases".to_string(),
                "Add a catch-all pattern if needed".to_string(),
            ],
            EvaluationError::UnboundVariable { .. } => vec![
                "Check that the variable is properly defined".to_string(),
                "Verify the variable is in scope".to_string(),
                "Check for typos in variable names".to_string(),
            ],
            EvaluationError::InvalidFunctionApplication { .. } => vec![
                "Check that you're applying a function to the correct number of arguments"
                    .to_string(),
                "Verify the function expression evaluates to a function".to_string(),
            ],
            EvaluationError::StackOverflow { .. } => vec![
                "Check for infinite recursion".to_string(),
                "Consider using tail call optimization".to_string(),
                "Simplify deeply nested expressions".to_string(),
            ],
            EvaluationError::RecursionLimitExceeded { .. } => vec![
                "Check for infinite recursion in your functions".to_string(),
                "Consider using iterative approaches".to_string(),
                "Increase recursion limit if appropriate".to_string(),
            ],
            EvaluationError::MemoryAllocationFailed { .. } => vec![
                "Check for memory leaks in your program".to_string(),
                "Consider using more efficient data structures".to_string(),
                "Simplify complex expressions".to_string(),
            ],
            EvaluationError::InvalidOperation { .. } => vec![
                "Check that the operation is valid for the given type".to_string(),
                "Verify operand types before performing operations".to_string(),
            ],
            EvaluationError::IndexOutOfBounds { .. } => vec![
                "Check that your index is within the valid range".to_string(),
                "Verify the length of your collection before indexing".to_string(),
            ],
            EvaluationError::FieldNotFound { .. } => vec![
                "Check that the field name is spelled correctly".to_string(),
                "Verify the record has the expected structure".to_string(),
            ],
            EvaluationError::VariantNotFound { .. } => vec![
                "Check that the variant name is spelled correctly".to_string(),
                "Verify the union type has the expected variants".to_string(),
            ],
            EvaluationError::Timeout { .. } => vec![
                "Check for infinite loops or very complex expressions".to_string(),
                "Consider breaking down complex evaluations".to_string(),
                "Increase timeout if appropriate".to_string(),
            ],
            EvaluationError::ExternalFunctionError { .. } => vec![
                "Check the external function implementation".to_string(),
                "Verify function arguments and return types".to_string(),
            ],
        }
    }
}

impl From<EvaluationError> for LigatureError {
    fn from(error: EvaluationError) -> Self {
        error.into_ligature_error()
    }
}

impl From<EvaluationError> for StandardError {
    fn from(error: EvaluationError) -> Self {
        StandardError::Internal(error.to_string())
    }
}

// Legacy evaluator struct for backward compatibility
// This should be removed once all code is migrated to the new evaluator
#[derive(Debug)]
pub struct LegacyEvaluator {
    error_collector: ligature_ast::ErrorCollection,
    recursion_limit: usize,
    timeout_ms: u64,
}

impl Default for LegacyEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

impl LegacyEvaluator {
    pub fn new() -> Self {
        Self {
            error_collector: ligature_ast::ErrorCollection::new(),
            recursion_limit: 1000,
            timeout_ms: 30000,
        }
    }

    pub fn with_error_limit(mut self, max_errors: usize) -> Self {
        self.error_collector = ligature_ast::ErrorCollection::with_max_errors(max_errors);
        self
    }

    pub fn with_recursion_limit(mut self, limit: usize) -> Self {
        self.recursion_limit = limit;
        self
    }

    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    pub fn evaluate_expression(
        &mut self,
        _expr: &ligature_ast::Expr,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        // The actual evaluation should be done by the new Evaluator
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_expression_with_context(
        &mut self,
        _expr: &ligature_ast::Expr,
        _recursion_depth: usize,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_literal(
        &self,
        _lit: &ligature_ast::Literal,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_identifier(&self, _id: &str) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_binary_operation(
        &mut self,
        _left: &ligature_ast::Expr,
        _operator: &ligature_ast::BinaryOperator,
        _right: &ligature_ast::Expr,
        _recursion_depth: usize,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_function(
        &mut self,
        _params: &[String],
        _body: &ligature_ast::Expr,
        _recursion_depth: usize,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    #[allow(dead_code)]
    fn evaluate_application(
        &mut self,
        _func: &ligature_ast::Expr,
        _args: &[ligature_ast::Expr],
        _recursion_depth: usize,
    ) -> EvaluationResult<crate::value::Value> {
        // This is a placeholder implementation
        Err(StandardError::Internal(
            "Legacy evaluator is deprecated".to_string(),
        ))
    }

    pub fn get_errors(&self) -> &ligature_ast::ErrorCollection {
        &self.error_collector
    }

    pub fn has_errors(&self) -> bool {
        !self.error_collector.is_empty()
    }

    pub fn error_report(&self) -> String {
        self.error_collector.to_string()
    }
}
