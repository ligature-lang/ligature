//! Error types for the Ligature evaluation engine.

use ligature_ast::{AstError, Span};
use thiserror::Error;

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

    #[error("Invalid operator: {operator}")]
    InvalidOperator { operator: String, span: Span },

    #[error("Field not found: {field}")]
    FieldNotFound { field: String, span: Span },

    #[error("Variant not found: {variant}")]
    VariantNotFound { variant: String, span: Span },
}

impl EvaluationError {
    /// Get the span associated with this error.
    pub fn span(&self) -> Span {
        match self {
            EvaluationError::RuntimeError { span, .. } => *span,
            EvaluationError::DivisionByZero { span } => *span,
            EvaluationError::TypeError { span, .. } => *span,
            EvaluationError::PatternMatchFailure { span } => *span,
            EvaluationError::UnboundVariable { span, .. } => *span,
            EvaluationError::InvalidFunctionApplication { span } => *span,
            EvaluationError::StackOverflow { span } => *span,
            EvaluationError::InvalidOperator { span, .. } => *span,
            EvaluationError::FieldNotFound { span, .. } => *span,
            EvaluationError::VariantNotFound { span, .. } => *span,
        }
    }

    /// Convert to an AST error.
    pub fn into_ast_error(self) -> AstError {
        match self {
            EvaluationError::RuntimeError { message, span } => {
                AstError::InternalError { message, span }
            }
            EvaluationError::DivisionByZero { span } => AstError::InvalidExpression { span },
            EvaluationError::TypeError {
                expected: _,
                found: _,
                span,
            } => AstError::InvalidTypeAnnotation { span },
            EvaluationError::PatternMatchFailure { span } => AstError::InvalidExpression { span },
            EvaluationError::UnboundVariable { name, span } => {
                AstError::UndefinedIdentifier { name, span }
            }
            EvaluationError::InvalidFunctionApplication { span } => {
                AstError::InvalidExpression { span }
            }
            EvaluationError::StackOverflow { span } => AstError::InternalError {
                message: "Evaluation stack overflow".to_string(),
                span,
            },
            EvaluationError::InvalidOperator { operator: _, span } => {
                AstError::InvalidExpression { span }
            }
            EvaluationError::FieldNotFound { field: _, span } => {
                AstError::InvalidExpression { span }
            }
            EvaluationError::VariantNotFound { variant: _, span } => {
                AstError::InvalidExpression { span }
            }
        }
    }
}

impl From<EvaluationError> for AstError {
    fn from(error: EvaluationError) -> Self {
        error.into_ast_error()
    }
}
