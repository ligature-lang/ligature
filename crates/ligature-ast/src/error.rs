//! Error types for the Ligature AST and compiler.

use crate::span::Span;
use thiserror::Error;

/// Errors that can occur during AST construction or manipulation.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum AstError {
    #[error("Invalid identifier: {name}")]
    InvalidIdentifier { name: String, span: Span },

    #[error("Duplicate identifier: {name}")]
    DuplicateIdentifier { name: String, span: Span },

    #[error("Undefined identifier: {name}")]
    UndefinedIdentifier { name: String, span: Span },

    #[error("Invalid type annotation")]
    InvalidTypeAnnotation { span: Span },

    #[error("Invalid expression")]
    InvalidExpression { span: Span },

    #[error("Invalid declaration")]
    InvalidDeclaration { span: Span },

    #[error("Circular dependency detected")]
    CircularDependency { span: Span },

    #[error("Invalid import path: {path}")]
    InvalidImportPath { path: String, span: Span },

    #[error("Import cycle detected: {path}")]
    ImportCycle { path: String, span: Span },

    #[error("Module not found: {module}")]
    ModuleNotFound { module: String, span: Span },

    #[error("Parse error: {message}")]
    ParseError { message: String, span: Span },

    #[error("Internal error: {message}")]
    InternalError { message: String, span: Span },

    // Type class system errors
    #[error("Duplicate type class: {name}")]
    DuplicateTypeClass { name: String, span: Span },

    #[error("Undefined type class: {name}")]
    UndefinedTypeClass { name: String, span: Span },

    #[error("Unused type parameter: {parameter}")]
    UnusedTypeParameter { parameter: String, span: Span },

    #[error("Type argument mismatch: expected {expected}, found {found}")]
    TypeArgumentMismatch {
        expected: usize,
        found: usize,
        span: Span,
    },

    #[error("Missing method: {method} in class {class}")]
    MissingMethod {
        method: String,
        class: String,
        span: Span,
    },

    #[error("Undefined method: {method} in class {class}")]
    UndefinedMethod {
        method: String,
        class: String,
        span: Span,
    },

    #[error("Method type mismatch: {method}, expected {expected:?}, found {found:?}")]
    MethodTypeMismatch {
        method: String,
        expected: crate::Type,
        found: crate::Type,
        span: Span,
    },

    #[error("No instance found for type {type_:?} in class {class}")]
    NoInstanceFound {
        class: String,
        type_: crate::Type,
        span: Span,
    },
}

impl AstError {
    /// Get the span associated with this error.
    pub fn span(&self) -> Span {
        match self {
            AstError::InvalidIdentifier { span, .. } => *span,
            AstError::DuplicateIdentifier { span, .. } => *span,
            AstError::UndefinedIdentifier { span, .. } => *span,
            AstError::InvalidTypeAnnotation { span } => *span,
            AstError::InvalidExpression { span } => *span,
            AstError::InvalidDeclaration { span } => *span,
            AstError::CircularDependency { span } => *span,
            AstError::InvalidImportPath { span, .. } => *span,
            AstError::ImportCycle { span, .. } => *span,
            AstError::ModuleNotFound { span, .. } => *span,
            AstError::ParseError { span, .. } => *span,
            AstError::InternalError { span, .. } => *span,
            AstError::DuplicateTypeClass { span, .. } => *span,
            AstError::UndefinedTypeClass { span, .. } => *span,
            AstError::UnusedTypeParameter { span, .. } => *span,
            AstError::TypeArgumentMismatch { span, .. } => *span,
            AstError::MissingMethod { span, .. } => *span,
            AstError::UndefinedMethod { span, .. } => *span,
            AstError::MethodTypeMismatch { span, .. } => *span,
            AstError::NoInstanceFound { span, .. } => *span,
        }
    }
}

/// Result type for AST operations.
pub type AstResult<T> = Result<T, AstError>;

/// A collection of errors that occurred during compilation.
#[derive(Debug, Clone)]
pub struct ErrorCollection {
    pub errors: Vec<AstError>,
}

impl ErrorCollection {
    /// Create a new empty error collection.
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    /// Add an error to the collection.
    pub fn push(&mut self, error: AstError) {
        self.errors.push(error);
    }

    /// Check if the collection has any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors.
    pub fn len(&self) -> usize {
        self.errors.len()
    }

    /// Check if the collection is empty.
    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    /// Convert to a result, returning the first error if any exist.
    pub fn into_result<T>(self, value: T) -> AstResult<T> {
        if self.has_errors() {
            Err(self.errors.into_iter().next().unwrap())
        } else {
            Ok(value)
        }
    }
}

impl Default for ErrorCollection {
    fn default() -> Self {
        Self::new()
    }
}

impl From<AstError> for ErrorCollection {
    fn from(error: AstError) -> Self {
        Self {
            errors: vec![error],
        }
    }
}
