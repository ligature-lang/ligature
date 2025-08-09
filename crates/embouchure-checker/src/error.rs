//! Error types for the Ligature type system.

use ligature_ast::{AstError, Span};
use thiserror::Error;

/// Errors that can occur during type checking and inference.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Type mismatch: expected {expected}, found {found}. {suggestion}")]
    TypeMismatchWithSuggestion {
        expected: String,
        found: String,
        suggestion: String,
        span: Span,
    },

    #[error("Unification failed: cannot unify {left} and {right}")]
    UnificationFailed {
        left: String,
        right: String,
        span: Span,
    },

    #[error("Subtyping failed: {left} is not a subtype of {right}. {suggestion}")]
    SubtypingFailed {
        left: String,
        right: String,
        suggestion: String,
        span: Span,
    },

    #[error("Occurs check failed: {variable} occurs in {type_}")]
    OccursCheckFailed {
        variable: String,
        type_: String,
        span: Span,
    },

    #[error("Undefined type variable: {variable}")]
    UndefinedTypeVariable { variable: String, span: Span },

    #[error("Type class constraint unsatisfied: {type_} does not implement {class}")]
    TypeClassConstraintUnsatisfied {
        type_: String,
        class: String,
        span: Span,
    },

    #[error("Ambiguous type: {type_}")]
    AmbiguousType { type_: String, span: Span },

    #[error("Circular type definition: {type_}")]
    CircularTypeDefinition { type_: String, span: Span },

    #[error("Invalid type application: {function} cannot be applied to {argument}")]
    InvalidTypeApplication {
        function: String,
        argument: String,
        span: Span,
    },

    #[error("Type inference failed: {message}")]
    InferenceFailed { message: String, span: Span },

    #[error("Constraint solving failed: {message}")]
    ConstraintSolvingFailed { message: String, span: Span },

    #[error("Record field error: {message}")]
    RecordFieldError {
        message: String,
        field: String,
        span: Span,
    },

    #[error("Union variant error: {message}")]
    UnionVariantError {
        message: String,
        variant: String,
        span: Span,
    },

    #[error("Function application error: {message}")]
    FunctionApplicationError { message: String, span: Span },

    #[error("Pattern matching error: {message}")]
    PatternMatchingError { message: String, span: Span },

    #[error("Binding conflict: {name} is already bound in this scope")]
    BindingConflict {
        name: String,
        existing_type: String,
        new_type: String,
        span: Span,
    },

    #[error("Import binding conflict: {name} conflicts with existing binding")]
    ImportBindingConflict {
        name: String,
        existing_type: String,
        imported_type: String,
        span: Span,
    },

    #[error("Type class instance conflict: multiple instances found for {class} on {type_}")]
    TypeClassInstanceConflict {
        class: String,
        type_: String,
        conflicting_instances: Vec<String>,
        span: Span,
    },

    #[error(
        "Type class constraint unsatisfied: {type_} does not implement {class}. Available \
         instances: {available_instances}"
    )]
    TypeClassConstraintUnsatisfiedWithInstances {
        type_: String,
        class: String,
        available_instances: String,
        span: Span,
    },

    #[error("Ambiguous type class resolution: {type_} could match multiple instances of {class}")]
    AmbiguousTypeClassResolution {
        type_: String,
        class: String,
        candidate_instances: Vec<String>,
        span: Span,
    },

    #[error("Type class method implementation mismatch: expected {expected}, found {found}")]
    TypeClassMethodMismatch {
        method: String,
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Type class context unsatisfied: {context}")]
    TypeClassContextUnsatisfied { context: String, span: Span },

    #[error("Type class overlap: instances for {class} on {type1} and {type2} overlap")]
    TypeClassOverlap {
        class: String,
        type1: String,
        type2: String,
        span: Span,
    },
}

impl TypeError {
    /// Get the span associated with this error.
    pub fn span(&self) -> Span {
        match self {
            TypeError::TypeMismatch { span, .. } => span.clone(),
            TypeError::TypeMismatchWithSuggestion { span, .. } => span.clone(),
            TypeError::UnificationFailed { span, .. } => span.clone(),
            TypeError::SubtypingFailed { span, .. } => span.clone(),
            TypeError::OccursCheckFailed { span, .. } => span.clone(),
            TypeError::UndefinedTypeVariable { span, .. } => span.clone(),
            TypeError::TypeClassConstraintUnsatisfied { span, .. } => span.clone(),
            TypeError::AmbiguousType { span, .. } => span.clone(),
            TypeError::CircularTypeDefinition { span, .. } => span.clone(),
            TypeError::InvalidTypeApplication { span, .. } => span.clone(),
            TypeError::InferenceFailed { span, .. } => span.clone(),
            TypeError::ConstraintSolvingFailed { span, .. } => span.clone(),
            TypeError::RecordFieldError { span, .. } => span.clone(),
            TypeError::UnionVariantError { span, .. } => span.clone(),
            TypeError::FunctionApplicationError { span, .. } => span.clone(),
            TypeError::PatternMatchingError { span, .. } => span.clone(),
            TypeError::BindingConflict { span, .. } => span.clone(),
            TypeError::ImportBindingConflict { span, .. } => span.clone(),
            TypeError::TypeClassInstanceConflict { span, .. } => span.clone(),
            TypeError::TypeClassConstraintUnsatisfiedWithInstances { span, .. } => span.clone(),
            TypeError::AmbiguousTypeClassResolution { span, .. } => span.clone(),
            TypeError::TypeClassMethodMismatch { span, .. } => span.clone(),
            TypeError::TypeClassContextUnsatisfied { span, .. } => span.clone(),
            TypeError::TypeClassOverlap { span, .. } => span.clone(),
        }
    }

    /// Create a type mismatch error with a helpful suggestion.
    pub fn type_mismatch_with_suggestion(
        expected: String,
        found: String,
        suggestion: String,
        span: Span,
    ) -> Self {
        Self::TypeMismatchWithSuggestion {
            expected,
            found,
            suggestion,
            span,
        }
    }

    /// Create a subtyping error with a helpful suggestion.
    pub fn subtyping_failed(left: String, found: String, suggestion: String, span: Span) -> Self {
        Self::SubtypingFailed {
            left,
            right: found,
            suggestion,
            span,
        }
    }

    /// Create a record field error.
    pub fn record_field_error(message: String, field: String, span: Span) -> Self {
        Self::RecordFieldError {
            message,
            field,
            span,
        }
    }

    /// Create a union variant error.
    pub fn union_variant_error(message: String, variant: String, span: Span) -> Self {
        Self::UnionVariantError {
            message,
            variant,
            span,
        }
    }

    /// Create a function application error.
    pub fn function_application_error(message: String, span: Span) -> Self {
        Self::FunctionApplicationError { message, span }
    }

    /// Create a pattern matching error.
    pub fn pattern_matching_error(message: String, span: Span) -> Self {
        TypeError::PatternMatchingError { message, span }
    }

    /// Create a binding conflict error.
    pub fn binding_conflict(
        name: String,
        existing_type: String,
        new_type: String,
        span: Span,
    ) -> Self {
        TypeError::BindingConflict {
            name,
            existing_type,
            new_type,
            span,
        }
    }

    /// Create an import binding conflict error.
    pub fn import_binding_conflict(
        name: String,
        existing_type: String,
        imported_type: String,
        span: Span,
    ) -> Self {
        TypeError::ImportBindingConflict {
            name,
            existing_type,
            imported_type,
            span,
        }
    }

    /// Create a type class instance conflict error.
    pub fn type_class_instance_conflict(
        class: String,
        type_: String,
        conflicting_instances: Vec<String>,
        span: Span,
    ) -> Self {
        TypeError::TypeClassInstanceConflict {
            class,
            type_,
            conflicting_instances,
            span,
        }
    }

    /// Create a type class constraint unsatisfied error with available instances.
    pub fn type_class_constraint_unsatisfied_with_instances(
        type_: String,
        class: String,
        available_instances: String,
        span: Span,
    ) -> Self {
        TypeError::TypeClassConstraintUnsatisfiedWithInstances {
            type_,
            class,
            available_instances,
            span,
        }
    }

    /// Create a type class constraint unsatisfied error.
    pub fn type_class_constraint_unsatisfied(type_: String, class: String, span: Span) -> Self {
        TypeError::TypeClassConstraintUnsatisfied { type_, class, span }
    }

    /// Create an ambiguous type class resolution error.
    pub fn ambiguous_type_class_resolution(
        type_: String,
        class: String,
        candidate_instances: Vec<String>,
        span: Span,
    ) -> Self {
        TypeError::AmbiguousTypeClassResolution {
            type_,
            class,
            candidate_instances,
            span,
        }
    }

    /// Create a type class method mismatch error.
    pub fn type_class_method_mismatch(
        method: String,
        expected: String,
        found: String,
        span: Span,
    ) -> Self {
        TypeError::TypeClassMethodMismatch {
            method,
            expected,
            found,
            span,
        }
    }

    /// Create a type class context unsatisfied error.
    pub fn type_class_context_unsatisfied(context: String, span: Span) -> Self {
        TypeError::TypeClassContextUnsatisfied { context, span }
    }

    /// Create a type class overlap error.
    pub fn type_class_overlap(class: String, type1: String, type2: String, span: Span) -> Self {
        TypeError::TypeClassOverlap {
            class,
            type1,
            type2,
            span,
        }
    }

    /// Convert to an AST error.
    pub fn into_ast_error(self) -> AstError {
        match self {
            TypeError::TypeMismatch {
                expected,
                found,
                span,
            } => AstError::Type {
                code: ligature_ast::ErrorCode::T2001,
                message: format!("Type mismatch: expected {}, found {}", expected, found),
                span,
                expected: Some(expected),
                found: Some(found),
                suggestions: vec![],
            },
            TypeError::TypeMismatchWithSuggestion {
                expected,
                found,
                suggestion,
                span,
            } => AstError::Type {
                code: ligature_ast::ErrorCode::T2001,
                message: format!(
                    "Type mismatch: expected {}, found {}. {}",
                    expected, found, suggestion
                ),
                span,
                expected: Some(expected),
                found: Some(found),
                suggestions: vec![suggestion],
            },
            TypeError::UnificationFailed { left, right, span } => AstError::Type {
                code: ligature_ast::ErrorCode::T2002,
                message: format!("Unification failed: cannot unify {} and {}", left, right),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::SubtypingFailed {
                left,
                right,
                suggestion,
                span,
            } => AstError::Type {
                code: ligature_ast::ErrorCode::T2003,
                message: format!(
                    "Subtyping failed: {} is not a subtype of {}. {}",
                    left, right, suggestion
                ),
                span,
                expected: Some(right),
                found: Some(left),
                suggestions: vec![suggestion],
            },
            TypeError::OccursCheckFailed {
                variable,
                type_,
                span,
            } => AstError::Type {
                code: ligature_ast::ErrorCode::T2002,
                message: format!("Occurs check failed: {} occurs in {}", variable, type_),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::UndefinedTypeVariable { variable, span } => AstError::Type {
                code: ligature_ast::ErrorCode::T2002,
                message: format!("Undefined type variable: {}", variable),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::TypeClassConstraintUnsatisfied { type_, class, span } => AstError::Type {
                code: ligature_ast::ErrorCode::T2008,
                message: format!(
                    "Type class constraint unsatisfied: {} does not implement {}",
                    type_, class
                ),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::AmbiguousType { type_, span } => AstError::Type {
                code: ligature_ast::ErrorCode::T2002,
                message: format!("Ambiguous type: {}", type_),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::CircularTypeDefinition { type_, span } => AstError::Type {
                code: ligature_ast::ErrorCode::T2002,
                message: format!("Circular type definition: {}", type_),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::InvalidTypeApplication {
                function,
                argument,
                span,
            } => AstError::Type {
                code: ligature_ast::ErrorCode::T2004,
                message: format!(
                    "Invalid type application: {} cannot be applied to {}",
                    function, argument
                ),
                span,
                expected: None,
                found: None,
                suggestions: vec![],
            },
            TypeError::InferenceFailed { message, span } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::ConstraintSolvingFailed { message, span } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::RecordFieldError {
                message,
                field: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::UnionVariantError {
                message,
                variant: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::FunctionApplicationError { message, span } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::PatternMatchingError { message, span } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message,
                span,
            },
            TypeError::BindingConflict {
                name,
                existing_type: _,
                new_type: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!("Binding conflict: {name} is already bound in this scope"),
                span,
            },
            TypeError::ImportBindingConflict {
                name,
                existing_type: _,
                imported_type: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!("Import binding conflict: {name} conflicts with existing binding"),
                span,
            },
            TypeError::TypeClassInstanceConflict {
                class,
                type_,
                conflicting_instances: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!(
                    "Type class instance conflict: multiple instances found for {class} on {type_}"
                ),
                span,
            },
            TypeError::TypeClassConstraintUnsatisfiedWithInstances {
                type_,
                class,
                available_instances,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!(
                    "Type class constraint unsatisfied: {type_} does not implement {class}. \
                     Available instances: {available_instances}"
                ),
                span,
            },
            TypeError::AmbiguousTypeClassResolution {
                type_,
                class,
                candidate_instances: _,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!(
                    "Ambiguous type class resolution: {type_} could match multiple instances of \
                     {class}"
                ),
                span,
            },
            TypeError::TypeClassMethodMismatch {
                method: _,
                expected,
                found,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!(
                    "Type class method implementation mismatch: expected {expected}, found {found}"
                ),
                span,
            },
            TypeError::TypeClassContextUnsatisfied { context, span } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!("Type class context unsatisfied: {context}"),
                span,
            },
            TypeError::TypeClassOverlap {
                class,
                type1,
                type2,
                span,
            } => AstError::InternalError {
                code: ligature_ast::ErrorCode::I6001,
                message: format!(
                    "Type class overlap: instances for {class} on {type1} and {type2} overlap"
                ),
                span,
            },
        }
    }
}

impl From<TypeError> for AstError {
    fn from(error: TypeError) -> Self {
        error.into_ast_error()
    }
}

impl From<TypeError> for ligature_error::StandardError {
    fn from(error: TypeError) -> Self {
        ligature_error::StandardError::Ligature(error.into_ast_error())
    }
}
