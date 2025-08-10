//! Error context utilities for building rich error contexts.

use std::collections::HashMap;

use ligature_ast::{LigatureError, Span};

/// Builder for creating rich error contexts.
#[derive(Debug, Clone)]
pub struct ErrorContextBuilder {
    context: Vec<String>,
    metadata: HashMap<String, String>,
    suggestions: Vec<String>,
    span: Option<Span>,
}

impl ErrorContextBuilder {
    /// Create a new error context builder.
    pub fn new() -> Self {
        Self {
            context: Vec::new(),
            metadata: HashMap::new(),
            suggestions: Vec::new(),
            span: None,
        }
    }

    /// Add context information.
    pub fn context(mut self, context: impl Into<String>) -> Self {
        self.context.push(context.into());
        self
    }

    /// Add multiple context items.
    pub fn contexts(mut self, contexts: Vec<String>) -> Self {
        self.context.extend(contexts);
        self
    }

    /// Add metadata key-value pair.
    pub fn metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Add multiple metadata items.
    pub fn metadata_map(mut self, metadata: HashMap<String, String>) -> Self {
        self.metadata.extend(metadata);
        self
    }

    /// Add a suggestion for fixing the error.
    pub fn suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestions.push(suggestion.into());
        self
    }

    /// Add multiple suggestions.
    pub fn with_suggestions(mut self, suggestions: Vec<String>) -> Self {
        self.suggestions.extend(suggestions);
        self
    }

    /// Set the span for the error.
    pub fn span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Build a LigatureError with the collected context.
    pub fn build_parse_error(self, message: impl Into<String>) -> LigatureError {
        LigatureError::Parse {
            code: ligature_ast::ErrorCode::E1001,
            message: message.into(),
            span: self.span.unwrap_or_else(|| Span::simple(0, 0)),
            suggestions: self.suggestions,
        }
    }

    /// Build a type error with the collected context.
    pub fn build_type_error(
        self,
        message: impl Into<String>,
        expected: Option<String>,
        found: Option<String>,
    ) -> LigatureError {
        LigatureError::Type {
            code: ligature_ast::ErrorCode::T2001,
            message: message.into(),
            span: self.span.unwrap_or_else(|| Span::simple(0, 0)),
            expected,
            found,
            suggestions: self.suggestions,
        }
    }

    /// Build an evaluation error with the collected context.
    pub fn build_evaluation_error(self, message: impl Into<String>) -> LigatureError {
        let context = if self.context.is_empty() {
            None
        } else {
            Some(self.context.join(": "))
        };

        LigatureError::Evaluation {
            code: ligature_ast::ErrorCode::R3001,
            message: message.into(),
            span: self.span.unwrap_or_else(|| Span::simple(0, 0)),
            context,
        }
    }

    /// Build a module error with the collected context.
    pub fn build_module_error(
        self,
        message: impl Into<String>,
        path: Option<String>,
    ) -> LigatureError {
        let cause = if self.context.is_empty() {
            None
        } else {
            Some(self.context.join(": "))
        };

        LigatureError::Module {
            code: ligature_ast::ErrorCode::M4001,
            message: message.into(),
            path,
            cause,
        }
    }

    /// Build a configuration error with the collected context.
    pub fn build_configuration_error(
        self,
        message: impl Into<String>,
        field: Option<String>,
        value: Option<String>,
    ) -> LigatureError {
        LigatureError::Configuration {
            code: ligature_ast::ErrorCode::C5001,
            message: message.into(),
            field,
            value,
        }
    }

    /// Get the collected context as a string.
    pub fn context_string(&self) -> String {
        self.context.join(": ")
    }

    /// Get the collected suggestions.
    pub fn get_suggestions(&self) -> Vec<String> {
        self.suggestions.clone()
    }

    /// Get the metadata as a string representation.
    pub fn metadata_string(&self) -> String {
        if self.metadata.is_empty() {
            return String::new();
        }

        let mut pairs: Vec<_> = self.metadata.iter().collect();
        pairs.sort_by_key(|(k, _)| *k);

        pairs
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl Default for ErrorContextBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Macro for creating error contexts with a fluent API.
#[macro_export]
macro_rules! error_context {
    () => {
        $crate::context::ErrorContextBuilder::new()
    };

    ($($context:expr),*) => {
        {
            let mut builder = $crate::context::ErrorContextBuilder::new();
            $(
                builder = builder.context($context);
            )*
            builder
        }
    };
}

/// Macro for creating parse errors with context.
#[macro_export]
macro_rules! parse_error_with_context {
    ($message:expr, $($context:expr),*) => {
        error_context!($($context),*).build_parse_error($message)
    };
}

/// Macro for creating type errors with context.
#[macro_export]
macro_rules! type_error_with_context {
    ($message:expr, $expected:expr, $found:expr, $($context:expr),*) => {
        error_context!($($context),*).build_type_error($message, Some($expected.to_string()), Some($found.to_string()))
    };

    ($message:expr, $($context:expr),*) => {
        error_context!($($context),*).build_type_error($message, None, None)
    };
}

/// Macro for creating evaluation errors with context.
#[macro_export]
macro_rules! eval_error_with_context {
    ($message:expr, $($context:expr),*) => {
        error_context!($($context),*).build_evaluation_error($message)
    };
}

/// Macro for creating module errors with context.
#[macro_export]
macro_rules! module_error_with_context {
    ($message:expr, $path:expr, $($context:expr),*) => {
        error_context!($($context),*).build_module_error($message, Some($path.to_string()))
    };

    ($message:expr, $($context:expr),*) => {
        error_context!($($context),*).build_module_error($message, None)
    };
}

/// Macro for creating configuration errors with context.
#[macro_export]
macro_rules! config_error_with_context {
    ($message:expr, $field:expr, $value:expr, $($context:expr),*) => {
        error_context!($($context),*).build_configuration_error($message, Some($field.to_string()), Some($value.to_string()))
    };

    ($message:expr, $($context:expr),*) => {
        error_context!($($context),*).build_configuration_error($message, None, None)
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_context_builder() {
        let error = ErrorContextBuilder::new()
            .context("Failed to parse configuration")
            .context("Invalid syntax")
            .metadata("file", "config.lig")
            .metadata("line", "10")
            .suggestion("Check the syntax")
            .suggestion("Verify all brackets are matched")
            .span(Span::simple(10, 20))
            .build_parse_error("Unexpected token");

        assert_eq!(error.code(), ligature_ast::ErrorCode::E1001);
        assert_eq!(error.span(), Some(Span::simple(10, 20)));
    }

    #[test]
    fn test_error_context_macros() {
        let error = parse_error_with_context!(
            "Unexpected token",
            "Failed to parse configuration",
            "Invalid syntax"
        );

        assert_eq!(error.code(), ligature_ast::ErrorCode::E1001);
    }

    #[test]
    fn test_type_error_with_context() {
        let error = type_error_with_context!(
            "Type mismatch",
            "integer",
            "string",
            "In function call",
            "Parameter validation"
        );

        assert_eq!(error.code(), ligature_ast::ErrorCode::T2001);
        if let LigatureError::Type {
            expected, found, ..
        } = error
        {
            assert_eq!(expected, Some("integer".to_string()));
            assert_eq!(found, Some("string".to_string()));
        } else {
            panic!("Expected type error");
        }
    }
}
