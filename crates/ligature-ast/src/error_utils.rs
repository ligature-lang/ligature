//! Error handling utilities for Ligature.
//!
//! This module provides common error handling patterns and utilities
//! that can be used across all Ligature crates.

use std::collections::HashMap;

use crate::{ErrorCode, LigatureError, LigatureResult, Span};

/// Error context builder for adding rich context to errors.
pub struct ErrorContext {
    context: Vec<String>,
    suggestions: Vec<String>,
}

impl ErrorContext {
    /// Create a new error context builder.
    pub fn new() -> Self {
        Self {
            context: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    /// Add context information.
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context.push(context.into());
        self
    }

    /// Add a suggestion for fixing the error.
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestions.push(suggestion.into());
        self
    }

    /// Add multiple suggestions.
    pub fn with_suggestions(mut self, suggestions: Vec<String>) -> Self {
        self.suggestions.extend(suggestions);
        self
    }

    /// Build the final error with all context and suggestions.
    pub fn build(self, error: LigatureError) -> LigatureError {
        let mut final_error = error;

        // Add context to evaluation errors
        if let LigatureError::Evaluation { context, .. } = &mut final_error {
            if !self.context.is_empty() {
                *context = Some(self.context.join(": "));
            }
        }

        // Add suggestions to parse and type errors
        if !self.suggestions.is_empty() {
            final_error = final_error.with_suggestions(self.suggestions);
        }

        final_error
    }
}

impl Default for ErrorContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Error recovery strategies for different types of errors.
pub trait RecoveryStrategy: std::fmt::Debug {
    /// Check if this strategy can recover from the given error.
    fn can_recover(&self, error: &LigatureError) -> bool;

    /// Attempt to recover from the error.
    fn recover(&self, error: &LigatureError) -> LigatureResult<()>;

    /// Get the priority of this recovery strategy (lower numbers = higher priority).
    fn priority(&self) -> u32 {
        100
    }
}

/// Skip to semicolon recovery strategy.
#[derive(Debug)]
pub struct SkipToSemicolon;

impl RecoveryStrategy for SkipToSemicolon {
    fn can_recover(&self, error: &LigatureError) -> bool {
        matches!(error, LigatureError::Parse { .. })
    }

    fn recover(&self, _error: &LigatureError) -> LigatureResult<()> {
        // Implementation would skip to the next semicolon
        Ok(())
    }

    fn priority(&self) -> u32 {
        1
    }
}

/// Insert missing token recovery strategy.
#[derive(Debug)]
pub struct InsertMissingToken {
    pub token: String,
}

impl RecoveryStrategy for InsertMissingToken {
    fn can_recover(&self, error: &LigatureError) -> bool {
        matches!(error, LigatureError::Parse { .. })
    }

    fn recover(&self, _error: &LigatureError) -> LigatureResult<()> {
        // Implementation would insert the missing token
        Ok(())
    }

    fn priority(&self) -> u32 {
        2
    }
}

/// Skip to closing brace recovery strategy.
#[derive(Debug)]
pub struct SkipToClosingBrace;

impl RecoveryStrategy for SkipToClosingBrace {
    fn can_recover(&self, error: &LigatureError) -> bool {
        matches!(error, LigatureError::Parse { .. })
    }

    fn recover(&self, _error: &LigatureError) -> LigatureResult<()> {
        // Implementation would skip to the next closing brace
        Ok(())
    }

    fn priority(&self) -> u32 {
        3
    }
}

/// Error recovery manager that tries multiple recovery strategies.
pub struct ErrorRecovery {
    strategies: Vec<Box<dyn RecoveryStrategy>>,
}

impl ErrorRecovery {
    /// Create a new error recovery manager.
    pub fn new() -> Self {
        let strategies: Vec<Box<dyn RecoveryStrategy>> = vec![
            Box::new(SkipToSemicolon),
            Box::new(InsertMissingToken {
                token: ";".to_string(),
            }),
            Box::new(SkipToClosingBrace),
        ];

        Self { strategies }
    }

    /// Add a custom recovery strategy.
    pub fn with_strategy(mut self, strategy: Box<dyn RecoveryStrategy>) -> Self {
        self.strategies.push(strategy);
        self
    }

    /// Try to recover from an error using available strategies.
    pub fn try_recover(&self, error: &LigatureError) -> LigatureResult<()> {
        // Sort strategies by priority
        let mut sorted_strategies: Vec<_> = self.strategies.iter().collect();
        sorted_strategies.sort_by_key(|s| s.priority());

        for strategy in sorted_strategies {
            if strategy.can_recover(error) {
                if let Ok(()) = strategy.recover(error) {
                    return Ok(());
                }
            }
        }

        Err(error.clone().into())
    }
}

impl Default for ErrorRecovery {
    fn default() -> Self {
        Self::new()
    }
}

/// Error reporting configuration.
#[derive(Debug, Clone)]
pub struct ErrorReportConfig {
    /// Whether to show source code context.
    pub show_source: bool,
    /// Whether to show suggestions.
    pub show_suggestions: bool,
    /// Maximum number of errors to show.
    pub max_errors: usize,
    /// Whether to use colored output.
    pub color_output: bool,
    /// Whether to show error codes.
    pub show_error_codes: bool,
    /// Whether to show error categories.
    pub show_categories: bool,
}

impl Default for ErrorReportConfig {
    fn default() -> Self {
        Self {
            show_source: true,
            show_suggestions: true,
            max_errors: 10,
            color_output: true,
            show_error_codes: false,
            show_categories: true,
        }
    }
}

/// Error category for grouping related errors.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorCategory {
    Syntax,
    Type,
    Runtime,
    Module,
    Configuration,
    Internal,
}

impl ErrorCategory {
    /// Get the display name for this category.
    pub fn display_name(&self) -> &'static str {
        match self {
            ErrorCategory::Syntax => "Syntax Error",
            ErrorCategory::Type => "Type Error",
            ErrorCategory::Runtime => "Runtime Error",
            ErrorCategory::Module => "Module Error",
            ErrorCategory::Configuration => "Configuration Error",
            ErrorCategory::Internal => "Internal Error",
        }
    }

    /// Get the color code for this category.
    pub fn color_code(&self) -> &'static str {
        match self {
            ErrorCategory::Syntax => "\x1b[31m",        // Red
            ErrorCategory::Type => "\x1b[33m",          // Yellow
            ErrorCategory::Runtime => "\x1b[35m",       // Magenta
            ErrorCategory::Module => "\x1b[36m",        // Cyan
            ErrorCategory::Configuration => "\x1b[34m", // Blue
            ErrorCategory::Internal => "\x1b[37m",      // White
        }
    }
}

/// Get the error category for a LigatureError.
pub fn get_error_category(error: &LigatureError) -> ErrorCategory {
    match error {
        LigatureError::Parse { .. } | LigatureError::InvalidIdentifier { .. } => {
            ErrorCategory::Syntax
        }
        LigatureError::Type { .. } | LigatureError::TypeArgumentMismatch { .. } => {
            ErrorCategory::Type
        }
        LigatureError::Evaluation { .. } => ErrorCategory::Runtime,
        LigatureError::Module { .. } | LigatureError::ModuleNotFound { .. } => {
            ErrorCategory::Module
        }
        LigatureError::Configuration { .. } => ErrorCategory::Configuration,
        LigatureError::InternalError { .. } => ErrorCategory::Internal,
        _ => ErrorCategory::Internal,
    }
}

/// Get a suggested error code for a LigatureError.
pub fn get_error_code(error: &LigatureError) -> ErrorCode {
    match error {
        LigatureError::Parse { .. } => ErrorCode::E1001,
        LigatureError::Type { .. } => ErrorCode::T2001,
        LigatureError::Evaluation { .. } => ErrorCode::R3001,
        LigatureError::Module { .. } => ErrorCode::M4001,
        LigatureError::Configuration { .. } => ErrorCode::C5001,
        LigatureError::InternalError { .. } => ErrorCode::I6001,
        _ => ErrorCode::I6001,
    }
}

/// Enhanced error reporter with advanced formatting options.
pub struct EnhancedErrorReporter {
    source: String,
    errors: Vec<LigatureError>,
    config: ErrorReportConfig,
}

impl EnhancedErrorReporter {
    /// Create a new enhanced error reporter.
    pub fn new(source: String) -> Self {
        Self {
            source,
            errors: Vec::new(),
            config: ErrorReportConfig::default(),
        }
    }

    /// Create a new enhanced error reporter with custom configuration.
    pub fn with_config(source: String, config: ErrorReportConfig) -> Self {
        Self {
            source,
            errors: Vec::new(),
            config,
        }
    }

    /// Add an error to the reporter.
    pub fn add_error(&mut self, error: LigatureError) {
        if self.errors.len() < self.config.max_errors {
            self.errors.push(error);
        }
    }

    /// Generate a comprehensive error report.
    pub fn report(&self) -> String {
        if self.errors.is_empty() {
            return "No errors found".to_string();
        }

        let mut output = String::new();

        // Group errors by category
        let mut errors_by_category: HashMap<ErrorCategory, Vec<&LigatureError>> = HashMap::new();

        for error in &self.errors {
            let category = get_error_category(error);
            errors_by_category
                .entry(category)
                .or_insert_with(Vec::new)
                .push(error);
        }

        // Report errors by category
        for (category, errors) in errors_by_category {
            if self.config.show_categories {
                output.push_str(&self.format_category_header(&category));
            }

            for (i, error) in errors.iter().enumerate() {
                if i > 0 {
                    output.push('\n');
                }
                output.push_str(&self.format_error(error));
            }

            output.push('\n');
        }

        if self.errors.len() >= self.config.max_errors {
            output.push_str(&format!(
                "\n\n... and {} more errors (max {} shown)",
                self.errors.len().saturating_sub(self.config.max_errors),
                self.config.max_errors
            ));
        }

        output
    }

    fn format_category_header(&self, category: &ErrorCategory) -> String {
        let mut output = String::new();

        if self.config.color_output {
            output.push_str(category.color_code());
        }

        output.push_str(&format!("{}s:\n", category.display_name()));

        if self.config.color_output {
            output.push_str("\x1b[0m"); // Reset
        }

        output
    }

    fn format_error(&self, error: &LigatureError) -> String {
        let mut output = String::new();

        // Error code
        if self.config.show_error_codes {
            let error_code = get_error_code(error);
            output.push_str(&format!("[{}] ", error_code.to_string()));
        }

        // Error header
        if self.config.color_output {
            output.push_str("\x1b[31m"); // Red
        }
        output.push_str("error: ");
        output.push_str(&error.to_string());
        if self.config.color_output {
            output.push_str("\x1b[0m"); // Reset
        }
        output.push('\n');

        // Source context
        if self.config.show_source {
            if let Some(span) = error.span() {
                output.push_str(&self.format_source_span(&span));
            }
        }

        // Suggestions
        if self.config.show_suggestions {
            let suggestions = error.get_suggestions();
            if !suggestions.is_empty() {
                if self.config.color_output {
                    output.push_str("\x1b[36m"); // Cyan
                }
                output.push_str("help:\n");
                if self.config.color_output {
                    output.push_str("\x1b[0m"); // Reset
                }
                for suggestion in suggestions {
                    output.push_str(&format!("  {}\n", suggestion));
                }
            }
        }

        output
    }

    fn format_source_span(&self, span: &Span) -> String {
        let lines: Vec<&str> = self.source.lines().collect();
        let line_num = span.line.saturating_sub(1);

        if line_num < lines.len() {
            let line = lines[line_num];
            let mut output = format!("  --> line {}:{}\n", span.line, span.column);
            output.push_str("  |\n");
            output.push_str(&format!("{} | {}\n", span.line, line));
            output.push_str("  |");

            for _ in 0..span.column.saturating_sub(1) {
                output.push(' ');
            }
            output.push_str(" ^\n");

            output
        } else {
            format!("  --> unknown location\n")
        }
    }
}

/// Utility function to create a LigatureError with context.
pub fn error_with_context(error: LigatureError, context: impl Into<String>) -> LigatureError {
    ErrorContext::new().with_context(context).build(error)
}

/// Utility function to create a LigatureError with suggestions.
pub fn error_with_suggestions(error: LigatureError, suggestions: Vec<String>) -> LigatureError {
    error.with_suggestions(suggestions)
}

/// Utility function to create a LigatureError with both context and suggestions.
pub fn error_with_context_and_suggestions(
    error: LigatureError,
    context: impl Into<String>,
    suggestions: Vec<String>,
) -> LigatureError {
    ErrorContext::new()
        .with_context(context)
        .with_suggestions(suggestions)
        .build(error)
}

/// Macro for creating errors with automatic context.
#[macro_export]
macro_rules! ligature_error {
    ($error:expr, $context:expr) => {
        $crate::error_utils::error_with_context($error, $context)
    };

    ($error:expr, $context:expr, $suggestions:expr) => {
        $crate::error_utils::error_with_context_and_suggestions($error, $context, $suggestions)
    };
}

/// Macro for creating parse errors with context.
#[macro_export]
macro_rules! parse_error {
    ($message:expr, $span:expr) => {
        $crate::LigatureError::Parse {
            code: $crate::ErrorCode::E1001,
            message: $message.to_string(),
            span: $span,
            suggestions: vec![],
        }
    };

    ($message:expr, $span:expr, $suggestions:expr) => {
        $crate::LigatureError::Parse {
            code: $crate::ErrorCode::E1001,
            message: $message.to_string(),
            span: $span,
            suggestions: $suggestions,
        }
    };
}

/// Macro for creating type errors with context.
#[macro_export]
macro_rules! type_error {
    ($message:expr, $span:expr) => {
        $crate::LigatureError::Type {
            code: $crate::ErrorCode::T2001,
            message: $message.to_string(),
            span: $span,
            expected: None,
            found: None,
            suggestions: vec![],
        }
    };

    ($message:expr, $span:expr, $expected:expr, $found:expr) => {
        $crate::LigatureError::Type {
            code: $crate::ErrorCode::T2001,
            message: $message.to_string(),
            span: $span,
            expected: Some($expected.to_string()),
            found: Some($found.to_string()),
            suggestions: vec![],
        }
    };
}

/// Macro for creating evaluation errors with context.
#[macro_export]
macro_rules! eval_error {
    ($message:expr, $span:expr) => {
        $crate::LigatureError::Evaluation {
            code: $crate::ErrorCode::R3001,
            message: $message.to_string(),
            span: $span,
            context: None,
        }
    };

    ($message:expr, $span:expr, $context:expr) => {
        $crate::LigatureError::Evaluation {
            code: $crate::ErrorCode::R3001,
            message: $message.to_string(),
            span: $span,
            context: Some($context.to_string()),
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ErrorCollection;

    #[test]
    fn test_error_context_builder() {
        let base_error = LigatureError::Evaluation {
            code: ErrorCode::R3001,
            message: "Runtime error".to_string(),
            span: Span::simple(0, 0),
            context: None,
        };

        let error_with_context = ErrorContext::new()
            .with_context("Failed to evaluate expression")
            .with_suggestion("Check the expression syntax")
            .with_suggestion("Verify all variables are defined")
            .build(base_error);

        if let LigatureError::Evaluation { context, .. } = error_with_context {
            assert!(context.is_some());
            assert!(context.unwrap().contains("Failed to evaluate expression"));
        }
    }

    #[test]
    fn test_error_collection() {
        let mut error_collection = ErrorCollection::new();

        let error1 = LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Test error 1".to_string(),
            span: Span::simple(0, 10),
            suggestions: vec!["Fix syntax".to_string()],
        };

        let error2 = LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Test error 2".to_string(),
            span: Span::simple(10, 20),
            expected: Some("integer".to_string()),
            found: Some("string".to_string()),
            suggestions: vec!["Convert to integer".to_string()],
        };

        assert!(error_collection.push(error1.clone()));
        assert!(error_collection.push(error2.clone()));

        assert_eq!(error_collection.len(), 2);
        assert!(error_collection.has_errors());
        assert!(!error_collection.is_empty());
    }

    #[test]
    fn test_error_categories() {
        let parse_error = LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            suggestions: vec![],
        };

        let type_error = LigatureError::Type {
            code: ErrorCode::T2001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            expected: None,
            found: None,
            suggestions: vec![],
        };

        let eval_error = LigatureError::Evaluation {
            code: ErrorCode::R3001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            context: None,
        };

        assert_eq!(get_error_category(&parse_error), ErrorCategory::Syntax);
        assert_eq!(get_error_category(&type_error), ErrorCategory::Type);
        assert_eq!(get_error_category(&eval_error), ErrorCategory::Runtime);
    }

    #[test]
    fn test_error_codes() {
        let parse_error = LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            suggestions: vec![],
        };

        let type_error = LigatureError::Type {
            code: ErrorCode::T2001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            expected: None,
            found: None,
            suggestions: vec![],
        };

        let eval_error = LigatureError::Evaluation {
            code: ErrorCode::R3001,
            message: "".to_string(),
            span: Span::simple(0, 0),
            context: None,
        };

        assert_eq!(get_error_code(&parse_error).to_string(), "E1001");
        assert_eq!(get_error_code(&type_error).to_string(), "T2001");
        assert_eq!(get_error_code(&eval_error).to_string(), "R3001");
    }

    #[test]
    fn test_user_friendly_errors() {
        let error = LigatureError::UndefinedIdentifier {
            code: ErrorCode::E1005,
            name: "undefined_var".to_string(),
            span: Span::simple(0, 0),
        };

        let user_friendly = error.to_user_friendly();

        assert!(user_friendly.contains("Error:"));
        assert!(user_friendly.contains("undefined_var"));
        assert!(user_friendly.contains("To fix this error:"));
        assert!(user_friendly.contains("Check if 'undefined_var' is defined"));
    }

    #[test]
    fn test_error_suggestions() {
        let error = LigatureError::UndefinedIdentifier {
            code: ErrorCode::E1005,
            name: "undefined_var".to_string(),
            span: Span::simple(0, 0),
        };

        let suggestions = error.get_suggestions();
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().any(|s| s.contains("undefined_var")));
        assert!(
            suggestions
                .iter()
                .any(|s| s.contains("defined in the current scope"))
        );
    }

    #[test]
    fn test_enhanced_error_reporter() {
        let source = "let x = 1 + \"hello\";\nlet y = x * 2;";
        let config = ErrorReportConfig {
            show_source: true,
            show_suggestions: true,
            max_errors: 5,
            color_output: false, // Disable colors for testing
            show_error_codes: true,
            show_categories: true,
        };

        let mut reporter = EnhancedErrorReporter::with_config(source.to_string(), config);

        let error = LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Cannot add integer and string".to_string(),
            span: Span::simple(8, 18),
            expected: Some("integer".to_string()),
            found: Some("string".to_string()),
            suggestions: vec![
                "Convert string to integer".to_string(),
                "Use string concatenation".to_string(),
            ],
        };

        reporter.add_error(error);

        let report = reporter.report();
        assert!(report.contains("Type Errors:"));
        assert!(report.contains("error:"));
        assert!(report.contains("help:"));
        assert!(report.contains("Convert string to integer"));
    }
}
