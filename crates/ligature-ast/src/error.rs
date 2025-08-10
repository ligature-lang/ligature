//! Error types for the Ligature AST and compiler.

use anyhow::Result;
use thiserror::Error;

use crate::span::Span;

/// Main result type for Ligature operations using anyhow.
pub type LigatureResult<T> = Result<T>;

/// Error codes for categorizing and identifying specific error types.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    // Syntax errors (E1000-E1999)
    E1001, // Parse error
    E1002, // Unexpected token
    E1003, // Expected token
    E1004, // Invalid literal
    E1005, // Invalid identifier
    E1006, // Unterminated string
    E1007, // Unterminated comment
    E1008, // Invalid escape sequence

    // Type errors (T2000-T2999)
    T2001, // Type mismatch
    T2002, // Unification failed
    T2003, // Subtyping failed
    T2004, // Type argument mismatch
    T2005, // Missing method
    T2006, // Undefined method
    T2007, // Method type mismatch
    T2008, // No instance found
    T2009, // Duplicate type class
    T2010, // Undefined type class
    T2011, // Unused type parameter

    // Runtime errors (R3000-R3999)
    R3001, // Evaluation error
    R3002, // Division by zero
    R3003, // Pattern match failure
    R3004, // Unbound variable
    R3005, // Invalid function application
    R3006, // Stack overflow
    R3007, // Memory allocation failed
    R3008, // Timeout

    // Module errors (M4000-M4999)
    M4001, // Module not found
    M4002, // Import cycle
    M4003, // Invalid import path
    M4004, // Circular dependency
    M4005, // Module compilation failed

    // Configuration errors (C5000-C5999)
    C5001, // Configuration error
    C5002, // Invalid configuration format
    C5003, // Missing required field
    C5004, // Invalid field value
    C5005, // Configuration validation failed

    // Internal errors (I6000-I6999)
    I6001, // Internal error
    I6002, // Compiler bug
    I6003, // Assertion failed
    I6004, // Unreachable code
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl ErrorCode {
    /// Get the string representation of the error code.
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorCode::E1001 => "E1001",
            ErrorCode::E1002 => "E1002",
            ErrorCode::E1003 => "E1003",
            ErrorCode::E1004 => "E1004",
            ErrorCode::E1005 => "E1005",
            ErrorCode::E1006 => "E1006",
            ErrorCode::E1007 => "E1007",
            ErrorCode::E1008 => "E1008",
            ErrorCode::T2001 => "T2001",
            ErrorCode::T2002 => "T2002",
            ErrorCode::T2003 => "T2003",
            ErrorCode::T2004 => "T2004",
            ErrorCode::T2005 => "T2005",
            ErrorCode::T2006 => "T2006",
            ErrorCode::T2007 => "T2007",
            ErrorCode::T2008 => "T2008",
            ErrorCode::T2009 => "T2009",
            ErrorCode::T2010 => "T2010",
            ErrorCode::T2011 => "T2011",
            ErrorCode::R3001 => "R3001",
            ErrorCode::R3002 => "R3002",
            ErrorCode::R3003 => "R3003",
            ErrorCode::R3004 => "R3004",
            ErrorCode::R3005 => "R3005",
            ErrorCode::R3006 => "R3006",
            ErrorCode::R3007 => "R3007",
            ErrorCode::R3008 => "R3008",
            ErrorCode::M4001 => "M4001",
            ErrorCode::M4002 => "M4002",
            ErrorCode::M4003 => "M4003",
            ErrorCode::M4004 => "M4004",
            ErrorCode::M4005 => "M4005",
            ErrorCode::C5001 => "C5001",
            ErrorCode::C5002 => "C5002",
            ErrorCode::C5003 => "C5003",
            ErrorCode::C5004 => "C5004",
            ErrorCode::C5005 => "C5005",
            ErrorCode::I6001 => "I6001",
            ErrorCode::I6002 => "I6002",
            ErrorCode::I6003 => "I6003",
            ErrorCode::I6004 => "I6004",
        }
    }

    /// Get the category of this error code.
    pub fn category(&self) -> &'static str {
        match self {
            ErrorCode::E1001
            | ErrorCode::E1002
            | ErrorCode::E1003
            | ErrorCode::E1004
            | ErrorCode::E1005
            | ErrorCode::E1006
            | ErrorCode::E1007
            | ErrorCode::E1008 => "Syntax",
            ErrorCode::T2001
            | ErrorCode::T2002
            | ErrorCode::T2003
            | ErrorCode::T2004
            | ErrorCode::T2005
            | ErrorCode::T2006
            | ErrorCode::T2007
            | ErrorCode::T2008
            | ErrorCode::T2009
            | ErrorCode::T2010
            | ErrorCode::T2011 => "Type",
            ErrorCode::R3001
            | ErrorCode::R3002
            | ErrorCode::R3003
            | ErrorCode::R3004
            | ErrorCode::R3005
            | ErrorCode::R3006
            | ErrorCode::R3007
            | ErrorCode::R3008 => "Runtime",
            ErrorCode::M4001
            | ErrorCode::M4002
            | ErrorCode::M4003
            | ErrorCode::M4004
            | ErrorCode::M4005 => "Module",
            ErrorCode::C5001
            | ErrorCode::C5002
            | ErrorCode::C5003
            | ErrorCode::C5004
            | ErrorCode::C5005 => "Configuration",
            ErrorCode::I6001 | ErrorCode::I6002 | ErrorCode::I6003 | ErrorCode::I6004 => "Internal",
        }
    }

    /// Get a brief description of this error code.
    pub fn description(&self) -> &'static str {
        match self {
            ErrorCode::E1001 => "Parse error",
            ErrorCode::E1002 => "Unexpected token",
            ErrorCode::E1003 => "Expected token",
            ErrorCode::E1004 => "Invalid literal",
            ErrorCode::E1005 => "Invalid identifier",
            ErrorCode::E1006 => "Unterminated string",
            ErrorCode::E1007 => "Unterminated comment",
            ErrorCode::E1008 => "Invalid escape sequence",
            ErrorCode::T2001 => "Type mismatch",
            ErrorCode::T2002 => "Unification failed",
            ErrorCode::T2003 => "Subtyping failed",
            ErrorCode::T2004 => "Type argument mismatch",
            ErrorCode::T2005 => "Missing method",
            ErrorCode::T2006 => "Undefined method",
            ErrorCode::T2007 => "Method type mismatch",
            ErrorCode::T2008 => "No instance found",
            ErrorCode::T2009 => "Duplicate type class",
            ErrorCode::T2010 => "Undefined type class",
            ErrorCode::T2011 => "Unused type parameter",
            ErrorCode::R3001 => "Evaluation error",
            ErrorCode::R3002 => "Division by zero",
            ErrorCode::R3003 => "Pattern match failure",
            ErrorCode::R3004 => "Unbound variable",
            ErrorCode::R3005 => "Invalid function application",
            ErrorCode::R3006 => "Stack overflow",
            ErrorCode::R3007 => "Memory allocation failed",
            ErrorCode::R3008 => "Timeout",
            ErrorCode::M4001 => "Module not found",
            ErrorCode::M4002 => "Import cycle",
            ErrorCode::M4003 => "Invalid import path",
            ErrorCode::M4004 => "Circular dependency",
            ErrorCode::M4005 => "Module compilation failed",
            ErrorCode::C5001 => "Configuration error",
            ErrorCode::C5002 => "Invalid configuration format",
            ErrorCode::C5003 => "Missing required field",
            ErrorCode::C5004 => "Invalid field value",
            ErrorCode::C5005 => "Configuration validation failed",
            ErrorCode::I6001 => "Internal error",
            ErrorCode::I6002 => "Compiler bug",
            ErrorCode::I6003 => "Assertion failed",
            ErrorCode::I6004 => "Unreachable code",
        }
    }
}

/// Errors that can occur during AST construction or manipulation.
#[derive(Error, Debug, Clone, PartialEq)]
pub enum LigatureError {
    #[error("[{code}] Parse error: {message}")]
    Parse {
        code: ErrorCode,
        message: String,
        span: Span,
        suggestions: Vec<String>,
    },

    #[error("[{code}] Type error: {message}")]
    Type {
        code: ErrorCode,
        message: String,
        span: Span,
        expected: Option<String>,
        found: Option<String>,
        suggestions: Vec<String>,
    },

    #[error("[{code}] Evaluation error: {message}")]
    Evaluation {
        code: ErrorCode,
        message: String,
        span: Span,
        context: Option<String>,
    },

    #[error("[{code}] Module error: {message}")]
    Module {
        code: ErrorCode,
        message: String,
        path: Option<String>,
        cause: Option<String>,
    },

    #[error("[{code}] Configuration error: {message}")]
    Configuration {
        code: ErrorCode,
        message: String,
        field: Option<String>,
        value: Option<String>,
    },

    // Legacy AST errors for backward compatibility
    #[error("[{code}] Invalid identifier: {name}")]
    InvalidIdentifier {
        code: ErrorCode,
        name: String,
        span: Span,
    },

    #[error("[{code}] Duplicate identifier: {name}")]
    DuplicateIdentifier {
        code: ErrorCode,
        name: String,
        span: Span,
    },

    #[error("[{code}] Undefined identifier: {name}")]
    UndefinedIdentifier {
        code: ErrorCode,
        name: String,
        span: Span,
    },

    #[error("[{code}] Invalid type annotation")]
    InvalidTypeAnnotation { code: ErrorCode, span: Span },

    #[error("[{code}] Invalid expression")]
    InvalidExpression { code: ErrorCode, span: Span },

    #[error("[{code}] Invalid declaration")]
    InvalidDeclaration { code: ErrorCode, span: Span },

    #[error("[{code}] Circular dependency detected")]
    CircularDependency { code: ErrorCode, span: Span },

    #[error("[{code}] Invalid import path: {path}")]
    InvalidImportPath {
        code: ErrorCode,
        path: String,
        span: Span,
    },

    #[error("[{code}] Import cycle detected: {path}")]
    ImportCycle {
        code: ErrorCode,
        path: String,
        span: Span,
    },

    #[error("[{code}] Module not found: {module}")]
    ModuleNotFound {
        code: ErrorCode,
        module: String,
        span: Span,
    },

    #[error("[{code}] Internal error: {message}")]
    InternalError {
        code: ErrorCode,
        message: String,
        span: Span,
    },

    // Type class system errors
    #[error("[{code}] Duplicate type class: {name}")]
    DuplicateTypeClass {
        code: ErrorCode,
        name: String,
        span: Span,
    },

    #[error("[{code}] Undefined type class: {name}")]
    UndefinedTypeClass {
        code: ErrorCode,
        name: String,
        span: Span,
    },

    #[error("[{code}] Unused type parameter: {parameter}")]
    UnusedTypeParameter {
        code: ErrorCode,
        parameter: String,
        span: Span,
    },

    #[error("[{code}] Type argument mismatch: expected {expected}, found {found}")]
    TypeArgumentMismatch {
        code: ErrorCode,
        expected: usize,
        found: usize,
        span: Span,
    },

    #[error("[{code}] Missing method: {method} in class {class}")]
    MissingMethod {
        code: ErrorCode,
        method: String,
        class: String,
        span: Span,
    },

    #[error("[{code}] Undefined method: {method} in class {class}")]
    UndefinedMethod {
        code: ErrorCode,
        method: String,
        class: String,
        span: Span,
    },

    #[error("[{code}] Method type mismatch: {method}, expected {expected:?}, found {found:?}")]
    MethodTypeMismatch {
        code: ErrorCode,
        method: String,
        expected: crate::Type,
        found: crate::Type,
        span: Span,
    },

    #[error("[{code}] No instance found for type {type_:?} in class {class}")]
    NoInstanceFound {
        code: ErrorCode,
        class: String,
        type_: crate::Type,
        span: Span,
    },
}

impl LigatureError {
    /// Get the error code for this error.
    pub fn code(&self) -> ErrorCode {
        match self {
            LigatureError::Parse { code, .. } => code.clone(),
            LigatureError::Type { code, .. } => code.clone(),
            LigatureError::Evaluation { code, .. } => code.clone(),
            LigatureError::Module { code, .. } => code.clone(),
            LigatureError::Configuration { code, .. } => code.clone(),
            LigatureError::InvalidIdentifier { code, .. } => code.clone(),
            LigatureError::DuplicateIdentifier { code, .. } => code.clone(),
            LigatureError::UndefinedIdentifier { code, .. } => code.clone(),
            LigatureError::InvalidTypeAnnotation { code, .. } => code.clone(),
            LigatureError::InvalidExpression { code, .. } => code.clone(),
            LigatureError::InvalidDeclaration { code, .. } => code.clone(),
            LigatureError::CircularDependency { code, .. } => code.clone(),
            LigatureError::InvalidImportPath { code, .. } => code.clone(),
            LigatureError::ImportCycle { code, .. } => code.clone(),
            LigatureError::ModuleNotFound { code, .. } => code.clone(),
            LigatureError::InternalError { code, .. } => code.clone(),
            LigatureError::DuplicateTypeClass { code, .. } => code.clone(),
            LigatureError::UndefinedTypeClass { code, .. } => code.clone(),
            LigatureError::UnusedTypeParameter { code, .. } => code.clone(),
            LigatureError::TypeArgumentMismatch { code, .. } => code.clone(),
            LigatureError::MissingMethod { code, .. } => code.clone(),
            LigatureError::UndefinedMethod { code, .. } => code.clone(),
            LigatureError::MethodTypeMismatch { code, .. } => code.clone(),
            LigatureError::NoInstanceFound { code, .. } => code.clone(),
        }
    }

    /// Get the span associated with this error.
    pub fn span(&self) -> Option<Span> {
        match self {
            LigatureError::Parse { span, .. } => Some(span.clone()),
            LigatureError::Type { span, .. } => Some(span.clone()),
            LigatureError::Evaluation { span, .. } => Some(span.clone()),
            LigatureError::InvalidIdentifier { span, .. } => Some(span.clone()),
            LigatureError::DuplicateIdentifier { span, .. } => Some(span.clone()),
            LigatureError::UndefinedIdentifier { span, .. } => Some(span.clone()),
            LigatureError::InvalidTypeAnnotation { span, .. } => Some(span.clone()),
            LigatureError::InvalidExpression { span, .. } => Some(span.clone()),
            LigatureError::InvalidDeclaration { span, .. } => Some(span.clone()),
            LigatureError::CircularDependency { span, .. } => Some(span.clone()),
            LigatureError::InvalidImportPath { span, .. } => Some(span.clone()),
            LigatureError::ImportCycle { span, .. } => Some(span.clone()),
            LigatureError::ModuleNotFound { span, .. } => Some(span.clone()),
            LigatureError::InternalError { span, .. } => Some(span.clone()),
            LigatureError::DuplicateTypeClass { span, .. } => Some(span.clone()),
            LigatureError::UndefinedTypeClass { span, .. } => Some(span.clone()),
            LigatureError::UnusedTypeParameter { span, .. } => Some(span.clone()),
            LigatureError::TypeArgumentMismatch { span, .. } => Some(span.clone()),
            LigatureError::MissingMethod { span, .. } => Some(span.clone()),
            LigatureError::UndefinedMethod { span, .. } => Some(span.clone()),
            LigatureError::MethodTypeMismatch { span, .. } => Some(span.clone()),
            LigatureError::NoInstanceFound { span, .. } => Some(span.clone()),
            LigatureError::Module { .. } | LigatureError::Configuration { .. } => None,
        }
    }

    /// Add suggestions to the error.
    pub fn with_suggestions(mut self, suggestions: Vec<String>) -> Self {
        match &mut self {
            LigatureError::Parse { suggestions: s, .. } => *s = suggestions,
            LigatureError::Type { suggestions: s, .. } => *s = suggestions,
            _ => {}
        }
        self
    }

    /// Add context to the error.
    pub fn with_context(mut self, context: String) -> Self {
        if let LigatureError::Evaluation { context: c, .. } = &mut self {
            *c = Some(context)
        }
        self
    }

    /// Get user-friendly suggestions for this error.
    pub fn get_suggestions(&self) -> Vec<String> {
        match self {
            LigatureError::Parse { suggestions, .. } => suggestions.clone(),
            LigatureError::Type { suggestions, .. } => suggestions.clone(),
            LigatureError::UndefinedIdentifier { name, .. } => vec![
                format!("Check if '{}' is defined in the current scope", name),
                "Make sure the variable is declared before use".to_string(),
                "Check for typos in the variable name".to_string(),
            ],
            LigatureError::DuplicateIdentifier { name, .. } => vec![
                format!("Rename one of the '{}' declarations", name),
                "Use different names for different variables".to_string(),
                "Check if you meant to use a different variable".to_string(),
            ],
            LigatureError::InvalidIdentifier { name, .. } => vec![
                format!("'{}' is not a valid identifier", name),
                "Identifiers must start with a letter or underscore".to_string(),
                "Identifiers can only contain letters, digits, and underscores".to_string(),
            ],
            LigatureError::ModuleNotFound { module, .. } => vec![
                format!("Check if the module '{}' exists", module),
                "Verify the module path is correct".to_string(),
                "Make sure the module file is in the search path".to_string(),
            ],
            LigatureError::ImportCycle { path, .. } => vec![
                format!("Break the circular dependency involving '{}'", path),
                "Restructure your modules to avoid circular imports".to_string(),
                "Consider using forward declarations if needed".to_string(),
            ],
            LigatureError::Evaluation { .. } => vec![
                "Check the expression and try again".to_string(),
                "Verify all variables are defined".to_string(),
                "Check for runtime errors".to_string(),
            ],
            _ => vec!["Check the syntax and try again".to_string()],
        }
    }

    /// Display the error with source context.
    pub fn display(&self, source: &str) -> String {
        match self {
            LigatureError::Parse {
                message,
                span,
                suggestions,
                ..
            } => {
                let mut output = format!("Parse error: {message}\n");
                output.push_str(&span.display(source));
                if !suggestions.is_empty() {
                    output.push_str("\nSuggestions:\n");
                    for suggestion in suggestions {
                        output.push_str(&format!("  - {suggestion}\n"));
                    }
                }
                output
            }
            LigatureError::Type {
                message,
                span,
                expected,
                found,
                suggestions,
                ..
            } => {
                let mut output = format!("Type error: {message}\n");
                output.push_str(&span.display(source));
                if let (Some(expected), Some(found)) = (expected, found) {
                    output.push_str(&format!("Expected: {expected}\nFound: {found}\n"));
                }
                if !suggestions.is_empty() {
                    output.push_str("Suggestions:\n");
                    for suggestion in suggestions {
                        output.push_str(&format!("  - {suggestion}\n"));
                    }
                }
                output
            }
            LigatureError::Evaluation {
                message,
                span,
                context,
                ..
            } => {
                let mut output = format!("Evaluation error: {message}\n");
                output.push_str(&span.display(source));
                if let Some(context) = context {
                    output.push_str(&format!("Context: {context}\n"));
                }
                output
            }
            _ => self.to_string(),
        }
    }

    /// Create a user-friendly error message with suggestions.
    pub fn to_user_friendly(&self) -> String {
        let mut output = format!("Error: {self}\n");

        let suggestions = self.get_suggestions();
        if !suggestions.is_empty() {
            output.push_str("\nTo fix this error:\n");
            for (i, suggestion) in suggestions.iter().enumerate() {
                output.push_str(&format!("  {}. {}\n", i + 1, suggestion));
            }
        }

        output
    }
}

// Legacy AstError for backward compatibility
pub type AstError = LigatureError;

/// Result type for AST operations.
pub type AstResult<T> = Result<T>;

/// A collection of errors that occurred during compilation.
#[derive(Debug, Clone)]
pub struct ErrorCollection {
    pub errors: Vec<LigatureError>,
    pub max_errors: usize,
}

impl ErrorCollection {
    /// Create a new empty error collection.
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            max_errors: 10, // Default to collecting up to 10 errors
        }
    }

    /// Create a new error collection with a maximum error limit.
    pub fn with_max_errors(max_errors: usize) -> Self {
        Self {
            errors: Vec::new(),
            max_errors,
        }
    }

    /// Add an error to the collection.
    pub fn push(&mut self, error: LigatureError) -> bool {
        if self.errors.len() < self.max_errors {
            self.errors.push(error);
            true
        } else {
            false
        }
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

    /// Check if the collection has reached its maximum capacity.
    pub fn is_full(&self) -> bool {
        self.errors.len() >= self.max_errors
    }

    /// Convert to a result, returning the first error if any exist.
    pub fn into_result<T>(self, value: T) -> LigatureResult<T> {
        if self.has_errors() {
            Err(self.errors.into_iter().next().unwrap().into())
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

impl std::fmt::Display for ErrorCollection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.errors.is_empty() {
            return write!(f, "No errors");
        }

        let mut output = format!("Found {} error(s):\n\n", self.errors.len());

        for (i, error) in self.errors.iter().enumerate() {
            output.push_str(&format!("{}. {}\n", i + 1, error.to_user_friendly()));
            if i < self.errors.len() - 1 {
                output.push('\n');
            }
        }

        if self.is_full() {
            output.push_str(&format!(
                "\n... and {} more errors (max {} shown)",
                self.errors.len().saturating_sub(self.max_errors),
                self.max_errors
            ));
        }

        write!(f, "{output}")
    }
}

impl From<LigatureError> for ErrorCollection {
    fn from(error: LigatureError) -> Self {
        Self {
            errors: vec![error],
            max_errors: 10,
        }
    }
}

/// Error reporter for formatting and displaying errors with source context.
pub struct ErrorReporter {
    source: String,
    errors: Vec<LigatureError>,
    config: ErrorReportConfig,
}

#[derive(Debug, Clone)]
pub struct ErrorReportConfig {
    pub show_source: bool,
    pub show_suggestions: bool,
    pub max_errors: usize,
    pub color_output: bool,
}

impl Default for ErrorReportConfig {
    fn default() -> Self {
        Self {
            show_source: true,
            show_suggestions: true,
            max_errors: 10,
            color_output: true,
        }
    }
}

impl ErrorReporter {
    /// Create a new error reporter.
    pub fn new(source: String) -> Self {
        Self {
            source,
            errors: Vec::new(),
            config: ErrorReportConfig::default(),
        }
    }

    /// Create a new error reporter with custom configuration.
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

    /// Generate a formatted error report.
    pub fn report(&self) -> String {
        if self.errors.is_empty() {
            return "No errors found".to_string();
        }

        let mut output = String::new();

        for (i, error) in self.errors.iter().enumerate() {
            if i > 0 {
                output.push('\n');
            }
            output.push_str(&self.format_error(error));
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

    fn format_error(&self, error: &LigatureError) -> String {
        let mut output = String::new();

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
                    output.push_str(&format!("  {suggestion}\n"));
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
            "  --> unknown location\n".to_string()
        }
    }
}
