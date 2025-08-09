# Error Handling Migration Guide

This guide helps you migrate existing Ligature crates to use the new standardized error handling system.

## Overview

The new error handling system provides:

- **Consistent error types** across all crates
- **Rich error context** with suggestions and metadata
- **Structured error codes** for better categorization
- **Enhanced error reporting** with source code context
- **Error recovery strategies** for better user experience

## Migration Steps

### 1. Add the Dependency

Add `ligature-error` to your `Cargo.toml`:

```toml
[dependencies]
ligature-error = { workspace = true }
```

### 2. Update Imports

Replace existing error handling imports with the new standardized ones:

```rust
// Before
use anyhow::{Context, Result};
use thiserror::Error;

// After
use ligature_error::{
    StandardError, StandardResult, StandardErrorReporter, ErrorReportConfig,
    error_context, parse_error_with_context, type_error_with_context
};
```

### 3. Update Error Types

#### Before: Custom Error Types

```rust
#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Parse error: {0}")]
    Parse(String),
}
```

#### After: Using StandardError

```rust
// Use StandardError directly or create a wrapper
pub type MyResult<T> = StandardResult<T>;

// Or create a custom error that wraps StandardError
#[derive(Error, Debug)]
pub enum MyError {
    #[error("{0}")]
    Standard(#[from] StandardError),

    // Add any crate-specific errors here
    #[error("Custom error: {0}")]
    Custom(String),
}
```

### 4. Update Function Signatures

#### Before

```rust
fn process_file(path: &str) -> Result<String, MyError> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read {}", path))?;
    Ok(content)
}
```

#### After

```rust
fn process_file(path: &str) -> StandardResult<String> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| StandardError::io_error(e, format!("Failed to read {}", path)))?;
    Ok(content)
}
```

### 5. Enhanced Error Creation

#### Before: Simple Error Messages

```rust
return Err(MyError::Parse("Unexpected token".to_string()));
```

#### After: Rich Error Context

```rust
return Err(parse_error_with_context!(
    "Unexpected token",
    "Failed to parse configuration",
    "Invalid syntax"
).into());
```

### 6. Error Reporting

#### Before: Basic Error Printing

```rust
if let Err(e) = result {
    eprintln!("Error: {}", e);
}
```

#### After: Enhanced Error Reporting

```rust
if let Err(e) = result {
    let mut reporter = StandardErrorReporter::with_source_and_config(
        source_code,
        ErrorReportConfig {
            show_source: true,
            show_suggestions: true,
            show_error_codes: true,
            color_output: true,
            max_errors: 10,
            group_by_category: true,
            ..Default::default()
        }
    );
    reporter.add_error(e);
    eprintln!("{}", reporter.report());
}
```

## Migration Examples

### Example 1: Parser Crate

#### Before

```rust
// crates/ligature-parser/src/error.rs
#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Syntax error: {message}")]
    SyntaxError { message: String, span: Span },
}

pub type ParserResult<T> = Result<T, ParserError>;
```

#### After

```rust
// crates/ligature-parser/src/error.rs
pub use ligature_error::{StandardError, StandardResult};

// Re-export for backward compatibility
pub type ParserResult<T> = StandardResult<T>;

// Convert existing errors to StandardError
impl From<ParserError> for StandardError {
    fn from(err: ParserError) -> Self {
        match err {
            ParserError::SyntaxError { message, span } => {
                StandardError::Ligature(LigatureError::Parse {
                    code: ErrorCode::E1001,
                    message,
                    span,
                    suggestions: vec![],
                })
            }
        }
    }
}
```

### Example 2: Evaluation Crate

#### Before

```rust
// crates/ligature-eval/src/error.rs
#[derive(Error, Debug)]
pub enum EvaluationError {
    #[error("Runtime error: {message}")]
    RuntimeError { message: String, span: Span },
}

pub type EvaluationResult<T> = Result<T, EvaluationError>;
```

#### After

```rust
// crates/ligature-eval/src/error.rs
pub use ligature_error::{StandardError, StandardResult};

pub type EvaluationResult<T> = StandardResult<T>;

// Enhanced error creation
pub fn runtime_error(message: impl Into<String>, span: Span) -> StandardError {
    StandardError::Ligature(LigatureError::Evaluation {
        code: ErrorCode::R3001,
        message: message.into(),
        span,
        context: None,
    })
}
```

### Example 3: Application

#### Before

```rust
// apps/cacophony/src/main.rs
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let content = std::fs::read_to_string("config.lig")
        .with_context(|| "Failed to read config file")?;

    if let Err(e) = process_config(&content) {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }

    Ok(())
}
```

#### After

```rust
// apps/cacophony/src/main.rs
use ligature_error::{StandardError, StandardResult, StandardErrorReporter};

fn main() -> StandardResult<()> {
    let content = std::fs::read_to_string("config.lig")
        .map_err(|e| StandardError::io_error(e, "Failed to read config file"))?;

    if let Err(e) = process_config(&content) {
        let mut reporter = StandardErrorReporter::with_source_and_config(
            content,
            ErrorReportConfig::default()
        );
        reporter.add_error(e);
        eprintln!("{}", reporter.report());
        std::process::exit(1);
    }

    Ok(())
}
```

## Best Practices

### 1. Use Error Context Builders

```rust
let error = error_context!(
    "Failed to process configuration",
    "Invalid syntax",
    "Missing required field"
)
.suggestion("Add the missing field")
.suggestion("Check the configuration format")
.metadata("file", "config.lig")
.metadata("line", "10")
.build_parse_error("Unexpected token");
```

### 2. Use Error Macros for Common Patterns

```rust
// Parse errors
let parse_error = parse_error_with_context!("Unexpected token", "Context");

// Type errors
let type_error = type_error_with_context!("Type mismatch", "expected", "found", "Context");

// Evaluation errors
let eval_error = eval_error_with_context!("Runtime error", "Context");

// Module errors
let module_error = module_error_with_context!("Module not found", "path", "Context");

// Configuration errors
let config_error = config_error_with_context!("Invalid value", "field", "value", "Context");
```

### 3. Provide Rich Suggestions

```rust
let error = StandardError::Ligature(LigatureError::Type {
    code: ErrorCode::T2001,
    message: "Type mismatch".to_string(),
    span: Span::simple(1, 10),
    expected: Some("integer".to_string()),
    found: Some("string".to_string()),
    suggestions: vec![
        "Convert string to integer".to_string(),
        "Use string concatenation".to_string(),
        "Check the variable type".to_string(),
    ],
});
```

### 4. Use Error Recovery

```rust
if error.is_recoverable() {
    // Try to recover from the error
    match try_recovery_strategy(&error) {
        Ok(_) => continue,
        Err(_) => return Err(error),
    }
} else {
    // Non-recoverable error
    return Err(error);
}
```

### 5. Group Related Errors

```rust
let mut reporter = StandardErrorReporter::new();
reporter.add_errors(errors);
let report = reporter.report();
```

## Testing

### Test Error Creation

```rust
#[test]
fn test_error_creation() {
    let error = StandardError::configuration_error("Test error");
    assert!(error.to_string().contains("Test error"));
}
```

### Test Error Context

```rust
#[test]
fn test_error_with_context() {
    let error = StandardError::validation_error("Test error")
        .with_context("Context 1")
        .with_context("Context 2");

    assert!(error.to_string().contains("Context 1: Context 2: Test error"));
}
```

### Test Error Reporter

```rust
#[test]
fn test_error_reporter() {
    let mut reporter = StandardErrorReporter::new();
    let error = StandardError::internal_error("Test error");
    reporter.add_error(error);

    let report = reporter.report();
    assert!(report.contains("Test error"));
    assert!(report.contains("Internal Errors"));
}
```

## Backward Compatibility

To maintain backward compatibility during migration:

1. **Keep existing error types** but implement `From` traits
2. **Use type aliases** to gradually transition
3. **Add deprecation warnings** for old error types
4. **Provide migration helpers** for common patterns

```rust
// Backward compatibility
#[deprecated(since = "0.2.0", note = "Use StandardError instead")]
pub type OldResult<T> = Result<T, OldError>;

// Migration helper
pub fn migrate_error(old_error: OldError) -> StandardError {
    // Convert old error to new format
    StandardError::internal_error(old_error.to_string())
}
```

## Benefits of Migration

1. **Consistent Error Handling**: All crates use the same error types and patterns
2. **Better User Experience**: Rich error messages with suggestions and context
3. **Improved Debugging**: Structured error codes and metadata
4. **Enhanced Reporting**: Source code context and error grouping
5. **Error Recovery**: Built-in recovery strategies for better resilience
6. **Maintainability**: Centralized error handling logic

## Support

For questions or issues during migration:

- Check the [error handling example](../examples/error_handling_example.rs)
- Review the [API documentation](../crates/ligature-error/src/lib.rs)
- Open an issue in the project repository
