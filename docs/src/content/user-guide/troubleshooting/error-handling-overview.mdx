# Error Handling Overview

## Introduction

The Ligature error handling system provides consistent, user-friendly error reporting across all crates and applications. It features structured error codes, rich context, and actionable suggestions to help users quickly identify and fix issues.

## Key Features

### 🎯 Structured Error Codes

Errors are categorized with specific codes:

- **E1001-E1008**: Syntax errors (parse errors, unexpected tokens, etc.)
- **T2001-T2011**: Type errors (type mismatches, unification failures, etc.)
- **R3001-R3008**: Runtime errors (evaluation errors, division by zero, etc.)
- **M4001-M4005**: Module errors (module not found, import cycles, etc.)
- **C5001-C5005**: Configuration errors (invalid config, missing fields, etc.)
- **I6001-I6004**: Internal errors (compiler bugs, assertion failures, etc.)

### 📍 Rich Context

Errors include detailed context to help with debugging:

- Source code location (file, line, column)
- Operation being performed
- Relevant metadata
- Error categorization

### 💡 Actionable Suggestions

Each error provides specific suggestions for fixing the issue:

- Code examples
- Common solutions
- Best practices
- Related documentation

### 🎨 Enhanced Reporting

Beautiful, informative error reports with:

- Color-coded output
- Source code highlighting
- Error grouping by category
- Multiple error display

## Quick Start

### Basic Usage

```rust
use ligature_error::{StandardError, StandardResult};

pub fn my_function() -> StandardResult<()> {
    // Your code here
    if something_went_wrong {
        return Err(StandardError::validation_error("Something went wrong"));
    }
    Ok(())
}
```

### Rich Error Context

```rust
use ligature_error::{StandardError, StandardResult, ErrorContextBuilder};

pub fn process_file(path: &str) -> StandardResult<()> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| StandardError::io_error(e, "Failed to read file"))
        .with_context(ErrorContextBuilder::new()
            .file(path)
            .operation("file_reading")
            .build())?;

    // Process content...
    Ok(())
}
```

### Error Reporting

```rust
use ligature_error::{StandardErrorReporter, ErrorReportConfig};

let mut reporter = StandardErrorReporter::with_source_and_config(
    source_code,
    ErrorReportConfig::default()
);
reporter.add_error(error);
eprintln!("{}", reporter.report());
```

## Error Types

### StandardError

The main error type for all Ligature operations:

```rust
pub enum StandardError {
    Ligature(LigatureError),      // Ligature-specific errors
    Io(std::io::Error),           // IO errors
    Serialization(String),        // Serialization errors
    Deserialization(String),      // Deserialization errors
    Configuration(String),        // Configuration errors
    Validation(String),           // Validation errors
    Plugin(String),               // Plugin errors
    Network(String),              // Network errors
    Timeout(String),              // Timeout errors
    NotFound(String),             // Resource not found
    Permission(String),           // Permission errors
    Internal(String),             // Internal errors
    Unsupported(String),          // Unsupported operations
    InvalidArgument(String),      // Invalid arguments
}
```

### LigatureError

Ligature-specific errors with structured codes:

```rust
pub enum LigatureError {
    Parse { code, message, span, suggestions },
    Type { code, message, span, expected, found, suggestions },
    Evaluation { code, message, span, context },
    Module { code, message, path, cause },
    Configuration { code, message, field, value },
    // ... and many more
}
```

## Error Recovery

The system includes built-in recovery strategies:

```rust
if error.is_recoverable() {
    // Attempt automatic recovery
    match attempt_recovery() {
        Ok(result) => return Ok(result),
        Err(_) => return Err(original_error),
    }
}
```

## Best Practices

### 1. Use Appropriate Error Types

Choose the most specific error type for your use case:

- `StandardError::io_error()` for file operations
- `StandardError::validation_error()` for data validation
- `StandardError::configuration_error()` for config issues

### 2. Provide Rich Context

Always add context to help with debugging:

```rust
ErrorContextBuilder::new()
    .file("config.toml")
    .line(42)
    .operation("validation")
    .metadata("field", "database_url")
    .build()
```

### 3. Use Consistent Error Reporting

Always use `StandardErrorReporter` for user-facing errors:

```rust
let mut reporter = StandardErrorReporter::new(ErrorReportConfig::default());
reporter.add_error(error);
eprintln!("{}", reporter.report());
```

### 4. Handle Multiple Errors

Collect multiple errors and report them together:

```rust
let mut errors = Vec::new();
for item in items {
    if let Err(error) = process_item(item) {
        errors.push(error);
    }
}
```

## Migration

If you're migrating from the old error handling system, see the [Migration Guide](error-handling-migration.md) for step-by-step instructions.

## Examples

See the [examples directory](../../examples/) for comprehensive examples demonstrating all features of the error handling system.

## API Reference

For detailed API documentation, see the individual crate documentation:

- [ligature-error](../../crates/ligature-error/)
- [ligature-ast](../../crates/ligature-ast/)

## Support

For questions or issues:

1. Check the examples and documentation
2. Review the migration guide
3. Open an issue in the project repository
