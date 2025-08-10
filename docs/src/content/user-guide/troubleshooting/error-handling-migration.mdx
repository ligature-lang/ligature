# Error Handling Migration Guide

This guide provides step-by-step instructions for migrating existing Ligature crates and applications to use the new standardized error handling system.

## Overview

The new error handling system consists of:

1. **Enhanced `ligature-ast` crate**: Contains structured error codes and improved error types
2. **New `ligature-error` crate**: Provides standardized error handling across all crates
3. **Consistent error reporting**: Rich error messages with source context and suggestions

## Migration Steps

### Step 1: Update Dependencies

Add the `ligature-error` crate to your `Cargo.toml`:

```toml
[dependencies]
ligature-error = { workspace = true }
```

### Step 2: Import New Error Types

Replace existing error imports with the new standardized types:

```rust
// Old imports
use anyhow::Result;
use thiserror::Error;

// New imports
use ligature_error::{
    StandardError, StandardResult, StandardErrorReporter,
    ErrorReportConfig, ErrorContextBuilder
};
```

### Step 3: Update Error Types

Replace custom error types with `StandardError`:

```rust
// Old approach
#[derive(Error, Debug)]
pub enum MyError {
    #[error("Parse error: {0}")]
    Parse(String),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

// New approach
pub type MyResult<T> = StandardResult<T>;

// Use StandardError directly or create specific error types
pub fn my_function() -> MyResult<()> {
    // Your implementation
    Ok(())
}
```

### Step 4: Update Result Types

Replace `anyhow::Result` with `StandardResult`:

```rust
// Old
pub fn process_data() -> anyhow::Result<()> {
    // implementation
}

// New
pub fn process_data() -> StandardResult<()> {
    // implementation
}
```

### Step 5: Use Error Context Builder

For rich error contexts, use the `ErrorContextBuilder`:

```rust
use ligature_error::ErrorContextBuilder;

pub fn process_file(path: &str) -> StandardResult<()> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| StandardError::io_error(e, "Failed to read file"))
        .with_context(ErrorContextBuilder::new()
            .file(path)
            .operation("file_reading")
            .metadata("size", content.len().to_string())
            .build())?;

    Ok(())
}
```

### Step 6: Implement Error Reporting

Use the `StandardErrorReporter` for consistent error display:

```rust
use ligature_error::{StandardErrorReporter, ErrorReportConfig};

pub fn handle_errors(errors: Vec<StandardError>, source: &str) {
    let config = ErrorReportConfig {
        show_source: true,
        show_suggestions: true,
        show_error_codes: true,
        show_categories: true,
        color_output: true,
        max_errors: 10,
        show_metadata: true,
        group_by_category: true,
    };

    let mut reporter = StandardErrorReporter::with_source_and_config(source.to_string(), config);

    for error in errors {
        reporter.add_error(error);
    }

    eprintln!("{}", reporter.report());
}
```

## Migration Examples

### Example 1: Simple Function Migration

**Before:**

```rust
use anyhow::Result;

pub fn parse_config(data: &str) -> Result<Config> {
    serde_json::from_str(data)
        .with_context(|| "Failed to parse configuration")
}
```

**After:**

```rust
use ligature_error::{StandardError, StandardResult};

pub fn parse_config(data: &str) -> StandardResult<Config> {
    serde_json::from_str(data)
        .map_err(|e| StandardError::deserialization_error(e.to_string()))
}
```

### Example 2: Complex Error Handling

**Before:**

```rust
use anyhow::{Context, Result};

pub fn process_file(path: &str) -> Result<()> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read file: {}", path))?;

    let config = serde_json::from_str(&content)
        .with_context(|| "Failed to parse JSON")?;

    validate_config(&config)
        .with_context(|| "Configuration validation failed")?;

    Ok(())
}
```

**After:**

```rust
use ligature_error::{StandardError, StandardResult, ErrorContextBuilder};

pub fn process_file(path: &str) -> StandardResult<()> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| StandardError::io_error(e, "Failed to read file"))
        .with_context(ErrorContextBuilder::new()
            .file(path)
            .operation("file_reading")
            .build())?;

    let config = serde_json::from_str(&content)
        .map_err(|e| StandardError::deserialization_error(e.to_string()))
        .with_context(ErrorContextBuilder::new()
            .file(path)
            .operation("json_parsing")
            .build())?;

    validate_config(&config)
        .map_err(|e| StandardError::validation_error(e.to_string()))
        .with_context(ErrorContextBuilder::new()
            .file(path)
            .operation("validation")
            .build())?;

    Ok(())
}
```

### Example 3: CLI Application Migration

**Before:**

```rust
use anyhow::Result;

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();

    if args.len() != 2 {
        anyhow::bail!("Usage: {} <file>", args[0]);
    }

    let file = &args[1];
    process_file(file)
}
```

**After:**

```rust
use ligature_error::{StandardError, StandardResult, StandardErrorReporter, ErrorReportConfig};

fn main() -> StandardResult<()> {
    let args = std::env::args().collect::<Vec<_>>();

    if args.len() != 2 {
        return Err(StandardError::invalid_argument_error(
            format!("Usage: {} <file>", args[0])
        ));
    }

    let file = &args[1];
    let result = process_file(file);

    if let Err(error) = result {
        let config = ErrorReportConfig {
            show_source: true,
            show_suggestions: true,
            show_error_codes: true,
            show_categories: true,
            color_output: true,
            max_errors: 10,
            show_metadata: false,
            group_by_category: true,
        };

        let mut reporter = StandardErrorReporter::new(config);
        reporter.add_error(error);
        eprintln!("{}", reporter.report());
    }

    result
}
```

## Best Practices

### 1. Use Appropriate Error Types

Choose the most specific error type for your use case:

```rust
// For file operations
StandardError::io_error(io_error, "context")

// For configuration issues
StandardError::configuration_error("message")

// For validation failures
StandardError::validation_error("message")

// For internal errors
StandardError::internal_error("message")
```

### 2. Provide Rich Context

Use `ErrorContextBuilder` to add metadata:

```rust
ErrorContextBuilder::new()
    .file("config.toml")
    .line(42)
    .operation("validation")
    .metadata("field", "database_url")
    .metadata("value", "***")
    .build()
```

### 3. Use Consistent Error Reporting

Always use `StandardErrorReporter` for user-facing error messages:

```rust
let mut reporter = StandardErrorReporter::with_source_and_config(
    source_code,
    ErrorReportConfig::default()
);
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

if !errors.is_empty() {
    let mut reporter = StandardErrorReporter::new(ErrorReportConfig::default());
    for error in errors {
        reporter.add_error(error);
    }
    eprintln!("{}", reporter.report());
}
```

## Testing

### Unit Tests

Test error handling in your unit tests:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use ligature_error::StandardError;

    #[test]
    fn test_invalid_input() {
        let result = process_data("invalid");
        assert!(result.is_err());

        if let Err(StandardError::Validation(_)) = result {
            // Expected error type
        } else {
            panic!("Expected validation error");
        }
    }
}
```

### Integration Tests

Test error reporting in integration tests:

```rust
#[test]
fn test_error_reporting() {
    let result = process_file("nonexistent.txt");
    assert!(result.is_err());

    // Verify error contains expected information
    if let Err(error) = result {
        assert!(error.get_suggestions().len() > 0);
        assert_eq!(error.error_code(), None); // Not a Ligature error
    }
}
```

## Troubleshooting

### Common Issues

1. **Compilation errors with `StandardResult`**: Make sure you've imported `StandardResult` from `ligature_error`
2. **Missing error context**: Use `ErrorContextBuilder` to add rich context to errors
3. **Poor error messages**: Ensure you're using `StandardErrorReporter` for user-facing errors

### Debugging

Enable verbose error reporting for debugging:

```rust
let config = ErrorReportConfig {
    show_source: true,
    show_suggestions: true,
    show_error_codes: true,
    show_categories: true,
    color_output: false, // Disable colors for logs
    max_errors: 100,     // Show more errors
    show_metadata: true,
    group_by_category: false,
};
```

## Migration Checklist

- [ ] Add `ligature-error` dependency to `Cargo.toml`
- [ ] Update imports to use new error types
- [ ] Replace `anyhow::Result` with `StandardResult`
- [ ] Update error creation to use `StandardError`
- [ ] Implement error reporting with `StandardErrorReporter`
- [ ] Add error context using `ErrorContextBuilder`
- [ ] Update tests to use new error types
- [ ] Verify error messages are user-friendly
- [ ] Test error recovery scenarios

## Next Steps

After completing the migration:

1. **Performance optimization**: Profile error reporting for large codebases
2. **Custom error types**: Create domain-specific error types if needed
3. **Error recovery**: Implement recovery strategies for common errors
4. **Documentation**: Update API documentation with error examples
5. **Monitoring**: Add error tracking and analytics

## Support

For questions or issues with the migration:

1. Check the examples in the `examples/` directory
2. Review the API documentation
3. Look at existing migrated crates for reference
4. Open an issue in the project repository
