//! Comprehensive examples demonstrating the new error handling system.
//!
//! This file shows how to use the enhanced error handling features including:
//! - Standardized error types
//! - Rich error context
//! - Error reporting with source code
//! - Error recovery strategies
//! - Multiple error collection

use std::collections::HashMap;

use ligature_ast::{ErrorCode, LigatureError, Span};
use ligature_error::{ErrorReportConfig, StandardError, StandardErrorReporter, StandardResult};

/// Example 1: Basic error handling with StandardError
pub fn basic_error_example() -> StandardResult<()> {
    // Simulate a file read operation
    let file_path = "config.json";

    // This would normally be a real file read
    let content = "invalid json content";

    // Parse JSON with error handling
    let parsed: serde_json::Value = serde_json::from_str(content)
        .map_err(|e| StandardError::deserialization_error(e.to_string()))
        .map_err(|e| {
            e.with_context(format!(
                "Failed to parse file: {file_path} during json_parsing"
            ))
        })?;

    println!("Successfully parsed: {parsed:?}");
    Ok(())
}

/// Example 2: Rich error context with metadata
pub fn rich_context_example() -> StandardResult<()> {
    let config_data = r#"
    {
        "database": {
            "host": "localhost",
            "port": "invalid_port"
        }
    }
    "#;

    // Parse with rich context
    let config: HashMap<String, serde_json::Value> = serde_json::from_str(config_data)
        .map_err(|e| StandardError::deserialization_error(e.to_string()))
        .map_err(|e| {
            e.with_context(format!(
                "Configuration parsing failed: format=json, size={}",
                config_data.len()
            ))
        })?;

    // Validate configuration
    if let Some(db_config) = config.get("database") {
        if let Some(port) = db_config.get("port") {
            if let Some(port_str) = port.as_str() {
                if port_str.parse::<u16>().is_err() {
                    return Err(StandardError::validation_error(format!(
                        "Invalid port number: {port_str}"
                    ))
                    .with_context(format!(
                        "Port validation failed: field=database.port, value={port_str}"
                    )));
                }
            }
        }
    }

    Ok(())
}

/// Example 3: Multiple error collection and reporting
pub fn multiple_errors_example() -> StandardResult<()> {
    let source_code = r#"
    let x = 42;
    let y = "hello";
    let z = x + y;  // Type error
    let undefined_var = not_defined;  // Undefined variable
    "#;

    let mut errors = Vec::new();

    // Simulate parsing and type checking
    if source_code.contains("not_defined") {
        errors.push(StandardError::Ligature(
            LigatureError::UndefinedIdentifier {
                code: ErrorCode::R3004,
                name: "not_defined".to_string(),
                span: Span::new(4, 5, 1, 20),
            },
        ));
    }

    if source_code.contains("x + y") {
        errors.push(StandardError::Ligature(LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Cannot add integer and string".to_string(),
            span: Span::new(3, 3, 1, 15),
            expected: Some("integer".to_string()),
            found: Some("string".to_string()),
            suggestions: vec![
                "Convert string to integer".to_string(),
                "Use string concatenation instead".to_string(),
            ],
        }));
    }

    if !errors.is_empty() {
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

        let mut reporter =
            StandardErrorReporter::with_source_and_config(source_code.to_string(), config);

        for error in errors {
            reporter.add_error(error);
        }

        eprintln!("{}", reporter.report());
        return Err(StandardError::validation_error("Multiple errors found"));
    }

    Ok(())
}

/// Example 4: Error recovery strategies
pub fn error_recovery_example() -> StandardResult<()> {
    let mut attempts = 0;
    let max_attempts = 3;

    loop {
        attempts += 1;

        match perform_operation() {
            Ok(result) => {
                println!("Operation successful: {result:?}");
                return Ok(());
            }
            Err(error) => {
                if error.is_recoverable() && attempts < max_attempts {
                    println!("Attempt {attempts} failed, retrying...");
                    std::thread::sleep(std::time::Duration::from_millis(100));
                    continue;
                } else {
                    return Err(error.with_context(format!(
                        "Operation failed after retries: attempts={attempts}, \
                         max_attempts={max_attempts}"
                    )));
                }
            }
        }
    }
}

fn perform_operation() -> StandardResult<String> {
    // Simulate an operation that might fail
    if rand::random::<bool>() {
        Ok("success".to_string())
    } else {
        Err(StandardError::validation_error("Random failure"))
    }
}

/// Example 5: Custom error types with conversion
pub fn custom_error_example() -> StandardResult<()> {
    #[derive(Debug, thiserror::Error)]
    pub enum CustomError {
        #[error("Network error: {0}")]
        Network(String),
        #[error("Timeout after {0} seconds")]
        Timeout(u64),
    }

    impl From<CustomError> for StandardError {
        fn from(err: CustomError) -> Self {
            match err {
                CustomError::Network(msg) => StandardError::network_error(msg),
                CustomError::Timeout(seconds) => StandardError::timeout_error(format!(
                    "Operation timed out after {seconds} seconds"
                )),
            }
        }
    }

    // Use custom error
    let result: StandardResult<()> =
        Err(CustomError::Network("Connection refused".to_string()).into());

    match result {
        Ok(_) => println!("Success"),
        Err(error) => {
            println!("Error: {error}");
            if let StandardError::Network(_) = error {
                println!("This is a network error");
            }
        }
    }

    Ok(())
}

/// Example 6: CLI application error handling
pub fn cli_error_example() -> StandardResult<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        return Err(StandardError::invalid_argument_error(format!(
            "Usage: {} <file>",
            args.first().unwrap_or(&"program".to_string())
        )));
    }

    let file_path = &args[1];

    // Simulate file processing
    let content = std::fs::read_to_string(file_path)
        .map_err(|e| StandardError::io_error(e, "Failed to read file"))
        .map_err(|e| e.with_context(format!("Failed to read file: {file_path}")))?;

    // Process content
    process_content(&content).map_err(|e| {
        e.with_context(format!(
            "Failed to process file: {} (size={})",
            file_path,
            content.len()
        ))
    })?;

    println!("File processed successfully");
    Ok(())
}

fn process_content(content: &str) -> StandardResult<()> {
    if content.is_empty() {
        return Err(StandardError::validation_error("File is empty"));
    }

    if content.len() > 1000 {
        return Err(StandardError::validation_error("File too large"));
    }

    Ok(())
}

/// Example 7: Error reporting with different configurations
pub fn error_reporting_examples() {
    let source_code = r#"
    fn main() {
        let x = 42;
        let y = "hello";
        let result = x + y;  // Type error
    }
    "#;

    let error = StandardError::Ligature(LigatureError::Type {
        code: ErrorCode::T2001,
        message: "Cannot add integer and string".to_string(),
        span: Span::new(4, 4, 1, 25),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec![
            "Convert string to integer: x + y.parse::<i32>()".to_string(),
            "Use string concatenation: format!(\"{}{}\", x, y)".to_string(),
        ],
    });

    // Basic reporting
    println!("=== Basic Error Report ===");
    let mut basic_reporter = StandardErrorReporter::new();
    basic_reporter.add_error(error);
    println!("{}", basic_reporter.report());

    // Detailed reporting
    println!("\n=== Detailed Error Report ===");
    let detailed_config = ErrorReportConfig {
        show_source: true,
        show_suggestions: true,
        show_error_codes: true,
        show_categories: true,
        color_output: false, // Disable colors for this example
        max_errors: 10,
        show_metadata: true,
        group_by_category: true,
    };

    let mut detailed_reporter =
        StandardErrorReporter::with_source_and_config(source_code.to_string(), detailed_config);

    // Create a new error for the detailed reporter
    let detailed_error = StandardError::Ligature(LigatureError::Type {
        code: ErrorCode::T2001,
        message: "Cannot add integer and string".to_string(),
        span: Span::new(4, 4, 1, 25),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec![
            "Convert string to integer: x + y.parse::<i32>()".to_string(),
            "Use string concatenation: format!(\"{}{}\", x, y)".to_string(),
        ],
    });

    detailed_reporter.add_error(detailed_error);
    println!("{}", detailed_reporter.report());
}

/// Example 8: Error handling in async contexts
pub async fn async_error_example() -> StandardResult<()> {
    use tokio::time::{Duration, sleep};

    // Simulate async operation
    sleep(Duration::from_millis(100)).await;

    // Simulate async error
    if rand::random::<bool>() {
        Err(StandardError::timeout_error("Async operation timed out"))
    } else {
        Ok(())
    }
}

/// Example 9: Error categorization and filtering
pub fn error_categorization_example() -> StandardResult<()> {
    let errors = vec![
        StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Unexpected token".to_string(),
            span: Span::new(1, 1, 1, 10),
            suggestions: vec!["Check syntax".to_string()],
        }),
        StandardError::Ligature(LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Type mismatch".to_string(),
            span: Span::new(2, 2, 1, 15),
            expected: Some("string".to_string()),
            found: Some("integer".to_string()),
            suggestions: vec!["Convert types".to_string()],
        }),
        StandardError::configuration_error("Invalid configuration"),
    ];

    // Categorize errors
    let mut syntax_errors = Vec::new();
    let mut type_errors = Vec::new();
    let mut config_errors = Vec::new();

    for error in errors {
        match error {
            StandardError::Ligature(ref ligature_error) => {
                let code = ligature_error.code();
                if matches!(
                    code,
                    ErrorCode::E1001
                        | ErrorCode::E1002
                        | ErrorCode::E1003
                        | ErrorCode::E1004
                        | ErrorCode::E1005
                        | ErrorCode::E1006
                        | ErrorCode::E1007
                        | ErrorCode::E1008
                ) {
                    syntax_errors.push(error);
                } else if matches!(
                    code,
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
                        | ErrorCode::T2011
                ) {
                    type_errors.push(error);
                }
            }
            StandardError::Configuration(_) => config_errors.push(error),
            _ => {}
        }
    }

    println!("Syntax errors: {}", syntax_errors.len());
    println!("Type errors: {}", type_errors.len());
    println!("Configuration errors: {}", config_errors.len());

    Ok(())
}

/// Example 10: Error handling with fallback strategies
pub fn fallback_strategy_example() -> StandardResult<()> {
    // Try primary method
    match primary_method() {
        Ok(result) => {
            println!("Primary method succeeded: {result:?}");
            Ok(())
        }
        Err(primary_error) => {
            println!("Primary method failed: {primary_error}");

            // Try fallback method
            match fallback_method() {
                Ok(result) => {
                    println!("Fallback method succeeded: {result:?}");
                    Ok(())
                }
                Err(fallback_error) => {
                    // Both methods failed, return combined error
                    Err(StandardError::internal_error(format!(
                        "Both primary and fallback methods failed. Primary: {primary_error}, \
                         Fallback: {fallback_error}"
                    )))
                }
            }
        }
    }
}

fn primary_method() -> StandardResult<String> {
    Err(StandardError::network_error("Primary service unavailable"))
}

fn fallback_method() -> StandardResult<String> {
    Ok("fallback_result".to_string())
}

/// Main function to run all examples
fn main() -> StandardResult<()> {
    println!("Running error handling examples...\n");

    // Run examples that don't require special setup
    println!("1. Error categorization example:");
    error_categorization_example()?;

    println!("\n2. Fallback strategy example:");
    fallback_strategy_example()?;

    println!("\n3. Custom error example:");
    custom_error_example()?;

    println!("\n4. Error reporting examples:");
    error_reporting_examples();

    println!("\n5. Rich context example:");
    rich_context_example()?;

    println!("\n6. Multiple errors example:");
    multiple_errors_example()?;

    println!("\nAll examples completed successfully!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_error_example() {
        let result = basic_error_example();
        assert!(result.is_err());

        if let Err(StandardError::Deserialization(_)) = result {
            // Expected error type
        } else {
            panic!("Expected deserialization error");
        }
    }

    #[test]
    fn test_rich_context_example() {
        let result = rich_context_example();
        assert!(result.is_err());

        if let Err(StandardError::Validation(_)) = result {
            // Expected error type
        } else {
            panic!("Expected validation error");
        }
    }

    #[test]
    fn test_fallback_strategy() {
        let result = fallback_strategy_example();
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_async_error_example() {
        let result = async_error_example().await;
        // This might succeed or fail randomly, but should not panic
        println!("Async result: {:?}", result);
    }
}
