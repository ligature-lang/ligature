//! Simple test to verify the error handling system works correctly.

use ligature_ast::{ErrorCode, LigatureError, Span};
use ligature_error::{ErrorReportConfig, StandardError, StandardErrorReporter, StandardResult};

fn main() -> StandardResult<()> {
    println!("Testing error handling system...\n");

    // Test 1: Basic error creation
    println!("1. Testing basic error creation:");
    let basic_error = StandardError::validation_error("Test validation error");
    println!("   Created error: {basic_error}");
    println!("   Suggestions: {:?}", basic_error.get_suggestions());
    println!("   Recoverable: {}", basic_error.is_recoverable());
    println!();

    // Test 2: Error with context
    println!("2. Testing error with context:");
    let context_error = StandardError::configuration_error("Invalid configuration")
        .with_context("Configuration validation failed: field=database_url");
    println!("   Created error: {context_error}");
    println!();

    // Test 3: Ligature error
    println!("3. Testing Ligature error:");
    let ligature_error = StandardError::Ligature(LigatureError::UndefinedIdentifier {
        code: ErrorCode::R3004,
        name: "undefined_var".to_string(),
        span: Span::new(1, 1, 1, 15),
    });
    println!("   Created error: {ligature_error}");
    println!("   Error code: {:?}", ligature_error.error_code());
    println!("   Span: {:?}", ligature_error.span());
    println!("   Suggestions: {:?}", ligature_error.get_suggestions());
    println!();

    // Test 4: Error reporting
    println!("4. Testing error reporting:");
    let source_code = r#"
let x = 42;
let y = "hello";
let result = x + y;  // This will cause a type error
"#;

    let type_error = StandardError::Ligature(LigatureError::Type {
        code: ErrorCode::T2001,
        message: "Cannot add integer and string".to_string(),
        span: Span::new(3, 3, 1, 25),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec![
            "Convert string to integer: x + y.parse::<i32>()".to_string(),
            "Use string concatenation: format!(\"{}{}\", x, y)".to_string(),
        ],
    });

    let config = ErrorReportConfig {
        show_source: true,
        show_suggestions: true,
        show_error_codes: true,
        show_categories: true,
        color_output: false, // Disable colors for testing
        max_errors: 10,
        show_metadata: true,
        group_by_category: true,
    };

    let mut reporter =
        StandardErrorReporter::with_source_and_config(source_code.to_string(), config);
    reporter.add_error(type_error);

    println!("   Error report:");
    println!("{}", reporter.report());
    println!();

    // Test 5: Multiple errors
    println!("5. Testing multiple errors:");
    let mut multi_reporter = StandardErrorReporter::new();

    multi_reporter.add_error(StandardError::validation_error("First error"));
    multi_reporter.add_error(StandardError::configuration_error("Second error"));
    multi_reporter.add_error(StandardError::Ligature(LigatureError::Parse {
        code: ErrorCode::E1001,
        message: "Parse error".to_string(),
        span: Span::new(1, 1, 1, 10),
        suggestions: vec!["Check syntax".to_string()],
    }));

    println!("   Multiple errors report:");
    println!("{}", multi_reporter.report());
    println!();

    // Test 6: Error categorization
    println!("6. Testing error categorization:");
    let errors = vec![
        StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Syntax error".to_string(),
            span: Span::new(1, 1, 1, 10),
            suggestions: vec!["Fix syntax".to_string()],
        }),
        StandardError::Ligature(LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Type error".to_string(),
            span: Span::new(2, 2, 1, 15),
            expected: Some("string".to_string()),
            found: Some("integer".to_string()),
            suggestions: vec!["Convert types".to_string()],
        }),
        StandardError::configuration_error("Config error"),
    ];

    for (i, error) in errors.iter().enumerate() {
        println!("   Error {}: {:?}", i + 1, error);
        if let StandardError::Ligature(ligature_error) = error {
            println!("     Category: {}", ligature_error.code().category());
            println!("     Code: {}", ligature_error.code().as_str());
            println!("     Description: {}", ligature_error.code().description());
        }
    }
    println!();

    println!("All tests completed successfully!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_error_creation() {
        let error = StandardError::validation_error("Test error");
        assert!(error.to_string().contains("Test error"));
        assert!(!error.get_suggestions().is_empty());
    }

    #[test]
    fn test_ligature_error() {
        let error = StandardError::Ligature(LigatureError::UndefinedIdentifier {
            code: ErrorCode::R3004,
            name: "test_var".to_string(),
            span: Span::new(1, 1, 1, 10),
        });

        assert_eq!(error.error_code(), Some(ErrorCode::R3004));
        assert!(error.span().is_some());
        assert!(!error.get_suggestions().is_empty());
    }

    #[test]
    fn test_error_recovery() {
        let recoverable_error = StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Parse error".to_string(),
            span: Span::new(1, 1, 1, 10),
            suggestions: vec!["Fix syntax".to_string()],
        });

        assert!(recoverable_error.is_recoverable());

        let non_recoverable_error = StandardError::NotFound("File not found".to_string());
        assert!(!non_recoverable_error.is_recoverable());
    }

    #[test]
    fn test_error_context() {
        let error = StandardError::configuration_error("Config error")
            .with_context("Configuration validation failed");

        // The error should still be valid after adding context
        assert!(error.to_string().contains("Config error"));
    }
}
