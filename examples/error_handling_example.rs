//! Example demonstrating the new standardized error handling system.

use ligature_ast::{ErrorCode, LigatureError, Span};
use ligature_error::{
    ErrorReportConfig, StandardError, StandardErrorReporter, StandardResult,
    config_error_with_context, error_context, eval_error_with_context, module_error_with_context,
    parse_error_with_context, type_error_with_context,
};

/// Example function that demonstrates various error handling patterns.
fn demonstrate_error_handling() -> StandardResult<()> {
    println!("=== Ligature Error Handling Example ===\n");

    // 1. Basic error creation
    println!("1. Basic Error Creation:");
    let basic_error = StandardError::configuration_error("Invalid configuration format");
    println!("   Error: {}\n", basic_error);

    // 2. Error with context
    println!("2. Error with Context:");
    let context_error = StandardError::validation_error("Invalid input")
        .with_context("Failed to validate user input")
        .with_context("Processing configuration file");
    println!("   Error: {}\n", context_error);

    // 3. Using error context builder
    println!("3. Error Context Builder:");
    let rich_error = error_context!(
        "Failed to parse configuration",
        "Invalid syntax at line 10",
        "Missing closing brace"
    )
    .suggestion("Add the missing closing brace")
    .suggestion("Check the syntax around line 10")
    .metadata("file", "config.lig")
    .metadata("line", "10")
    .span(Span::simple(10, 15))
    .build_parse_error("Unexpected token");

    println!("   Error: {}", rich_error);
    println!("   Suggestions: {:?}", rich_error.get_suggestions());
    println!("   Error Code: {}\n", rich_error.code().as_str());

    // 4. Using error macros
    println!("4. Error Macros:");
    let parse_error = parse_error_with_context!(
        "Unexpected token",
        "Failed to parse expression",
        "Invalid operator"
    );
    println!("   Parse Error: {}", parse_error);

    let type_error = type_error_with_context!(
        "Type mismatch",
        "integer",
        "string",
        "In function call",
        "Parameter validation"
    );
    println!("   Type Error: {}", type_error);

    let eval_error = eval_error_with_context!(
        "Division by zero",
        "Runtime evaluation",
        "Mathematical operation"
    );
    println!("   Eval Error: {}", eval_error);

    let module_error = module_error_with_context!(
        "Module not found",
        "utils.lig",
        "Import resolution",
        "File system lookup"
    );
    println!("   Module Error: {}", module_error);

    let config_error = config_error_with_context!(
        "Invalid field value",
        "timeout",
        "invalid_value",
        "Configuration validation",
        "Field parsing"
    );
    println!("   Config Error: {}\n", config_error);

    // 5. Error reporter demonstration
    println!("5. Error Reporter:");
    let source_code = r#"
let x = 1 + "hello";
let y = x * 2;
let z = y / 0;
"#;

    let mut reporter = StandardErrorReporter::with_source_and_config(
        source_code.to_string(),
        ErrorReportConfig {
            show_source: true,
            show_suggestions: true,
            show_error_codes: true,
            show_categories: true,
            color_output: false, // Disable colors for example
            max_errors: 5,
            show_metadata: false,
            group_by_category: true,
        },
    );

    // Add various types of errors
    reporter.add_error(StandardError::Ligature(LigatureError::Type {
        code: ErrorCode::T2001,
        message: "Cannot add integer and string".to_string(),
        span: Span::simple(2, 10),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec![
            "Convert string to integer".to_string(),
            "Use string concatenation".to_string(),
        ],
    }));

    reporter.add_error(StandardError::Ligature(LigatureError::Evaluation {
        code: ErrorCode::R3002,
        message: "Division by zero".to_string(),
        span: Span::simple(4, 10),
        context: Some("Mathematical operation".to_string()),
    }));

    reporter.add_error(StandardError::Ligature(LigatureError::Parse {
        code: ErrorCode::E1001,
        message: "Unexpected token".to_string(),
        span: Span::simple(1, 5),
        suggestions: vec![
            "Check the syntax".to_string(),
            "Verify all tokens are valid".to_string(),
        ],
    }));

    println!("{}", reporter.report());

    // 6. Error recovery demonstration
    println!("6. Error Recovery:");
    let recoverable_errors = vec![
        StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Parse error".to_string(),
            span: Span::simple(1, 1),
            suggestions: vec![],
        }),
        StandardError::validation_error("Validation error"),
        StandardError::configuration_error("Configuration error"),
    ];

    for error in recoverable_errors {
        println!("   Error: {}", error);
        println!("   Recoverable: {}", error.is_recoverable());
        println!("   Suggestions: {:?}", error.get_suggestions());
        println!();
    }

    // 7. Result extension methods
    println!("7. Result Extension Methods:");

    // Simulate a function that returns a result
    let result: Result<String, std::io::Error> = Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "File not found",
    ));

    let enhanced_result = result
        .with_context("Failed to read configuration file")
        .with_context("Processing user input");

    match enhanced_result {
        Ok(_) => println!("   Success!"),
        Err(e) => println!("   Enhanced Error: {}\n", e),
    }

    Ok(())
}

/// Example function demonstrating error handling in a real-world scenario.
fn process_configuration_file(filename: &str) -> StandardResult<()> {
    // Simulate reading a configuration file
    let source = std::fs::read_to_string(filename)
        .map_err(|e| StandardError::io_error(e, "Failed to read configuration file"))?;

    // Simulate parsing the configuration
    if source.contains("invalid") {
        return Err(parse_error_with_context!(
            "Invalid configuration syntax",
            "File parsing",
            "Configuration validation"
        )
        .into());
    }

    // Simulate type checking
    if source.contains("type_mismatch") {
        return Err(type_error_with_context!(
            "Type mismatch in configuration",
            "ConfigValue",
            "String",
            "Configuration validation"
        )
        .into());
    }

    // Simulate validation
    if source.contains("invalid_value") {
        return Err(
            StandardError::validation_error("Invalid configuration value")
                .with_context("Configuration validation")
                .with_context("User input processing"),
        );
    }

    println!("Configuration processed successfully!");
    Ok(())
}

fn main() -> StandardResult<()> {
    // Run the demonstration
    demonstrate_error_handling()?;

    // Demonstrate real-world error handling
    println!("=== Real-world Error Handling Example ===\n");

    // This will fail because the file doesn't exist
    match process_configuration_file("nonexistent.lig") {
        Ok(_) => println!("Success!"),
        Err(e) => {
            let mut reporter = StandardErrorReporter::new();
            reporter.add_error(e);
            println!("{}", reporter.report());
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let error = StandardError::configuration_error("Test error");
        assert!(error.to_string().contains("Test error"));
    }

    #[test]
    fn test_error_with_context() {
        let error = StandardError::validation_error("Test error")
            .with_context("Context 1")
            .with_context("Context 2");

        assert!(
            error
                .to_string()
                .contains("Context 1: Context 2: Test error")
        );
    }

    #[test]
    fn test_error_macros() {
        let parse_error = parse_error_with_context!("Test parse error", "Context");
        assert_eq!(parse_error.code(), ErrorCode::E1001);

        let type_error =
            type_error_with_context!("Test type error", "expected", "found", "Context");
        assert_eq!(type_error.code(), ErrorCode::T2001);
    }

    #[test]
    fn test_error_reporter() {
        let mut reporter = StandardErrorReporter::new();
        let error = StandardError::internal_error("Test error");
        reporter.add_error(error);

        let report = reporter.report();
        assert!(report.contains("Test error"));
        assert!(report.contains("Internal Errors"));
    }
}
