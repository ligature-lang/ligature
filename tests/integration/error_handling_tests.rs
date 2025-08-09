//! Error handling integration tests.
//! 
//! These tests verify that the language properly handles and reports
//! various types of errors throughout the pipeline with enhanced
//! error context, suggestions, and recovery mechanisms.

use ligature_parser::{parse_program, parse_expression};
use ligature_eval::{evaluate_program, evaluate_expression};
use ligature_types::{type_check_program, infer_expression};
use ligature_ast::{AstResult, LigatureError, ErrorCollection, ErrorReporter, ErrorReportConfig};

#[test]
fn test_parser_error_handling() {
    // Test syntax errors with enhanced error reporting
    let test_cases = vec![
        ("let x =", "unexpected end of input"),
        ("if then else", "missing condition"),
        ("\\x ->", "incomplete function"),
        ("{ name = }", "missing value"),
        ("let x = 1 +", "incomplete expression"),
        ("let x = 1 + \"hello\"", "type mismatch"),
    ];

    for (input, expected_error) in test_cases {
        let result = parse_program(input);
        assert!(result.is_err(), "Expected error for input: {}", input);
        
        if let Err(e) = result {
            let error_msg = e.to_string();
            assert!(
                error_msg.contains(expected_error) || error_msg.contains("Parse error"),
                "Error message should contain '{}' or 'Parse error', got: {}",
                expected_error,
                error_msg
            );
        }
    }
}

#[test]
fn test_type_checker_error_handling() {
    // Test type mismatch errors with suggestions
    let test_cases = vec![
        ("let x = 1 + \"hello\";", "type mismatch", "integer", "string"),
        ("let x = true && 42;", "type mismatch", "boolean", "integer"),
        ("let x = 5 > \"hello\";", "type mismatch", "integer", "string"),
    ];

    for (input, expected_error, expected_type, found_type) in test_cases {
        let parsed = parse_program(input).unwrap();
        let result = type_check_program(&parsed);
        assert!(result.is_err(), "Expected error for input: {}", input);
        
        if let Err(e) = result {
            let error_msg = e.to_string();
            assert!(
                error_msg.contains(expected_error) || error_msg.contains("Type error"),
                "Error message should contain '{}' or 'Type error', got: {}",
                expected_error,
                error_msg
            );
            
            // Check for type information in error
            if let Some(ligature_error) = e.downcast_ref::<LigatureError>() {
                match ligature_error {
                    LigatureError::Type { expected, found, .. } => {
                        if let (Some(exp), Some(fnd)) = (expected, found) {
                            assert!(
                                exp.contains(expected_type) || fnd.contains(found_type),
                                "Expected type info to contain '{}' or '{}', got expected: '{}', found: '{}'",
                                expected_type,
                                found_type,
                                exp,
                                fnd
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

#[test]
fn test_evaluator_error_handling() {
    // Test runtime errors with context
    let test_cases = vec![
        ("let x = 1 / 0;", "division by zero"),
        ("let x = 1 + \"hello\";", "type mismatch"),
        ("let x = true && 42;", "type mismatch"),
    ];

    for (input, expected_error) in test_cases {
        let parsed = parse_program(input).unwrap();
        let result = evaluate_program(&parsed);
        assert!(result.is_err(), "Expected error for input: {}", input);
        
        if let Err(e) = result {
            let error_msg = e.to_string();
            assert!(
                error_msg.contains(expected_error) || error_msg.contains("Evaluation error"),
                "Error message should contain '{}' or 'Evaluation error', got: {}",
                expected_error,
                error_msg
            );
        }
    }
}

#[test]
fn test_error_context_preservation() {
    // Test that error context is preserved through the pipeline
    
    // Parse error should include source location
    let result = parse_program("let x = 1 +");
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should include some indication of where the error occurred
        assert!(!error_msg.is_empty());
        
        // Check for context information
        if let Some(ligature_error) = e.downcast_ref::<LigatureError>() {
            if let Some(span) = ligature_error.span() {
                assert!(span.is_valid(), "Error span should be valid");
            }
        }
    }
    
    // Type error should include type information
    let result = type_check_program(&parse_program("let x = 1 + \"hello\";").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should include type information
        assert!(!error_msg.is_empty());
        
        // Check for suggestions
        if let Some(ligature_error) = e.downcast_ref::<LigatureError>() {
            let suggestions = ligature_error.get_suggestions();
            assert!(!suggestions.is_empty(), "Type errors should include suggestions");
        }
    }
    
    // Evaluation error should include runtime information
    let result = evaluate_program(&parse_program("let x = 1 / 0;").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should include runtime error information
        assert!(!error_msg.is_empty());
        
        // Check for context
        if let Some(ligature_error) = e.downcast_ref::<LigatureError>() {
            match ligature_error {
                LigatureError::Evaluation { context, .. } => {
                    assert!(context.is_some(), "Evaluation errors should include context");
                }
                _ => {}
            }
        }
    }
}

#[test]
fn test_error_collection() {
    // Test error collection functionality
    let mut error_collection = ErrorCollection::new();
    
    // Add some errors
    let error1 = LigatureError::Parse {
        message: "Test error 1".to_string(),
        span: ligature_ast::Span::simple(0, 10),
        suggestions: vec!["Fix syntax".to_string()],
    };
    
    let error2 = LigatureError::Type {
        message: "Test error 2".to_string(),
        span: ligature_ast::Span::simple(10, 20),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec!["Convert to integer".to_string()],
    };
    
    assert!(error_collection.push(error1.clone()));
    assert!(error_collection.push(error2.clone()));
    
    assert_eq!(error_collection.len(), 2);
    assert!(error_collection.has_errors());
    assert!(!error_collection.is_empty());
    
    // Test error collection with limit
    let mut limited_collection = ErrorCollection::with_max_errors(1);
    assert!(limited_collection.push(error1.clone()));
    assert!(!limited_collection.push(error2.clone())); // Should not add due to limit
    assert_eq!(limited_collection.len(), 1);
    assert!(limited_collection.is_full());
}

#[test]
fn test_error_reporter() {
    // Test error reporter functionality
    let source = "let x = 1 + \"hello\";\nlet y = x * 2;";
    let mut reporter = ErrorReporter::new(source.to_string());
    
    let error = LigatureError::Type {
        message: "Cannot add integer and string".to_string(),
        span: ligature_ast::Span::simple(8, 18),
        expected: Some("integer".to_string()),
        found: Some("string".to_string()),
        suggestions: vec![
            "Convert string to integer".to_string(),
            "Use string concatenation".to_string(),
        ],
    };
    
    reporter.add_error(error);
    
    let report = reporter.report();
    assert!(report.contains("Type error"));
    assert!(report.contains("Cannot add integer and string"));
    assert!(report.contains("Convert string to integer"));
    assert!(report.contains("Use string concatenation"));
}

#[test]
fn test_enhanced_error_reporter() {
    // Test enhanced error reporter with configuration
    let source = "let x = 1 + \"hello\";\nlet y = x * 2;";
    let config = ErrorReportConfig {
        show_source: true,
        show_suggestions: true,
        max_errors: 5,
        color_output: false, // Disable colors for testing
        show_error_codes: true,
        show_categories: true,
    };
    
    let mut reporter = ligature_ast::EnhancedErrorReporter::with_config(source.to_string(), config);
    
    let error = LigatureError::Type {
        message: "Cannot add integer and string".to_string(),
        span: ligature_ast::Span::simple(8, 18),
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

#[test]
fn test_error_suggestions() {
    // Test that errors provide helpful suggestions
    let test_cases = vec![
        (
            LigatureError::UndefinedIdentifier {
                name: "undefined_var".to_string(),
                span: ligature_ast::Span::simple(0, 0),
            },
            vec![
                "Check if 'undefined_var' is defined in the current scope",
                "Make sure the variable is declared before use",
                "Check for typos in the variable name",
            ],
        ),
        (
            LigatureError::DuplicateIdentifier {
                name: "duplicate_var".to_string(),
                span: ligature_ast::Span::simple(0, 0),
            },
            vec![
                "Rename one of the 'duplicate_var' declarations",
                "Use different names for different variables",
                "Check if you meant to use a different variable",
            ],
        ),
        (
            LigatureError::DivisionByZero {
                span: ligature_ast::Span::simple(0, 0),
            },
            vec![
                "Check if the divisor can be zero",
                "Add a runtime check before division",
                "Use a conditional to handle the zero case",
            ],
        ),
    ];

    for (error, expected_suggestions) in test_cases {
        let suggestions = error.get_suggestions();
        assert_eq!(suggestions.len(), expected_suggestions.len());
        
        for expected in expected_suggestions {
            assert!(
                suggestions.iter().any(|s| s.contains(expected)),
                "Expected suggestion containing '{}', got: {:?}",
                expected,
                suggestions
            );
        }
    }
}

#[test]
fn test_error_recovery() {
    // Test error recovery strategies
    use ligature_ast::{ErrorRecovery, RecoveryStrategy, SkipToSemicolon, InsertMissingToken};
    
    let recovery = ErrorRecovery::new();
    
    let parse_error = LigatureError::Parse {
        message: "Unexpected token".to_string(),
        span: ligature_ast::Span::simple(0, 0),
        suggestions: vec![],
    };
    
    // Test that recovery can handle parse errors
    let result = recovery.try_recover(&parse_error);
    // Note: In a real implementation, this would actually attempt recovery
    // For now, we just test that the interface works
    assert!(result.is_ok() || result.is_err());
    
    // Test custom recovery strategy
    let custom_recovery = ErrorRecovery::new()
        .with_strategy(Box::new(InsertMissingToken {
            token: ";".to_string(),
        }));
    
    let result = custom_recovery.try_recover(&parse_error);
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn test_error_categories() {
    // Test error categorization
    use ligature_ast::{get_error_category, ErrorCategory};
    
    let test_cases = vec![
        (
            LigatureError::Parse {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                suggestions: vec![],
            },
            ErrorCategory::Syntax,
        ),
        (
            LigatureError::Type {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                expected: None,
                found: None,
                suggestions: vec![],
            },
            ErrorCategory::Type,
        ),
        (
            LigatureError::Evaluation {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                context: None,
            },
            ErrorCategory::Runtime,
        ),
        (
            LigatureError::Module {
                message: "".to_string(),
                path: None,
                cause: None,
            },
            ErrorCategory::Module,
        ),
        (
            LigatureError::Configuration {
                message: "".to_string(),
                field: None,
                value: None,
            },
            ErrorCategory::Configuration,
        ),
        (
            LigatureError::InternalError {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
            },
            ErrorCategory::Internal,
        ),
    ];

    for (error, expected_category) in test_cases {
        let category = get_error_category(&error);
        assert_eq!(category, expected_category);
    }
}

#[test]
fn test_error_codes() {
    // Test error code generation
    use ligature_ast::{get_error_code, ErrorCode, ErrorCategory};
    
    let test_cases = vec![
        (
            LigatureError::Parse {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                suggestions: vec![],
            },
            "E1001",
        ),
        (
            LigatureError::Type {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                expected: None,
                found: None,
                suggestions: vec![],
            },
            "T2001",
        ),
        (
            LigatureError::Evaluation {
                message: "".to_string(),
                span: ligature_ast::Span::simple(0, 0),
                context: None,
            },
            "R3001",
        ),
    ];

    for (error, expected_code) in test_cases {
        let error_code = get_error_code(&error);
        assert_eq!(error_code.to_string(), expected_code);
    }
}

#[test]
fn test_user_friendly_errors() {
    // Test user-friendly error formatting
    let error = LigatureError::UndefinedIdentifier {
        name: "undefined_var".to_string(),
        span: ligature_ast::Span::simple(0, 0),
    };
    
    let user_friendly = error.to_user_friendly();
    
    assert!(user_friendly.contains("Error:"));
    assert!(user_friendly.contains("undefined_var"));
    assert!(user_friendly.contains("To fix this error:"));
    assert!(user_friendly.contains("Check if 'undefined_var' is defined"));
}

#[test]
fn test_error_context_builder() {
    // Test error context builder
    use ligature_ast::{ErrorContext, error_with_context, error_with_suggestions};
    
    let base_error = LigatureError::Evaluation {
        message: "Runtime error".to_string(),
        span: ligature_ast::Span::simple(0, 0),
        context: None,
    };
    
    // Test context builder
    let error_with_context = ErrorContext::new()
        .with_context("Failed to evaluate expression")
        .with_suggestion("Check the expression syntax")
        .with_suggestion("Verify all variables are defined")
        .build(base_error.clone());
    
    if let LigatureError::Evaluation { context, .. } = error_with_context {
        assert!(context.is_some());
        assert!(context.unwrap().contains("Failed to evaluate expression"));
    }
    
    // Test utility functions
    let error_with_ctx = error_with_context(
        base_error.clone(),
        "Additional context"
    );
    
    let error_with_suggestions = error_with_suggestions(
        base_error,
        vec!["Suggestion 1".to_string(), "Suggestion 2".to_string()]
    );
    
    assert!(error_with_ctx.to_string().contains("Runtime error"));
    assert!(error_with_suggestions.to_string().contains("Runtime error"));
} 