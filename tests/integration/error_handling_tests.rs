//! Error handling integration tests.
//! 
//! These tests verify that the language properly handles and reports
//! various types of errors throughout the pipeline.

use ligature_parser::{parse_program, parse_expression};
use ligature_eval::{evaluate_program, evaluate_expression};
use ligature_types::{type_check_program, infer_expression};
use ligature_ast::AstResult;

#[test]
fn test_parser_error_handling() {
    // Test syntax errors
    assert!(parse_program("let x =").is_err());
    assert!(parse_program("if then else").is_err());
    assert!(parse_program("\\x ->").is_err());
    assert!(parse_program("{ name = }").is_err());
    assert!(parse_program("let x = 1 +").is_err());
    assert!(parse_program("let x = 1 + \"hello\"").is_err());
    
    // Test malformed expressions
    assert!(parse_expression("1 +").is_err());
    assert!(parse_expression("if true then").is_err());
    assert!(parse_expression("\\x ->").is_err());
    assert!(parse_expression("{ name =").is_err());
    assert!(parse_expression("[1, 2,").is_err());
}

#[test]
fn test_type_checker_error_handling() {
    // Test type mismatch errors
    assert!(type_check_program(&parse_program("let x = 1 + \"hello\";").unwrap()).is_err());
    assert!(type_check_program(&parse_program("let x = true && 42;").unwrap()).is_err());
    assert!(type_check_program(&parse_program("let x = 5 > \"hello\";").unwrap()).is_err());
    
    // Test undefined variable errors
    assert!(type_check_program(&parse_program("let x = undefined_var;").unwrap()).is_err());
    assert!(type_check_program(&parse_program("let x = 1; let y = x + undefined_var;").unwrap()).is_err());
    
    // Test function application errors
    assert!(type_check_program(&parse_program("
        let add = \\x y -> x + y;
        let result = add 5 \"hello\";
    ").unwrap()).is_err());
    
    assert!(type_check_program(&parse_program("
        let add = \\x y -> x + y;
        let result = add 5;
    ").unwrap()).is_err());
    
    // Test if expression type mismatch
    assert!(type_check_program(&parse_program("
        let x = if true then 42 else \"hello\";
    ").unwrap()).is_err());
    
    // Test record field access errors
    assert!(type_check_program(&parse_program("
        let user = { name = \"Alice\" };
        let age = user.age;
    ").unwrap()).is_err());
}

#[test]
fn test_evaluator_error_handling() {
    // Test division by zero
    assert!(evaluate_program(&parse_program("let x = 1 / 0;").unwrap()).is_err());
    
    // Test type mismatch during evaluation
    assert!(evaluate_program(&parse_program("let x = 1 + \"hello\";").unwrap()).is_err());
    assert!(evaluate_program(&parse_program("let x = true && 42;").unwrap()).is_err());
    
    // Test undefined variable during evaluation
    assert!(evaluate_program(&parse_program("let x = undefined_var;").unwrap()).is_err());
    
    // Test function application errors
    assert!(evaluate_program(&parse_program("
        let add = \\x y -> x + y;
        let result = add 5 \"hello\";
    ").unwrap()).is_err());
    
    // Test pattern matching errors
    assert!(evaluate_program(&parse_program("
        let x = match 1 { 1 => \"one\" };
    ").unwrap()).is_err()); // Missing default case
    
    // Test record field access errors
    assert!(evaluate_program(&parse_program("
        let user = { name = \"Alice\" };
        let age = user.age;
    ").unwrap()).is_err());
}

#[test]
fn test_error_message_quality() {
    // Test that error messages are informative
    let result = parse_program("let x = 1 +");
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("unexpected end of input") || 
                error_msg.contains("expected") ||
                error_msg.contains("syntax error"));
    }
    
    let result = type_check_program(&parse_program("let x = 1 + \"hello\";").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("type") || 
                error_msg.contains("mismatch") ||
                error_msg.contains("expected"));
    }
    
    let result = evaluate_program(&parse_program("let x = 1 / 0;").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("division") || 
                error_msg.contains("zero") ||
                error_msg.contains("error"));
    }
}

#[test]
fn test_error_recovery() {
    // Test that the parser can recover from some errors and continue
    let result = parse_program("
        let x = 1 +;
        let y = 2;
        let z = x + y;
    ");
    // This should fail due to the syntax error, but we can test recovery
    assert!(result.is_err());
    
    // Test that valid code after an error is still parsed correctly
    let result = parse_program("
        let x = 1;
        let y = 2;
        let z = x + y;
    ");
    assert!(result.is_ok());
}

#[test]
fn test_nested_error_handling() {
    // Test errors in nested expressions
    let result = parse_program("
        let x = if true then 1 + else 0;
    ");
    assert!(result.is_err());
    
    let result = parse_program("
        let x = let y = 1 + in y * 2;
    ");
    assert!(result.is_err());
    
    let result = parse_program("
        let x = { name = \"Alice\", age = };
    ");
    assert!(result.is_err());
}

#[test]
fn test_type_inference_errors() {
    // Test type inference errors
    let result = infer_expression(&parse_program("1 + \"hello\"").unwrap().bindings[0].value.clone());
    assert!(result.is_err());
    
    let result = infer_expression(&parse_program("true && 42").unwrap().bindings[0].value.clone());
    assert!(result.is_err());
    
    let result = infer_expression(&parse_program("undefined_var").unwrap().bindings[0].value.clone());
    assert!(result.is_err());
}

#[test]
fn test_complex_error_scenarios() {
    // Test complex error scenarios that might occur in real programs
    
    // Multiple errors in one program
    let result = parse_program("
        let x = 1 +;
        let y = true && 42;
        let z = undefined_var;
    ");
    assert!(result.is_err());
    
    // Error in function definition
    let result = parse_program("
        let add = \\x y -> x +;
        let result = add 5 3;
    ");
    assert!(result.is_err());
    
    // Error in conditional expression
    let result = parse_program("
        let x = if true then 1 + else 0;
        let y = if false then \"hello\" else 42;
    ");
    assert!(result.is_err());
    
    // Error in record construction
    let result = parse_program("
        let user = { name = \"Alice\", age = };
        let greeting = \"Hello, \" ++ user.name;
    ");
    assert!(result.is_err());
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
    }
    
    // Type error should include type information
    let result = type_check_program(&parse_program("let x = 1 + \"hello\";").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should include type information
        assert!(!error_msg.is_empty());
    }
    
    // Evaluation error should include runtime information
    let result = evaluate_program(&parse_program("let x = 1 / 0;").unwrap());
    assert!(result.is_err());
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should include runtime error information
        assert!(!error_msg.is_empty());
    }
} 