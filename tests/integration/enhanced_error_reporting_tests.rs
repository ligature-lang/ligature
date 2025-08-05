//! Enhanced error reporting integration tests.
//! 
//! These tests verify that the enhanced error reporting provides helpful
//! suggestions and context for fixing type errors.

use ligature_parser::parse_program;
use ligature_types::{type_check_program, infer_expression};
use ligature_ast::AstResult;

#[test]
fn test_type_mismatch_with_suggestions() {
    // Test arithmetic type mismatch with suggestion
    let program = parse_program(r#"
        let x = 5 + "hello";
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("type mismatch") || 
                error_msg.contains("cannot unify"));
    }

    // Test boolean operation type mismatch
    let program = parse_program(r#"
        let x = true && 42;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_record_field_error_reporting() {
    // Test missing field access with helpful error
    let program = parse_program(r#"
        let user = { name = "Alice" };
        let age = user.age;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("field") || 
                error_msg.contains("missing"));
    }

    // Test record construction with wrong field type
    let program = parse_program(r#"
        let user: { name: String, age: Integer } = { name = "Alice", age = "thirty" };
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_union_variant_error_reporting() {
    // Test pattern matching with missing variant
    let program = parse_program(r#"
        type Result = Success String | Error String;
        let result = Success "ok";
        let message = match result {
            Success msg => msg,
            Error err => err
        };
        let invalid = match result {
            Success msg => msg
        };
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());

    // Test variant construction with wrong type
    let program = parse_program(r#"
        type Number = Int Integer | Float Float;
        let number: Number = Int "not a number";
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_function_application_error_reporting() {
    // Test function application with wrong argument type
    let program = parse_program(r#"
        let add = \x y -> x + y;
        let result = add 5 "hello";
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());

    // Test function application with wrong number of arguments
    let program = parse_program(r#"
        let add = \x y -> x + y;
        let result = add 5;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_pattern_matching_error_reporting() {
    // Test incomplete pattern matching
    let program = parse_program(r#"
        let x = match 1 {
            1 => "one"
        };
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());

    // Test pattern matching with wrong type
    let program = parse_program(r#"
        let x = match "hello" {
            1 => "one",
            _ => "other"
        };
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_subtyping_error_context() {
    // Test record subtyping with detailed error context
    let program = parse_program(r#"
        let user = { name = "Alice" };
        let full_user: { name: String, age: Integer, email: String } = user;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should mention the missing fields
        assert!(error_msg.contains("missing") || 
                error_msg.contains("required field"));
    }

    // Test union subtyping with detailed error context
    let program = parse_program(r#"
        type Result = Success String | Error String;
        let result: Success String | Error String | Pending | Loading = Success "ok";
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
}

#[test]
fn test_error_recovery_and_context() {
    // Test that errors provide enough context for recovery
    let program = parse_program(r#"
        let process_user = \user -> user.name;
        let user = { name = "Alice" };
        let result = process_user user;
        let invalid = process_user 42;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should provide context about the function signature
        assert!(error_msg.contains("function") || 
                error_msg.contains("parameter") ||
                error_msg.contains("argument"));
    }
}

#[test]
fn test_nested_error_context() {
    // Test errors in nested expressions provide proper context
    let program = parse_program(r#"
        let complex = {
            user = { name = "Alice", age = "thirty" },
            settings = { theme = "dark", notifications = 42 }
        };
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should mention the nested structure
        assert!(error_msg.contains("record") || 
                error_msg.contains("field") ||
                error_msg.contains("type"));
    }
}

#[test]
fn test_type_inference_error_context() {
    // Test that type inference errors provide helpful context
    let program = parse_program(r#"
        let ambiguous = \x -> x;
        let result = ambiguous 5;
        let string_result: String = result;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        // Should mention type inference or ambiguity
        assert!(error_msg.contains("ambiguous") || 
                error_msg.contains("inference") ||
                error_msg.contains("unify"));
    }
} 