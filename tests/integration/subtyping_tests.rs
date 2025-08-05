//! Subtyping integration tests.
//! 
//! These tests verify that the enhanced subtyping implementation works correctly
//! for records, unions, functions, and lists with proper width and depth subtyping.

use ligature_parser::parse_program;
use ligature_types::{type_check_program, infer_expression};
use ligature_ast::AstResult;

#[test]
fn test_record_subtyping() {
    // Test width subtyping: supertype has more fields than subtype
    let program = parse_program(r#"
        let user = { name = "Alice", age = 30, email = "alice@example.com" };
        let basic_user: { name: String, age: Integer } = user;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test depth subtyping: field types are in subtype relationship
    let program = parse_program(r#"
        let user = { name = "Alice", age = 30 };
        let flexible_user: { name: String, age: Float } = user;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test subtyping failure: missing required field
    let program = parse_program(r#"
        let user = { name = "Alice" };
        let full_user: { name: String, age: Integer } = user;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_err());
}

#[test]
fn test_union_subtyping() {
    // Test width subtyping: supertype has more variants than subtype
    let program = parse_program(r#"
        type Result = Success String | Error String | Pending;
        let result: Success String | Error String = Success "ok";
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test depth subtyping: variant types are in subtype relationship
    let program = parse_program(r#"
        type Number = Int Integer | Float Float;
        let number: Int Integer | Float Float = Int 42;
        let flexible_number: Int Integer | Float Float = number;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test subtyping failure: missing required variant
    let program = parse_program(r#"
        type Result = Success String | Error String;
        let result: Success String | Error String | Pending = Success "ok";
    "#).unwrap();
    
    assert!(type_check_program(&program).is_err());
}

#[test]
fn test_function_subtyping() {
    // Test contravariant parameter subtyping and covariant return subtyping
    let program = parse_program(r#"
        let add_int = \x y -> x + y;
        let add_number: Integer -> Integer -> Integer = add_int;
        let flexible_add: Float -> Float -> Float = add_number;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test function subtyping with different parameter types
    let program = parse_program(r#"
        let process_int = \x -> x * 2;
        let process_number: Float -> Float = process_int;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());
}

#[test]
fn test_list_subtyping() {
    // Test list subtyping with element type subtyping
    let program = parse_program(r#"
        let int_list = [1, 2, 3];
        let number_list: [Float] = int_list;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test nested list subtyping
    let program = parse_program(r#"
        let int_matrix = [[1, 2], [3, 4]];
        let number_matrix: [[Float]] = int_matrix;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());
}

#[test]
fn test_complex_subtyping_scenarios() {
    // Test complex nested subtyping
    let program = parse_program(r#"
        let user = { 
            name = "Alice", 
            age = 30, 
            preferences = { theme = "dark", notifications = true }
        };
        let basic_user: { 
            name: String, 
            age: Float, 
            preferences: { theme: String } 
        } = user;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test function with record parameters
    let program = parse_program(r#"
        let process_user = \user -> user.name;
        let flexible_process: { name: String, age: Float } -> String = process_user;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());
}

#[test]
fn test_subtyping_error_messages() {
    // Test that subtyping errors provide helpful messages
    let program = parse_program(r#"
        let user = { name = "Alice" };
        let full_user: { name: String, age: Integer } = user;
    "#).unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("missing required field") || 
                error_msg.contains("subtyping failed"));
    }
}

#[test]
fn test_type_inference_with_subtyping() {
    // Test that type inference works correctly with subtyping
    let program = parse_program(r#"
        let add = \x y -> x + y;
        let result = add 5 3;
        let float_result: Float = result;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());

    // Test polymorphic functions with subtyping
    let program = parse_program(r#"
        let id = \x -> x;
        let int_id: Integer -> Integer = id;
        let float_id: Float -> Float = id;
    "#).unwrap();
    
    assert!(type_check_program(&program).is_ok());
} 