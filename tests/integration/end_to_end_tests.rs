//! End-to-end integration tests.
//! 
//! These tests verify that the complete pipeline from parsing
//! through type checking to evaluation works correctly.

use crate::integration::{parse_type_check_and_evaluate, create_test_environment};
use ligature_parser::parse_program;
use ligature_eval::{evaluate_program, Value};
use ligature_types::type_check_program;
use ligature_ast::AstResult;

#[test]
fn test_basic_arithmetic_pipeline() -> AstResult<()> {
    let source = "
        let x = 5;
        let y = 3;
        let result = x + y;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(8)));
    
    Ok(())
}

#[test]
fn test_function_definition_and_application() -> AstResult<()> {
    let source = "
        let add = \\x y -> x + y;
        let result = add 5 3;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(8)));
    
    Ok(())
}

#[test]
fn test_conditional_logic() -> AstResult<()> {
    let source = "
        let max = \\a b -> if a > b then a else b;
        let result = max 10 5;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(10)));
    
    let source = "
        let max = \\a b -> if a > b then a else b;
        let result = max 3 7;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(7)));
    
    Ok(())
}

#[test]
fn test_record_construction_and_access() -> AstResult<()> {
    let source = "
        let user = { name = \"Alice\", age = 30 };
        let greeting = \"Hello, \" ++ user.name;
        greeting
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::String(s) if s == "Hello, Alice"));
    
    Ok(())
}

#[test]
fn test_list_operations() -> AstResult<()> {
    let source = "
        let numbers = [1, 2, 3, 4, 5];
        let sum = 0; // Placeholder for list sum
        sum
    ";
    
    // This test will need to be updated when list operations are implemented
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(0)));
    
    Ok(())
}

#[test]
fn test_nested_function_calls() -> AstResult<()> {
    let source = "
        let add = \\x y -> x + y;
        let multiply = \\x y -> x * y;
        let result = add (multiply 2 3) 4;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(10)));
    
    Ok(())
}

#[test]
fn test_let_expressions() -> AstResult<()> {
    let source = "
        let result = let x = 5 in let y = 3 in x + y;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(8)));
    
    Ok(())
}

#[test]
fn test_pattern_matching() -> AstResult<()> {
    let source = "
        let classify = \\x -> match x {
            1 => \"one\",
            2 => \"two\",
            _ => \"other\"
        };
        let result = classify 2;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::String(s) if s == "two"));
    
    let source = "
        let classify = \\x -> match x {
            1 => \"one\",
            2 => \"two\",
            _ => \"other\"
        };
        let result = classify 5;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::String(s) if s == "other"));
    
    Ok(())
}

#[test]
fn test_complex_configuration_example() -> AstResult<()> {
    let source = "
        // Server configuration
        let server_config = {
            host = \"localhost\",
            port = 8080,
            timeout = 30,
            ssl = true
        };
        
        // Validation function
        let validate_port = \\port -> if port > 0 && port < 65536 then true else false;
        
        // Validate configuration
        let is_valid = validate_port server_config.port;
        is_valid
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Boolean(true)));
    
    Ok(())
}

#[test]
fn test_recursive_function() -> AstResult<()> {
    let source = "
        let factorial = \\n -> if n <= 1 then 1 else n * (factorial (n - 1));
        let result = factorial 5;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(120)));
    
    Ok(())
}

#[test]
fn test_multiple_bindings() -> AstResult<()> {
    let source = "
        let x = 1;
        let y = 2;
        let z = 3;
        let sum = x + y + z;
        sum
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(6)));
    
    Ok(())
}

#[test]
fn test_string_concatenation() -> AstResult<()> {
    let source = "
        let first = \"Hello\";
        let second = \"World\";
        let greeting = first ++ \", \" ++ second ++ \"!\";
        greeting
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::String(s) if s == "Hello, World!"));
    
    Ok(())
}

#[test]
fn test_boolean_logic() -> AstResult<()> {
    let source = "
        let a = true;
        let b = false;
        let result = a && !b;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Boolean(true)));
    
    Ok(())
}

#[test]
fn test_comparison_operations() -> AstResult<()> {
    let source = "
        let x = 5;
        let y = 3;
        let z = 7;
        let result = x > y && y < z;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Boolean(true)));
    
    Ok(())
}

#[test]
fn test_error_propagation() {
    // Test that errors in parsing propagate correctly
    assert!(parse_type_check_and_evaluate("let x = 1 + \"hello\";").is_err());
    
    // Test that errors in type checking propagate correctly
    assert!(parse_type_check_and_evaluate("let x = undefined_var;").is_err());
    
    // Test that errors in evaluation propagate correctly
    assert!(parse_type_check_and_evaluate("let x = 1 / 0;").is_err());
}

#[test]
fn test_whitespace_and_comments() -> AstResult<()> {
    let source = "
        // This is a comment
        let x = 42; // Inline comment
        /* Block comment
           spanning multiple lines */
        let y = 10;
        let result = x + y;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(52)));
    
    Ok(())
}

#[test]
fn test_type_annotations() -> AstResult<()> {
    let source = "
        let x: Integer = 42;
        let y: String = \"hello\";
        let add: Integer -> Integer -> Integer = \\a b -> a + b;
        let result = add x 8;
        result
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::Integer(50)));
    
    Ok(())
}

#[test]
fn test_complex_nested_expressions() -> AstResult<()> {
    let source = "
        let process = \\config -> {
            let validated = if config.port > 0 then true else false;
            let result = if validated then \"valid\" else \"invalid\";
            result
        };
        let config = { port = 8080 };
        let status = process config;
        status
    ";
    
    let value = parse_type_check_and_evaluate(source)?;
    assert!(matches!(value, Value::String(s) if s == "valid"));
    
    Ok(())
} 