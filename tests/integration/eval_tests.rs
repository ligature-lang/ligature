//! Evaluation integration tests.
//! 
//! These tests verify that the evaluation engine correctly
//! evaluates various language constructs and produces expected values.

use ligature_eval::{evaluate_program, evaluate_expression, Environment, Value};
use ligature_parser::parse_program;
use ligature_ast::AstResult;

#[test]
fn test_evaluate_literals() -> AstResult<()> {
    let mut env = Environment::new();
    
    // Integer literals
    let value = evaluate_expression(&parse_program("42")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(42)));
    
    // Float literals
    let value = evaluate_expression(&parse_program("3.14")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Float(f) if (f - 3.14).abs() < f64::EPSILON));
    
    // String literals
    let value = evaluate_expression(&parse_program("\"hello\"")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::String(s) if s == "hello"));
    
    // Boolean literals
    let value = evaluate_expression(&parse_program("true")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    // Unit literal
    let value = evaluate_expression(&parse_program("()")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Unit));
    
    Ok(())
}

#[test]
fn test_evaluate_arithmetic_operations() -> AstResult<()> {
    let mut env = Environment::new();
    
    // Addition
    let value = evaluate_expression(&parse_program("1 + 2")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(3)));
    
    // Subtraction
    let value = evaluate_expression(&parse_program("5 - 3")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(2)));
    
    // Multiplication
    let value = evaluate_expression(&parse_program("4 * 3")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(12)));
    
    // Division
    let value = evaluate_expression(&parse_program("10 / 2")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(5)));
    
    // Complex arithmetic
    let value = evaluate_expression(&parse_program("(2 + 3) * 4")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Integer(20)));
    
    Ok(())
}

#[test]
fn test_evaluate_comparison_operations() -> AstResult<()> {
    let mut env = Environment::new();
    
    // Greater than
    let value = evaluate_expression(&parse_program("5 > 3")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    let value = evaluate_expression(&parse_program("3 > 5")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(false)));
    
    // Less than
    let value = evaluate_expression(&parse_program("3 < 5")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    // Equal
    let value = evaluate_expression(&parse_program("5 == 5")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    let value = evaluate_expression(&parse_program("5 == 3")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(false)));
    
    Ok(())
}

#[test]
fn test_evaluate_logical_operations() -> AstResult<()> {
    let mut env = Environment::new();
    
    // AND
    let value = evaluate_expression(&parse_program("true && true")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    let value = evaluate_expression(&parse_program("true && false")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(false)));
    
    // OR
    let value = evaluate_expression(&parse_program("true || false")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    let value = evaluate_expression(&parse_program("false || false")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(false)));
    
    // NOT
    let value = evaluate_expression(&parse_program("!true")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(false)));
    
    let value = evaluate_expression(&parse_program("!false")?.bindings[0].value.clone())?;
    assert!(matches!(value, Value::Boolean(true)));
    
    Ok(())
}

#[test]
fn test_evaluate_variable_bindings() -> AstResult<()> {
    let program = parse_program("
        let x = 42;
        let y = 10;
        let z = x + y;
    ")?;
    
    let result = evaluate_program(&program)?;
    // The result should be the value of the last binding
    assert!(matches!(result, Value::Integer(52)));
    
    Ok(())
}

#[test]
fn test_evaluate_let_expressions() -> AstResult<()> {
    let expr = parse_program("let x = 5 in x * 2")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Integer(10)));
    
    let expr = parse_program("let x = 3 in let y = 4 in x + y")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Integer(7)));
    
    Ok(())
}

#[test]
fn test_evaluate_if_expressions() -> AstResult<()> {
    let expr = parse_program("if true then 42 else 0")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Integer(42)));
    
    let expr = parse_program("if false then 42 else 0")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Integer(0)));
    
    let expr = parse_program("if 5 > 3 then \"yes\" else \"no\"")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::String(s) if s == "yes"));
    
    Ok(())
}

#[test]
fn test_evaluate_record_construction() -> AstResult<()> {
    let expr = parse_program("{ name = \"Alice\", age = 30 }")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Record(_)));
    
    // Test field access
    let program = parse_program("
        let user = { name = \"Alice\", age = 30 };
        user.name
    ")?;
    let value = evaluate_program(&program)?;
    assert!(matches!(value, Value::String(s) if s == "Alice"));
    
    Ok(())
}

#[test]
fn test_evaluate_list_construction() -> AstResult<()> {
    let expr = parse_program("[1, 2, 3]")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::List(_)));
    
    let expr = parse_program("[]")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::List(list) if list.is_empty()));
    
    Ok(())
}

#[test]
fn test_evaluate_list_literals_with_optimization() -> AstResult<()> {
    // Test list literals with various element types
    let test_cases = vec![
        ("[1, 2, 3]", "integer list"),
        ("[\"a\", \"b\", \"c\"]", "string list"),
        ("[true, false, true]", "boolean list"),
        ("[1.5, 2.5, 3.5]", "float list"),
        ("[1, \"hello\", true]", "mixed list"),
        ("[[1, 2], [3, 4]]", "nested list"),
    ];
    
    for (source, description) in test_cases {
        let expr = parse_program(source)?.bindings[0].value.clone();
        let value = evaluate_expression(&expr)?;
        assert!(matches!(value, Value::List(_)), "Failed for {}: {}", description, source);
    }
    
    // Test empty list
    let expr = parse_program("[]")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::List(list) if list.is_empty()));
    
    // Test list with expressions
    let expr = parse_program("[1 + 2, 3 * 4, 10 - 5]")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::List(_)));
    
    Ok(())
}

#[test]
fn test_evaluate_function_application() -> AstResult<()> {
    // Test with built-in functions
    let mut env = Environment::new();
    env.bind("add", Value::Function(Box::new(|args| {
        if args.len() != 2 {
            return Err(ligature_ast::AstError::new("add expects 2 arguments"));
        }
        match (&args[0], &args[1]) {
            (Value::Integer(a), Value::Integer(b)) => Ok(Value::Integer(a + b)),
            _ => Err(ligature_ast::AstError::new("add expects integer arguments"))
        }
    })));
    
    // Test function application
    let expr = parse_program("add 5 3")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Integer(8)));
    
    Ok(())
}

#[test]
fn test_evaluate_lambda_expressions() -> AstResult<()> {
    let expr = parse_program("\\x -> x + 1")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::Closure { .. }));
    
    // Test lambda application
    let program = parse_program("
        let add_one = \\x -> x + 1;
        add_one 5
    ")?;
    let value = evaluate_program(&program)?;
    assert!(matches!(value, Value::Integer(6)));
    
    Ok(())
}

#[test]
fn test_evaluate_pattern_matching() -> AstResult<()> {
    let expr = parse_program("match 1 { 1 => \"one\", _ => \"other\" }")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::String(s) if s == "one"));
    
    let expr = parse_program("match 2 { 1 => \"one\", _ => \"other\" }")?.bindings[0].value.clone();
    let value = evaluate_expression(&expr)?;
    assert!(matches!(value, Value::String(s) if s == "other"));
    
    Ok(())
}

#[test]
fn test_evaluate_complex_expressions() -> AstResult<()> {
    let program = parse_program("
        let x = 5;
        let y = 10;
        let result = if x > y then x else y;
        result * 2
    ")?;
    let value = evaluate_program(&program)?;
    assert!(matches!(value, Value::Integer(20)));
    
    let program = parse_program("
        let add = \\x y -> x + y;
        let multiply = \\x y -> x * y;
        let result = add (multiply 2 3) 4;
        result
    ")?;
    let value = evaluate_program(&program)?;
    assert!(matches!(value, Value::Integer(10)));
    
    Ok(())
}

#[test]
fn test_evaluate_error_handling() {
    // Division by zero
    assert!(evaluate_expression(&parse_program("1 / 0").unwrap().bindings[0].value.clone()).is_err());
    
    // Type mismatch
    assert!(evaluate_expression(&parse_program("1 + \"hello\"").unwrap().bindings[0].value.clone()).is_err());
    
    // Undefined variable
    assert!(evaluate_expression(&parse_program("undefined_var").unwrap().bindings[0].value.clone()).is_err());
}

#[test]
fn test_evaluate_termination() -> AstResult<()> {
    // Test that evaluation terminates for valid programs
    let program = parse_program("
        let factorial = \\n -> if n <= 1 then 1 else n * (factorial (n - 1));
        factorial 5
    ")?;
    
    // This should terminate and produce a result
    let value = evaluate_program(&program)?;
    assert!(matches!(value, Value::Integer(120)));
    
    Ok(())
} 