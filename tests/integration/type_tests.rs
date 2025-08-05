//! Type system integration tests.
//! 
//! These tests verify that the type system correctly
//! checks types and infers types for various language constructs.

use ligature_types::{type_check_program, infer_expression};
use ligature_parser::parse_program;
use ligature_ast::{Type, AstResult};

#[test]
fn test_type_check_literals() -> AstResult<()> {
    let program = parse_program("let x = 42;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x: Integer = 42;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x: String = \"hello\";")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x: Boolean = true;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x: Unit = ();")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_arithmetic_operations() -> AstResult<()> {
    let program = parse_program("let x = 1 + 2;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 5 * 3;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 10 / 2;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 7 - 3;")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_comparison_operations() -> AstResult<()> {
    let program = parse_program("let x = 5 > 3;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 3 < 5;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 5 == 5;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = 5 != 3;")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_logical_operations() -> AstResult<()> {
    let program = parse_program("let x = true && false;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = true || false;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = !true;")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_function_definitions() -> AstResult<()> {
    let program = parse_program("let add = \\x y -> x + y;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let add: Integer -> Integer -> Integer = \\x y -> x + y;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let greet: String -> String = \\name -> \"Hello, \" ++ name;")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_function_application() -> AstResult<()> {
    let program = parse_program("
        let add = \\x y -> x + y;
        let result = add 5 3;
    ")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let multiply = \\x y -> x * y;
        let result = multiply 4 2;
    ")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_let_expressions() -> AstResult<()> {
    let program = parse_program("let x = let y = 5 in y * 2;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = let y = 3 in let z = 4 in y + z;")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_if_expressions() -> AstResult<()> {
    let program = parse_program("let x = if true then 42 else 0;")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = if 5 > 3 then \"yes\" else \"no\";")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_record_construction() -> AstResult<()> {
    let program = parse_program("let user = { name = \"Alice\", age = 30 };")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let user = { name = \"Alice\", age = 30 };
        let name = user.name;
    ")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_list_construction() -> AstResult<()> {
    let program = parse_program("let numbers = [1, 2, 3];")?;
    type_check_program(&program)?;
    
    let program = parse_program("let strings = [\"a\", \"b\", \"c\"];")?;
    type_check_program(&program)?;
    
    let program = parse_program("let empty = [];")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_pattern_matching() -> AstResult<()> {
    let program = parse_program("let x = match 1 { 1 => \"one\", _ => \"other\" };")?;
    type_check_program(&program)?;
    
    let program = parse_program("let x = match true { true => 1, false => 0 };")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_inference() -> AstResult<()> {
    // Test type inference for literals
    let expr = parse_program("42")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Integer));
    
    let expr = parse_program("\"hello\"")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::String));
    
    let expr = parse_program("true")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Boolean));
    
    let expr = parse_program("()")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Unit));
    
    // Test type inference for operations
    let expr = parse_program("1 + 2")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Integer));
    
    let expr = parse_program("true && false")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Boolean));
    
    // Test type inference for functions
    let expr = parse_program("\\x -> x + 1")?.bindings[0].value.clone();
    let ty = infer_expression(&expr)?;
    assert!(matches!(ty, Type::Function { .. }));
    
    Ok(())
}

#[test]
fn test_type_check_error_handling() {
    // Type mismatch in arithmetic
    assert!(type_check_program(&parse_program("let x = 1 + \"hello\";").unwrap()).is_err());
    
    // Type mismatch in comparison
    assert!(type_check_program(&parse_program("let x = 5 > \"hello\";").unwrap()).is_err());
    
    // Type mismatch in logical operations
    assert!(type_check_program(&parse_program("let x = true && 42;").unwrap()).is_err());
    
    // Type mismatch in if expression
    assert!(type_check_program(&parse_program("let x = if true then 42 else \"hello\";").unwrap()).is_err());
    
    // Type mismatch in function application
    assert!(type_check_program(&parse_program("
        let add = \\x y -> x + y;
        let result = add 5 \"hello\";
    ").unwrap()).is_err());
    
    // Undefined variable
    assert!(type_check_program(&parse_program("let x = undefined_var;").unwrap()).is_err());
}

#[test]
fn test_type_check_complex_programs() -> AstResult<()> {
    let program = parse_program("
        let add = \\x y -> x + y;
        let multiply = \\x y -> x * y;
        let result = add (multiply 2 3) 4;
        result
    ")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let max = \\a b -> if a > b then a else b;
        let result = max 5 3;
        result
    ")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let user = { name = \"Alice\", age = 30 };
        let greet = \\user -> \"Hello, \" ++ user.name;
        let message = greet user;
        message
    ")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_generic_functions() -> AstResult<()> {
    // Test that polymorphic functions work correctly
    let program = parse_program("
        let id = \\x -> x;
        let result1 = id 42;
        let result2 = id \"hello\";
        result2
    ")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let const = \\x y -> x;
        let result1 = const 42 \"hello\";
        let result2 = const \"hello\" 42;
        result2
    ")?;
    type_check_program(&program)?;
    
    Ok(())
}

#[test]
fn test_type_check_recursive_functions() -> AstResult<()> {
    let program = parse_program("
        let factorial = \\n -> if n <= 1 then 1 else n * (factorial (n - 1));
        let result = factorial 5;
        result
    ")?;
    type_check_program(&program)?;
    
    let program = parse_program("
        let length = \\list -> match list {
            [] => 0,
            [head, ...tail] => 1 + (length tail)
        };
        let result = length [1, 2, 3];
        result
    ")?;
    type_check_program(&program)?;
    
    Ok(())
} 