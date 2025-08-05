//! Parser integration tests.
//! 
//! These tests verify that the parser correctly handles various
//! language constructs and produces the expected AST.

use ligature_parser::{parse_program, parse_expression, parse_type};
use ligature_ast::{Expr, Type, AstResult};

#[test]
fn test_parse_literals() -> AstResult<()> {
    // Integer literals
    let expr = parse_expression("42")?;
    assert!(matches!(expr, Expr::Integer(42)));
    
    let expr = parse_expression("-123")?;
    assert!(matches!(expr, Expr::Integer(-123)));
    
    // Float literals
    let expr = parse_expression("3.14")?;
    assert!(matches!(expr, Expr::Float(f) if (f - 3.14).abs() < f64::EPSILON));
    
    // String literals
    let expr = parse_expression("\"hello world\"")?;
    assert!(matches!(expr, Expr::String(s) if s == "hello world"));
    
    // Boolean literals
    let expr = parse_expression("true")?;
    assert!(matches!(expr, Expr::Boolean(true)));
    
    let expr = parse_expression("false")?;
    assert!(matches!(expr, Expr::Boolean(false)));
    
    // Unit literal
    let expr = parse_expression("()")?;
    assert!(matches!(expr, Expr::Unit));
    
    Ok(())
}

#[test]
fn test_parse_variable_bindings() -> AstResult<()> {
    let program = parse_program("let x = 42;")?;
    assert_eq!(program.bindings.len(), 1);
    
    let program = parse_program("let answer: Integer = 42;")?;
    assert_eq!(program.bindings.len(), 1);
    
    let program = parse_program("
        let x = 1;
        let y = 2;
        let z = 3;
    ")?;
    assert_eq!(program.bindings.len(), 3);
    
    Ok(())
}

#[test]
fn test_parse_record_construction() -> AstResult<()> {
    let expr = parse_expression("{ name = \"Alice\", age = 30 }")?;
    assert!(matches!(expr, Expr::Record(_)));
    
    let expr = parse_expression("user.name")?;
    assert!(matches!(expr, Expr::FieldAccess { .. }));
    
    Ok(())
}

#[test]
fn test_parse_function_definitions() -> AstResult<()> {
    let expr = parse_expression("\\x y -> x + y")?;
    assert!(matches!(expr, Expr::Lambda { .. }));
    
    let expr = parse_expression("add 5 3")?;
    assert!(matches!(expr, Expr::Application { .. }));
    
    Ok(())
}

#[test]
fn test_parse_let_expressions() -> AstResult<()> {
    let expr = parse_expression("let x = 5 in x * 2")?;
    assert!(matches!(expr, Expr::Let { .. }));
    
    Ok(())
}

#[test]
fn test_parse_if_expressions() -> AstResult<()> {
    let expr = parse_expression("if x > 0 then x else 0")?;
    assert!(matches!(expr, Expr::If { .. }));
    
    Ok(())
}

#[test]
fn test_parse_binary_operations() -> AstResult<()> {
    let expr = parse_expression("1 + 2")?;
    assert!(matches!(expr, Expr::BinaryOp { .. }));
    
    let expr = parse_expression("a * b")?;
    assert!(matches!(expr, Expr::BinaryOp { .. }));
    
    let expr = parse_expression("x > y")?;
    assert!(matches!(expr, Expr::BinaryOp { .. }));
    
    let expr = parse_expression("true && false")?;
    assert!(matches!(expr, Expr::BinaryOp { .. }));
    
    Ok(())
}

#[test]
fn test_parse_unary_operations() -> AstResult<()> {
    let expr = parse_expression("-5")?;
    assert!(matches!(expr, Expr::UnaryOp { .. }));
    
    let expr = parse_expression("!true")?;
    assert!(matches!(expr, Expr::UnaryOp { .. }));
    
    Ok(())
}

#[test]
fn test_parse_lists() -> AstResult<()> {
    let expr = parse_expression("[1, 2, 3]")?;
    assert!(matches!(expr, Expr::List(_)));
    
    let expr = parse_expression("[]")?;
    assert!(matches!(expr, Expr::List(_)));
    
    Ok(())
}

#[test]
fn test_parse_pattern_matching() -> AstResult<()> {
    let expr = parse_expression("match x { 1 => \"one\", _ => \"other\" }")?;
    assert!(matches!(expr, Expr::Match { .. }));
    
    Ok(())
}

#[test]
fn test_parse_types() -> AstResult<()> {
    let ty = parse_type("Integer")?;
    assert!(matches!(ty, Type::Integer));
    
    let ty = parse_type("String")?;
    assert!(matches!(ty, Type::String));
    
    let ty = parse_type("Boolean")?;
    assert!(matches!(ty, Type::Boolean));
    
    let ty = parse_type("Unit")?;
    assert!(matches!(ty, Type::Unit));
    
    let ty = parse_type("Integer -> String")?;
    assert!(matches!(ty, Type::Function { .. }));
    
    let ty = parse_type("[Integer]")?;
    assert!(matches!(ty, Type::List(_)));
    
    Ok(())
}

#[test]
fn test_parse_comments() -> AstResult<()> {
    let program = parse_program("
        // This is a comment
        let x = 42; // Inline comment
        /* Block comment
           spanning multiple lines */
        let y = 10;
    ")?;
    assert_eq!(program.bindings.len(), 2);
    
    Ok(())
}

#[test]
fn test_parse_complex_expressions() -> AstResult<()> {
    let expr = parse_expression("add (multiply 2 3) 4")?;
    assert!(matches!(expr, Expr::Application { .. }));
    
    let expr = parse_expression("if x > 0 then add x 1 else 0")?;
    assert!(matches!(expr, Expr::If { .. }));
    
    let expr = parse_expression("let x = 5 in let y = 10 in x + y")?;
    assert!(matches!(expr, Expr::Let { .. }));
    
    Ok(())
}

#[test]
fn test_parse_error_handling() {
    // Invalid syntax should return an error
    assert!(parse_expression("let x =").is_err());
    assert!(parse_expression("if then else").is_err());
    assert!(parse_expression("\\x ->").is_err());
    assert!(parse_expression("{ name = }").is_err());
}

#[test]
fn test_parse_whitespace_handling() -> AstResult<()> {
    // Should handle various whitespace patterns
    let expr1 = parse_expression("42")?;
    let expr2 = parse_expression("  42  ")?;
    assert!(matches!(expr1, Expr::Integer(42)));
    assert!(matches!(expr2, Expr::Integer(42)));
    
    let expr1 = parse_expression("1+2")?;
    let expr2 = parse_expression("1 + 2")?;
    assert!(matches!(expr1, Expr::BinaryOp { .. }));
    assert!(matches!(expr2, Expr::BinaryOp { .. }));
    
    Ok(())
} 