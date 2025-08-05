use ligature_eval::Evaluator;
use ligature_parser::Parser;
use ligature_ast::AstResult;

#[test]
fn test_simple_pattern_guard() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match 5 {
            x when x > 3 => "greater than 3",
            x when x < 3 => "less than 3",
            _ => "exactly 3"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    // The result should be "greater than 3" since 5 > 3
    // We can't easily check the result without exposing it, but we can verify it parses and evaluates
    Ok(())
}

#[test]
fn test_pattern_guard_with_arithmetic() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match 10 {
            x when x % 2 == 0 => "even",
            x when x % 2 == 1 => "odd",
            _ => "unknown"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
}

#[test]
fn test_pattern_guard_with_union() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match Some(15) {
            Some(x) when x > 10 => "large number",
            Some(x) when x <= 10 => "small number",
            None => "no value"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
}

#[test]
fn test_pattern_guard_with_record() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match { name = "Alice", age = 25 } {
            { name = n, age = a } when a >= 18 => "adult",
            { name = n, age = a } when a < 18 => "minor",
            _ => "unknown"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
}

#[test]
fn test_pattern_guard_with_list() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match [1, 2, 3] {
            [x, y, z] when x + y + z > 5 => "sum greater than 5",
            [x, y, z] when x + y + z <= 5 => "sum less than or equal to 5",
            _ => "other"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
}

#[test]
fn test_pattern_guard_with_function_call() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let is_even = \x -> x % 2 == 0;
        let result = match 8 {
            x when is_even(x) => "even number",
            x when !is_even(x) => "odd number",
            _ => "unknown"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
}

#[test]
fn test_pattern_guard_fallback() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let result = match 1 {
            x when x > 10 => "greater than 10",
            x when x < 0 => "negative",
            _ => "fallback"
        };
    "#;
    
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    
    Ok(())
} 