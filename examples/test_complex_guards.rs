use ligature_ast::AstResult;
use ligature_eval::Evaluator;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();

    println!("Testing complex pattern guard expressions...");

    // Test 1: Multiple arithmetic operations in guard
    let source1 = r#"
        let result = match 15 {
            x when x % 3 == 0 && x % 5 == 0 => "divisible by both 3 and 5",
            x when x % 3 == 0 => "divisible by 3",
            x when x % 5 == 0 => "divisible by 5",
            _ => "not divisible by 3 or 5"
        };
    "#;

    println!("Test 1: Multiple arithmetic operations");
    match parser.parse_program(source1) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Multiple arithmetic operations test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 2: Nested function calls in guard
    let source2 = r#"
        let is_even = \x -> x % 2 == 0;
        let is_positive = \x -> x > 0;
        let result = match 8 {
            x when is_even(x) && is_positive(x) => "positive even",
            x when is_even(x) && !is_positive(x) => "negative even",
            x when !is_even(x) && is_positive(x) => "positive odd",
            _ => "negative odd"
        };
    "#;

    println!("Test 2: Nested function calls");
    match parser.parse_program(source2) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Nested function calls test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 3: Complex boolean logic in guard
    let source3 = r#"
        let result = match 7 {
            x when x > 10 && x < 20 => "between 10 and 20",
            x when x > 0 && x <= 10 => "between 1 and 10",
            x when x == 0 => "zero",
            x when x < 0 => "negative",
            _ => "other"
        };
    "#;

    println!("Test 3: Complex boolean logic");
    match parser.parse_program(source3) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Complex boolean logic test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 4: String operations in guard
    let source4 = r#"
        let result = match "hello world" {
            s when s == "hello" => "greeting",
            s when s == "goodbye" => "farewell",
            s when s == "" => "empty",
            s when s == "hello world" => "full greeting",
            _ => "other string"
        };
    "#;

    println!("Test 4: String operations");
    match parser.parse_program(source4) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ String operations test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 5: Record pattern matching with complex guards
    let source5 = r#"
        let result = match { name = "Alice", age = 25, city = "New York" } {
            { name = n, age = a, city = c } when a >= 18 && c == "New York" => "adult in NYC",
            { name = n, age = a, city = c } when a >= 18 && c != "New York" => "adult elsewhere",
            { name = n, age = a, city = c } when a < 18 => "minor",
            _ => "unknown"
        };
    "#;

    println!("Test 5: Record pattern with complex guards");
    match parser.parse_program(source5) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Record pattern with complex guards test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 6: List pattern matching with arithmetic
    let source6 = r#"
        let result = match [1, 2, 3, 4] {
            [x, y, z, w] when x + y + z + w > 10 => "sum greater than 10",
            [x, y, z, w] when x + y + z + w == 10 => "sum equals 10",
            [x, y, z, w] when x + y + z + w < 10 => "sum less than 10",
            _ => "other list"
        };
    "#;

    println!("Test 6: List pattern with arithmetic");
    match parser.parse_program(source6) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ List pattern with arithmetic test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 7: Union pattern with nested conditions
    let source7 = r#"
        type Option = Some(Integer) | None;
        let result = match Some(15) {
            Some(x) when x > 10 && x < 20 => "between 10 and 20",
            Some(x) when x > 0 && x <= 10 => "between 1 and 10",
            Some(x) when x <= 0 => "non-positive",
            None => "no value",
            _ => "other"
        };
    "#;

    println!("Test 7: Union pattern with nested conditions");
    match parser.parse_program(source7) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Union pattern with nested conditions test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 8: Multiple guards with different patterns
    let source8 = r#"
        let result = match 42 {
            x when x > 100 => "very large",
            x when x > 50 => "large",
            x when x > 25 => "medium",
            x when x > 10 => "small",
            x when x > 0 => "tiny",
            x when x == 0 => "zero",
            _ => "negative"
        };
    "#;

    println!("Test 8: Multiple guards with different patterns");
    match parser.parse_program(source8) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Multiple guards test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 9: Complex nested expressions
    let source9 = r#"
        let result = match 12 {
            x when (x % 2 == 0) && (x % 3 == 0) && (x > 10) => "even, divisible by 3, and > 10",
            x when (x % 2 == 0) && (x % 3 == 0) => "even and divisible by 3",
            x when x % 2 == 0 => "even",
            x when x % 3 == 0 => "divisible by 3",
            _ => "other"
        };
    "#;

    println!("Test 9: Complex nested expressions");
    match parser.parse_program(source9) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Complex nested expressions test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 10: Guard with field access
    let source10 = r#"
        let result = match { value = 15, flag = true } {
            { value = v, flag = f } when v > 10 && f => "high value with flag",
            { value = v, flag = f } when v > 10 && !f => "high value without flag",
            { value = v, flag = f } when v <= 10 && f => "low value with flag",
            _ => "low value without flag"
        };
    "#;

    println!("Test 10: Guard with field access");
    match parser.parse_program(source10) {
        Ok(program) => {
            evaluator.evaluate_program(&program)?;
            println!("✓ Guard with field access test passed");
        }
        Err(e) => println!("✗ Error: {:?}", e),
    }

    println!("All complex guard expression tests completed!");
    Ok(())
}
