use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    println!("Testing match expression parsing...");

    let mut parser = Parser::new();

    // Test 1: Simple match expression with wildcard pattern
    println!("\n=== Test 1: Simple Match Expression ===");
    let simple_match = r#"
        let x = match 5 {
            _ => 0
        };
    "#;

    match parser.parse_program(simple_match) {
        Ok(program) => {
            println!("✓ Simple match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Simple match expression failed: {:?}", e);
        }
    }

    // Test 2: Match expression with union patterns
    println!("\n=== Test 2: Union Pattern Match Expression ===");
    let union_match = r#"
        let x = match Some(42) {
            Some => 0,
            None => 1
        };
    "#;

    match parser.parse_program(union_match) {
        Ok(program) => {
            println!("✓ Union pattern match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Union pattern match expression failed: {:?}", e);
        }
    }

    // Test 3: Match expression with variable binding
    println!("\n=== Test 3: Variable Binding Match Expression ===");
    let binding_match = r#"
        let x = match Some(42) {
            Some(n) => n,
            None => 0
        };
    "#;

    match parser.parse_program(binding_match) {
        Ok(program) => {
            println!("✓ Variable binding match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Variable binding match expression failed: {:?}", e);
        }
    }

    // Test 4: Match expression with literal patterns
    println!("\n=== Test 4: Literal Pattern Match Expression ===");
    let literal_match = r#"
        let x = match 42 {
            0 => "zero",
            42 => "forty-two",
            _ => "other"
        };
    "#;

    match parser.parse_program(literal_match) {
        Ok(program) => {
            println!("✓ Literal pattern match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Literal pattern match expression failed: {:?}", e);
        }
    }

    // Test 5: Match expression with record patterns
    println!("\n=== Test 5: Record Pattern Match Expression ===");
    let record_match = r#"
        let x = match { name = "Alice", age = 30 } {
            { name = n, age = a } => n,
            _ => "unknown"
        };
    "#;

    match parser.parse_program(record_match) {
        Ok(program) => {
            println!("✓ Record pattern match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Record pattern match expression failed: {:?}", e);
        }
    }

    // Test 6: Match expression with list patterns
    println!("\n=== Test 6: List Pattern Match Expression ===");
    let list_match = r#"
        let x = match [1, 2, 3] {
            [first, second, third] => first + second + third,
            [first, second] => first + second,
            _ => 0
        };
    "#;

    match parser.parse_program(list_match) {
        Ok(program) => {
            println!("✓ List pattern match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ List pattern match expression failed: {:?}", e);
        }
    }

    // Test 7: Nested match expressions
    println!("\n=== Test 7: Nested Match Expression ===");
    let nested_match = r#"
        let x = match Some(Some(42)) {
            Some(Some(n)) => n,
            Some(None) => 0,
            None => -1
        };
    "#;

    match parser.parse_program(nested_match) {
        Ok(program) => {
            println!("✓ Nested match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Nested match expression failed: {:?}", e);
        }
    }

    // Test 8: Complex match expression with multiple patterns
    println!("\n=== Test 8: Complex Match Expression ===");
    let complex_match = r#"
        let process_result = \result -> match result {
            { status = Success(code), data = Some(content) } => content,
            { status = Error(msg), data = None } => "error: " ++ msg,
            { status = Loading, data = _ } => "loading...",
            _ => "unknown"
        };
    "#;

    match parser.parse_program(complex_match) {
        Ok(program) => {
            println!("✓ Complex match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Complex match expression failed: {:?}", e);
        }
    }

    // Test 9: Match expression with function calls
    println!("\n=== Test 9: Match Expression with Function Calls ===");
    let func_match = r#"
        let x = match get_value() {
            Some(n) => process(n),
            None => default_value()
        };
    "#;

    match parser.parse_program(func_match) {
        Ok(program) => {
            println!("✓ Function call match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Function call match expression failed: {:?}", e);
        }
    }

    // Test 10: Match expression with if expressions in cases
    println!("\n=== Test 10: Match Expression with If Cases ===");
    let if_match = r#"
        let x = match value {
            Some(n) => if n > 0 then "positive" else "negative",
            None => "none"
        };
    "#;

    match parser.parse_program(if_match) {
        Ok(program) => {
            println!("✓ If case match expression parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ If case match expression failed: {:?}", e);
        }
    }

    println!("\n✓ Match expression parsing tests completed!");
    Ok(())
}
