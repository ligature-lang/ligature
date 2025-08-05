use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();

    println!("Testing operator parsing issues...");

    // Test 1: Simple <= operator
    let source1 = "let x = 5 <= 10;";
    println!("Test 1: Simple <= operator");
    match parser.parse_program(source1) {
        Ok(program) => println!("✓ Simple <= operator test passed"),
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 2: <= in comparison
    let source2 = "let x = 5 <= 10 && 10 > 5;";
    println!("Test 2: <= in comparison");
    match parser.parse_program(source2) {
        Ok(program) => println!("✓ <= in comparison test passed"),
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 3: <= in pattern guard
    let source3 = r#"
        let result = match 7 {
            x when x <= 10 => "small",
            _ => "large"
        };
    "#;
    println!("Test 3: <= in pattern guard");
    match parser.parse_program(source3) {
        Ok(program) => println!("✓ <= in pattern guard test passed"),
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 4: Complex <= expression
    let source4 = r#"
        let result = match 7 {
            x when x > 0 && x <= 10 => "between 1 and 10",
            _ => "other"
        };
    "#;
    println!("Test 4: Complex <= expression");
    match parser.parse_program(source4) {
        Ok(program) => println!("✓ Complex <= expression test passed"),
        Err(e) => println!("✗ Error: {:?}", e),
    }

    // Test 5: Multiple <= operators
    let source5 = r#"
        let result = match 15 {
            x when x >= 10 && x <= 20 => "between 10 and 20",
            _ => "outside range"
        };
    "#;
    println!("Test 5: Multiple <= operators");
    match parser.parse_program(source5) {
        Ok(program) => println!("✓ Multiple <= operators test passed"),
        Err(e) => println!("✗ Error: {:?}", e),
    }

    Ok(())
}
