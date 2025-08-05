use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    println!("Testing simple union pattern parsing...");

    let mut parser = Parser::new();

    // Test 1: Simple union pattern without binding
    println!("\n=== Test 1: Simple Union Pattern ===");
    let simple_union = r#"
        let x = match Some(42) {
            Some => 0
        };
    "#;

    match parser.parse_program(simple_union) {
        Ok(program) => {
            println!("✓ Simple union pattern parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Simple union pattern failed: {:?}", e);
        }
    }

    // Test 2: Union pattern with variable binding
    println!("\n=== Test 2: Union Pattern with Variable Binding ===");
    let binding_union = r#"
        let x = match Some(42) {
            Some(n) => n
        };
    "#;

    match parser.parse_program(binding_union) {
        Ok(program) => {
            println!("✓ Union pattern with binding parsed successfully");
            println!("  AST: {:?}", program);
        }
        Err(e) => {
            println!("✗ Union pattern with binding failed: {:?}", e);
        }
    }

    // Test 3: Parse just the pattern to see what's happening
    println!("\n=== Test 3: Parse Individual Patterns ===");

    // Test parsing "Some" as a pattern
    match parser.parse_expression("Some") {
        Ok(expr) => {
            println!("✓ 'Some' parsed as expression: {:?}", expr);
        }
        Err(e) => {
            println!("✗ 'Some' failed to parse as expression: {:?}", e);
        }
    }

    // Test parsing "Some(n)" as a pattern
    match parser.parse_expression("Some(n)") {
        Ok(expr) => {
            println!("✓ 'Some(n)' parsed as expression: {:?}", expr);
        }
        Err(e) => {
            println!("✗ 'Some(n)' failed to parse as expression: {:?}", e);
        }
    }

    println!("\n✓ Simple union pattern tests completed!");
    Ok(())
}
