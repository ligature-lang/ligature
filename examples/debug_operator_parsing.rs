use ligature_ast::AstResult;
use ligature_parser::Parser;

fn test_expression(source: &str) {
    println!("\n=== Testing: '{source}' ===");

    // Test with the full parser
    let mut parser = Parser::new();
    match parser.parse_expression(source) {
        Ok(expr) => {
            println!("✓ Full parser: {:?}", expr.kind);
        }
        Err(e) => {
            println!("✗ Full parser failed: {e:?}");
        }
    }
}

fn main() -> AstResult<()> {
    println!("Testing complex operator expressions...");

    // Test basic comparison operators
    test_expression("5 < 10");
    test_expression("5 <= 10");
    test_expression("5 > 10");
    test_expression("5 >= 10");
    test_expression("5 == 10");
    test_expression("5 != 10");

    // Test mixed precedence
    test_expression("5 + 3 < 10");
    test_expression("5 * 3 <= 20");
    test_expression("10 > 5 + 2");
    test_expression("15 >= 3 * 4");

    // Test logical operators with comparisons
    test_expression("5 < 10 && 10 > 5");
    test_expression("5 <= 10 || 10 < 5");
    test_expression("5 == 5 && 10 != 5");

    // Test complex nested expressions
    test_expression("(5 + 3) * 2 <= 20");
    test_expression("10 > (5 + 2) * 2");
    test_expression("5 + 3 < 10 && 10 > 5 + 2");

    // Test multiple operators in sequence
    test_expression("5 < 10 < 15");
    test_expression("5 <= 10 <= 15");
    test_expression("5 == 5 == true");

    Ok(())
}
