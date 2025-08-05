use ligature_parser::Parser;

fn main() {
    let mut parser = Parser::new();
    
    // Test simple expressions first
    println!("Testing simple expression:");
    match parser.parse_expression("5 * 2") {
        Ok(expr) => println!("✓ Parsed: {:?}", expr),
        Err(e) => println!("✗ Error: {:?}", e),
    }
    
    println!("\nTesting let expression:");
    match parser.parse_expression("let x = 5 in x * 2") {
        Ok(expr) => println!("✓ Parsed: {:?}", expr),
        Err(e) => println!("✗ Error: {:?}", e),
    }
    
    println!("\nTesting simple let expression:");
    match parser.parse_expression("let x = 5 in x") {
        Ok(expr) => println!("✓ Parsed: {:?}", expr),
        Err(e) => println!("✗ Error: {:?}", e),
    }
} 