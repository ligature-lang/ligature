use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();

    // Test simple modulo operation
    let source = "let x = 10 % 2;";
    println!("Testing: {source}");

    // Parse the expression directly to see the structure
    match parser.parse_expression(source) {
        Ok(expr) => {
            println!("Expression: {expr:?}");
            // Try to parse as program to see the full structure
            match parser.parse_program(source) {
                Ok(program) => println!("Program: {program:?}"),
                Err(e) => println!("Program parse error: {e:?}"),
            }
        }
        Err(e) => println!("Expression parse error: {e:?}"),
    }

    // Test with parentheses to see if that helps
    let source2 = "let x = (10 % 2);";
    println!("Testing with parentheses: {source2}");
    match parser.parse_program(source2) {
        Ok(program) => println!("Program with parentheses: {program:?}"),
        Err(e) => println!("Error: {e:?}"),
    }

    Ok(())
}
