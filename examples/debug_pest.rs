use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();

    // Test simple expression to see what pest produces
    let source = "5 <= 10";
    println!("Testing: {}", source);

    // Try to parse as expression
    match parser.parse_expression(source) {
        Ok(expr) => {
            println!("Expression parsed successfully: {:?}", expr);
        }
        Err(e) => {
            println!("Expression parse error: {:?}", e);

            // Try to parse as program
            match parser.parse_program(&format!("let x = {};", source)) {
                Ok(program) => println!("Program parsed successfully: {:?}", program),
                Err(e2) => println!("Program parse error: {:?}", e2),
            }
        }
    }

    Ok(())
}
