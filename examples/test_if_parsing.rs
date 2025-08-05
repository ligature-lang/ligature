use ligature_ast::ExprKind;
use ligature_parser::Parser;

fn main() {
    let mut parser = Parser::new();

    // Test if expression parsing
    let result = parser.parse_expression("if x > 0 then x else 0");
    match result {
        Ok(expr) => {
            println!("Successfully parsed: {expr:?}");
            match expr.kind {
                ExprKind::If { .. } => println!("Correctly parsed as If expression"),
                _ => println!("Parsed as wrong type: {:?}", expr.kind),
            }
        }
        Err(e) => {
            println!("Failed to parse if expression: {e:?}");

            // Let's try to parse it as a program to see what happens
            let program_result = parser.parse_program("if x > 0 then x else 0");
            match program_result {
                Ok(program) => println!("Parsed as program: {program:?}"),
                Err(e2) => println!("Also failed as program: {e2:?}"),
            }

            // Let's try a simpler expression first
            let simple_result = parser.parse_expression("x > 0");
            match simple_result {
                Ok(expr) => println!("Simple expression parsed: {expr:?}"),
                Err(e3) => println!("Simple expression failed: {e3:?}"),
            }
        }
    }
}
