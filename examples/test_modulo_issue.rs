use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();

    // Test simple modulo operation
    let source = "let x = 10 % 2;";
    println!("Testing: {source}");
    match parser.parse_program(source) {
        Ok(program) => println!("Success: {program:?}"),
        Err(e) => println!("Error: {e:?}"),
    }

    // Test modulo in comparison
    let source2 = "let x = 10 % 2 == 0;";
    println!("Testing: {source2}");
    match parser.parse_program(source2) {
        Ok(program) => println!("Success: {program:?}"),
        Err(e) => println!("Error: {e:?}"),
    }

    // Test modulo in pattern guard
    let source3 = r#"
        let result = match 10 {
            x when x % 2 == 0 => "even",
            _ => "odd"
        };
    "#;
    println!("Testing pattern guard with modulo...");
    match parser.parse_program(source3) {
        Ok(program) => println!("Success: {program:?}"),
        Err(e) => println!("Error: {e:?}"),
    }

    Ok(())
}
