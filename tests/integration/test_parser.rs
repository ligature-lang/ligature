use ligature_parser::parse_program;

fn main() {
    let result = parse_program("let x = 42;");
    match result {
        Ok(program) => println!("Successfully parsed program: {:?}", program),
        Err(e) => println!("Parse error: {:?}", e),
    }
}
