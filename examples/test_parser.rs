use ligature_parser::parse_expression;

fn main() {
    let result = parse_expression("let x = 5 in x * 2");
    match result {
        Ok(expr) => println!("Successfully parsed: {expr:?}"),
        Err(e) => println!("Parse error: {e:?}"),
    }
} 