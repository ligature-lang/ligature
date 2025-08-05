use ligature_ast::AstResult;
use ligature_eval::Evaluator;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();

    // Test simple pattern guard
    let source = r#"
        let result = match 5 {
            x when x > 3 => "greater than 3",
            x when x < 3 => "less than 3",
            _ => "exactly 3"
        };
    "#;

    println!("Testing pattern guards...");
    let program = parser.parse_program(source)?;
    evaluator.evaluate_program(&program)?;
    println!("Pattern guards test passed!");

    Ok(())
}
