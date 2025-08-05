use ligature_ast::ExprKind;
use ligature_parser::parse_expression;

fn main() {
    println!("Testing Ligature Operator Precedence Issues\n");

    let test_cases = vec![
        ("2 + 3 * 4", "Should be 2 + (3 * 4) = 14"),
        ("-5 + 3", "Should be (-5) + 3 = -2"),
        (
            "true && false || true",
            "Should be (true && false) || true = true",
        ),
        ("5 + 3 > 7", "Should be (5 + 3) > 7 = true"),
        ("--5", "Should be -(-5) = 5"),
    ];

    for (expression, expected) in test_cases {
        println!("Testing: {}", expression);
        println!("Expected: {}", expected);

        match parse_expression(expression) {
            Ok(expr) => {
                println!("✓ Parsed successfully");
                println!("  AST: {:?}", expr.kind);
                println!();
            }
            Err(e) => {
                println!("✗ Parse error: {}", e);
                println!();
            }
        }
    }

    println!("Precedence Analysis Complete");
}
