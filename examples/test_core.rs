use embouchure_checker::type_check_program;
use ligature_ast::*;
use ligature_eval::evaluate_program;

fn main() {
    // Create a simple program: let x = 5; let y = x * 2;
    let program = Program {
        declarations: vec![
            Declaration::value(
                "x".to_string(),
                None,
                Expr {
                    kind: ExprKind::Literal(Literal::Integer(5)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
            Declaration::value(
                "y".to_string(),
                None,
                Expr {
                    kind: ExprKind::BinaryOp {
                        operator: BinaryOperator::Multiply,
                        left: Box::new(Expr {
                            kind: ExprKind::Variable("x".to_string()),
                            span: Span::default(),
                        }),
                        right: Box::new(Expr {
                            kind: ExprKind::Literal(Literal::Integer(2)),
                            span: Span::default(),
                        }),
                    },
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
        ],
    };

    // Test type checking
    match type_check_program(&program) {
        Ok(()) => println!("✓ Type checking passed"),
        Err(e) => println!("✗ Type checking failed: {e}"),
    }

    // Test evaluation
    match evaluate_program(&program) {
        Ok(result) => println!("✓ Evaluation succeeded: {result:?}"),
        Err(e) => println!("✗ Evaluation failed: {e}"),
    }
}
