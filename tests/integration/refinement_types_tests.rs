use ligature_ast::{Expr, ExprKind, Literal, Span, Type, TypeKind};
use ligature_parser::parse_program;
use ligature_types::type_check_program;

#[test]
fn test_refinement_type_creation() {
    // Test that we can create refinement types
    let base_type = Type::integer(Span::default());
    let predicate = Expr {
        kind: ExprKind::BinaryOp {
            operator: ligature_ast::BinaryOperator::GreaterThan,
            left: Box::new(Expr {
                kind: ExprKind::Variable("x".to_string()),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(0)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let refinement_type = Type::refinement(
        base_type,
        predicate,
        Some("isPositive".to_string()),
        Span::default(),
    );

    // Verify the refinement type was created correctly
    assert!(refinement_type.is_refinement());
    
    if let Some((base, pred, name)) = refinement_type.as_refinement() {
        assert!(base.is_integer());
        assert!(matches!(pred.kind, ExprKind::BinaryOp { .. }));
        assert_eq!(name, &Some("isPositive".to_string()));
    } else {
        panic!("Refinement type should have base type, predicate, and name");
    }
}

#[test]
fn test_constraint_type_creation() {
    // Test that we can create constraint types
    let base_type = Type::string(Span::default());
    let constraint = ligature_ast::ty::Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::BinaryOp {
            operator: ligature_ast::BinaryOperator::GreaterThan,
            left: Box::new(Expr {
                kind: ExprKind::Variable("x".to_string()),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(0)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    }));

    let constraint_type = Type::constraint_type(
        base_type,
        vec![constraint],
        Span::default(),
    );

    // Verify the constraint type was created correctly
    assert!(constraint_type.is_constraint_type());
    
    if let Some((base, constraints)) = constraint_type.as_constraint_type() {
        assert!(base.is_string());
        assert_eq!(constraints.len(), 1);
    } else {
        panic!("Constraint type should have base type and constraints");
    }
}

#[test]
fn test_refinement_type_equality() {
    // Test that refinement types can be compared for equality
    let base_type1 = Type::integer(Span::default());
    let base_type2 = Type::integer(Span::default());
    
    let predicate = Expr {
        kind: ExprKind::BinaryOp {
            operator: ligature_ast::BinaryOperator::GreaterThan,
            left: Box::new(Expr {
                kind: ExprKind::Variable("x".to_string()),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(0)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    let refinement1 = Type::refinement(
        base_type1,
        predicate.clone(),
        Some("isPositive".to_string()),
        Span::default(),
    );

    let refinement2 = Type::refinement(
        base_type2,
        predicate,
        Some("isPositive".to_string()),
        Span::default(),
    );

    // Test type equality
    let mut checker = ligature_types::checker::TypeChecker::new();
    let are_equal = checker.types_equal(&refinement1, &refinement2).unwrap();
    assert!(are_equal, "Refinement types with same base type and predicate name should be equal");
}

#[test]
fn test_simple_refinement_type_parsing() {
    // Test that we can parse a simple refinement type
    let source = "
        type PositiveInt = Int where x > 0;
        let value: PositiveInt = 42;
    ";

    let program = parse_program(source);
    // For now, we expect parsing to fail since we haven't implemented the grammar yet
    // This test will be updated once we implement the parser support
    assert!(program.is_err(), "Parsing should fail until grammar is implemented");
} 