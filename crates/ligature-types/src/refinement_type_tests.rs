use crate::checker::TypeChecker;
use ligature_ast::{Expr, ExprKind, Literal, Span, Type};

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
        assert!(matches!(base.kind, ligature_ast::TypeKind::Integer));
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

    let constraint_type = Type::constraint_type(base_type, vec![constraint], Span::default());

    // Verify the constraint type was created correctly
    assert!(constraint_type.is_constraint_type());

    if let Some((base, constraints)) = constraint_type.as_constraint_type() {
        assert!(matches!(base.kind, ligature_ast::TypeKind::String));
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
    let checker = TypeChecker::new();
    let are_equal = checker.types_equal(&refinement1, &refinement2).unwrap();
    assert!(
        are_equal,
        "Refinement types with same base type and predicate name should be equal"
    );
}

#[test]
fn test_refinement_type_checking() {
    // Test that refinement types can be type-checked
    let base_type = Type::integer(Span::default());
    let predicate = Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)),
        span: Span::default(),
    };

    let refinement_type = Type::refinement(
        base_type,
        predicate,
        Some("isPositive".to_string()),
        Span::default(),
    );

    // Test that the refinement type can be checked
    let mut checker = TypeChecker::new();
    let result = checker.check_type(&refinement_type);
    assert!(
        result.is_ok(),
        "Refinement type checking should work: {result:?}"
    );
}

#[test]
fn test_constraint_type_checking() {
    // Test that constraint types can be type-checked
    let base_type = Type::string(Span::default());
    let constraint = ligature_ast::ty::Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)),
        span: Span::default(),
    }));

    let constraint_type = Type::constraint_type(base_type, vec![constraint], Span::default());

    // Test that the constraint type can be checked
    let mut checker = TypeChecker::new();
    let result = checker.check_type(&constraint_type);
    assert!(
        result.is_ok(),
        "Constraint type checking should work: {result:?}"
    );
}
