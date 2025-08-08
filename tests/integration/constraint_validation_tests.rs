//! Integration tests for constraint-based validation.
//!
//! These tests verify the complete pipeline from parsing constraint-based
//! validation syntax through AST construction to runtime validation.

use crate::integration::{create_test_environment, parse_type_check_and_evaluate};
use ligature_ast::ty::Constraint;
use ligature_ast::{AstResult, Expr, ExprKind, Literal, Span, Type, TypeKind};
use ligature_eval::{evaluate_program, Evaluator, ValidationResult, Value};
use ligature_parser::parse_program;
use ligature_types::type_check_program;

/// Helper function to create a refinement type for testing
fn create_refinement_type(base_type: Type, predicate: Expr) -> Type {
    Type::refinement(
        base_type,
        predicate,
        Some("test_predicate".to_string()),
        Span::default(),
    )
}

/// Helper function to create a constraint type for testing
fn create_constraint_type(base_type: Type, constraints: Vec<Constraint>) -> Type {
    Type::constraint_type(base_type, constraints, Span::default())
}

#[test]
fn test_basic_refinement_type_parsing() -> AstResult<()> {
    let source = "
        type PositiveInt = Int where x > 0;
        let value = 42;
        value
    ";

    // This should parse successfully even though validation isn't implemented yet
    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Check that the type alias was parsed correctly
    if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "PositiveInt");
        // The type should be a refinement type
        assert!(matches!(type_alias.type_.kind, TypeKind::Refinement { .. }));
    } else {
        panic!("Expected type alias declaration");
    }

    Ok(())
}

#[test]
fn test_basic_constraint_type_parsing() -> AstResult<()> {
    let source = "
        type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");
        let email = \"user@example.com\";
        email
    ";

    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Check that the type alias was parsed correctly
    if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "ValidEmail");
        // The type should be a constraint type
        assert!(matches!(
            type_alias.type_.kind,
            TypeKind::ConstraintType { .. }
        ));
    } else {
        panic!("Expected type alias declaration");
    }

    Ok(())
}

#[test]
fn test_multiple_constraints_parsing() -> AstResult<()> {
    let source = "
        type NonEmptyAlpha = String with regexp(\"^[A-Za-z]+$\") with length > 0;
        let name = \"Hello\";
        name
    ";

    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Check that the type alias was parsed correctly
    if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "NonEmptyAlpha");
        // The type should be a constraint type with multiple constraints
        if let TypeKind::ConstraintType { constraints, .. } = &type_alias.type_.kind {
            assert_eq!(constraints.len(), 2);
        } else {
            panic!("Expected constraint type");
        }
    } else {
        panic!("Expected type alias declaration");
    }

    Ok(())
}

#[test]
fn test_runtime_validation_basic_types() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Test integer validation
    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());
    let result = evaluator.validate_value(&int_value, &int_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Test string validation
    let string_type = Type::string(Span::default());
    let string_value = Value::string("hello".to_string(), Span::default());
    let result = evaluator.validate_value(&string_value, &string_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Test type mismatch
    let result = evaluator.validate_value(&int_value, &string_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_runtime_validation_refinement_types() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Create a refinement type: PositiveInt = Int where x > 0
    let predicate = Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified predicate
        span: Span::default(),
    };

    let refinement_type = create_refinement_type(Type::integer(Span::default()), predicate);

    let positive_value = Value::integer(42, Span::default());
    let result = evaluator.validate_value(&positive_value, &refinement_type)?;
    assert_eq!(result, ValidationResult::Valid);

    let negative_value = Value::integer(-5, Span::default());
    let result = evaluator.validate_value(&negative_value, &refinement_type)?;
    assert_eq!(result, ValidationResult::Valid); // Simplified predicate always returns true

    Ok(())
}

#[test]
fn test_runtime_validation_pattern_constraints() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Create a constraint type: ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$")
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        create_constraint_type(Type::string(Span::default()), vec![email_constraint]);

    let valid_email = Value::string("user@example.com".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_email, &constraint_type)?;
    assert_eq!(result, ValidationResult::Valid);

    let invalid_email = Value::string("invalid-email".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_email, &constraint_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_runtime_validation_multiple_constraints() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Create a type with multiple constraints: NonEmptyAlpha = String with regexp("^[A-Za-z]+$") with length > 0
    let alpha_constraint = Constraint::PatternConstraint {
        pattern: "^[A-Za-z]+$".to_string(),
        regex: true,
    };

    let length_constraint = Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified length check
        span: Span::default(),
    }));

    let multi_constraint_type = create_constraint_type(
        Type::string(Span::default()),
        vec![alpha_constraint, length_constraint],
    );

    let valid_alpha = Value::string("Hello".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_alpha, &multi_constraint_type)?;
    assert_eq!(result, ValidationResult::Valid);

    let invalid_alpha = Value::string("Hello123".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_alpha, &multi_constraint_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_runtime_validation_unsupported_constraints() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Test range constraints (not yet implemented)
    let range_constraint = Constraint::RangeConstraint {
        min: Some(Box::new(Expr {
            kind: ExprKind::Literal(Literal::Integer(0)),
            span: Span::default(),
        })),
        max: Some(Box::new(Expr {
            kind: ExprKind::Literal(Literal::Integer(100)),
            span: Span::default(),
        })),
        inclusive: true,
    };

    let range_type = create_constraint_type(Type::integer(Span::default()), vec![range_constraint]);

    let test_value = Value::integer(50, Span::default());
    let result = evaluator.validate_value(&test_value, &range_type)?;
    assert!(matches!(result, ValidationResult::CannotValidate(_)));

    // Test custom constraints (not yet implemented)
    let custom_constraint = Constraint::CustomConstraint {
        function: "isValidEmail".to_string(),
        arguments: vec![],
    };

    let custom_type =
        create_constraint_type(Type::string(Span::default()), vec![custom_constraint]);

    let test_string = Value::string("test@example.com".to_string(), Span::default());
    let result = evaluator.validate_value(&test_string, &custom_type)?;
    assert!(matches!(result, ValidationResult::CannotValidate(_)));

    Ok(())
}

#[test]
fn test_validation_statistics() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Perform some validations to generate statistics
    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());
    let _ = evaluator.validate_value(&int_value, &int_type)?;

    let string_type = Type::string(Span::default());
    let string_value = Value::string("hello".to_string(), Span::default());
    let _ = evaluator.validate_value(&string_value, &string_type)?;

    // Check statistics
    let stats = evaluator.validation_stats();
    assert_eq!(stats.cache_size, 0); // Caching disabled by default
    assert_eq!(stats.regex_cache_size, 0); // No regex patterns used in this test
    assert_eq!(stats.caching_enabled, false);

    Ok(())
}

#[test]
fn test_validation_caching() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Enable caching
    evaluator.set_validation_caching(true);

    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());

    // First validation
    let result1 = evaluator.validate_value(&int_value, &int_type)?;
    assert_eq!(result1, ValidationResult::Valid);

    // Second validation (should use cache)
    let result2 = evaluator.validate_value(&int_value, &int_type)?;
    assert_eq!(result2, ValidationResult::Valid);

    // Check that caching is enabled
    let stats = evaluator.validation_stats();
    assert_eq!(stats.caching_enabled, true);

    // Clear cache
    evaluator.clear_validation_cache();
    let stats = evaluator.validation_stats();
    assert_eq!(stats.cache_size, 0);

    Ok(())
}

#[test]
fn test_regex_caching() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        create_constraint_type(Type::string(Span::default()), vec![email_constraint]);

    let email1 = Value::string("user1@example.com".to_string(), Span::default());
    let email2 = Value::string("user2@example.com".to_string(), Span::default());

    // First validation (compiles regex)
    let result1 = evaluator.validate_value(&email1, &constraint_type)?;
    assert_eq!(result1, ValidationResult::Valid);

    // Second validation (uses cached regex)
    let result2 = evaluator.validate_value(&email2, &constraint_type)?;
    assert_eq!(result2, ValidationResult::Valid);

    // Check regex cache
    let stats = evaluator.validation_stats();
    assert_eq!(stats.regex_cache_size, 1); // One regex pattern cached

    Ok(())
}

#[test]
fn test_complex_refinement_type_validation() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Create a refinement type for a record: ValidUser = { name: String, age: Int } where isValidUser x
    let record_type = Type::record(
        vec![
            ligature_ast::TypeField {
                name: "name".to_string(),
                type_: Type::string(Span::default()),
                span: Span::default(),
            },
            ligature_ast::TypeField {
                name: "age".to_string(),
                type_: Type::integer(Span::default()),
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    let user_predicate = Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified predicate
        span: Span::default(),
    };

    let user_refinement_type = create_refinement_type(record_type, user_predicate);

    // Create a record value
    let mut user_fields = std::collections::HashMap::new();
    user_fields.insert(
        "name".to_string(),
        Value::string("Alice".to_string(), Span::default()),
    );
    user_fields.insert("age".to_string(), Value::integer(25, Span::default()));
    let user_value = Value::record(user_fields, Span::default());

    let result = evaluator.validate_value(&user_value, &user_refinement_type)?;
    assert_eq!(result, ValidationResult::Valid);

    Ok(())
}

#[test]
fn test_error_handling_invalid_regex() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Create a constraint with invalid regex
    let invalid_regex_constraint = Constraint::PatternConstraint {
        pattern: "[invalid".to_string(), // Invalid regex pattern
        regex: true,
    };

    let constraint_type = create_constraint_type(
        Type::string(Span::default()),
        vec![invalid_regex_constraint],
    );

    let test_value = Value::string("test".to_string(), Span::default());
    let result = evaluator.validate_value(&test_value, &constraint_type);

    // Should return an error for invalid regex
    assert!(result.is_err());

    Ok(())
}

#[test]
fn test_end_to_end_constraint_validation_pipeline() -> AstResult<()> {
    // This test simulates a complete end-to-end scenario
    let mut evaluator = Evaluator::new();

    // Define constraint types programmatically (simulating parsed types)
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let age_constraint = Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified age check
        span: Span::default(),
    }));

    let user_type = create_constraint_type(
        Type::record(
            vec![
                ligature_ast::TypeField {
                    name: "email".to_string(),
                    type_: Type::string(Span::default()),
                    span: Span::default(),
                },
                ligature_ast::TypeField {
                    name: "age".to_string(),
                    type_: Type::integer(Span::default()),
                    span: Span::default(),
                },
            ],
            Span::default(),
        ),
        vec![email_constraint, age_constraint],
    );

    // Create valid user data
    let mut valid_user_fields = std::collections::HashMap::new();
    valid_user_fields.insert(
        "email".to_string(),
        Value::string("user@example.com".to_string(), Span::default()),
    );
    valid_user_fields.insert("age".to_string(), Value::integer(25, Span::default()));
    let valid_user = Value::record(valid_user_fields, Span::default());

    // Validate valid user
    let result = evaluator.validate_value(&valid_user, &user_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Create invalid user data (invalid email)
    let mut invalid_user_fields = std::collections::HashMap::new();
    invalid_user_fields.insert(
        "email".to_string(),
        Value::string("invalid-email".to_string(), Span::default()),
    );
    invalid_user_fields.insert("age".to_string(), Value::integer(25, Span::default()));
    let invalid_user = Value::record(invalid_user_fields, Span::default());

    // Validate invalid user
    let result = evaluator.validate_value(&invalid_user, &user_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_validation_performance_characteristics() -> AstResult<()> {
    let mut evaluator = Evaluator::new();

    // Test basic type validation performance
    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());

    let start = std::time::Instant::now();
    for _ in 0..1000 {
        let _ = evaluator.validate_value(&int_value, &int_type)?;
    }
    let basic_duration = start.elapsed();

    // Test pattern constraint validation performance
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        create_constraint_type(Type::string(Span::default()), vec![email_constraint]);

    let email_value = Value::string("user@example.com".to_string(), Span::default());

    let start = std::time::Instant::now();
    for _ in 0..1000 {
        let _ = evaluator.validate_value(&email_value, &constraint_type)?;
    }
    let pattern_duration = start.elapsed();

    // Basic validation should be faster than pattern validation
    assert!(basic_duration < pattern_duration);

    // Test regex caching performance
    let start = std::time::Instant::now();
    for _ in 0..1000 {
        let _ = evaluator.validate_value(&email_value, &constraint_type)?;
    }
    let cached_duration = start.elapsed();

    // Cached validation should be faster than first-time validation
    assert!(cached_duration <= pattern_duration);

    Ok(())
}
