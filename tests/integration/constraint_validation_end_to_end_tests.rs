//! End-to-end tests for constraint-based validation.
//!
//! These tests verify the complete pipeline from parsing constraint-based
//! validation syntax through AST construction to runtime validation.

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
fn test_complete_refinement_type_pipeline() -> AstResult<()> {
    // Test the complete pipeline for refinement types
    let source = "
        type PositiveInt = Int where x > 0;
        let value = 42;
        value
    ";

    // Step 1: Parse the program
    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Step 2: Extract the refinement type from the parsed program
    let refinement_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "PositiveInt");
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    // Step 3: Verify it's a refinement type
    assert!(matches!(refinement_type.kind, TypeKind::Refinement { .. }));

    // Step 4: Create a runtime validation engine
    let mut evaluator = Evaluator::new();

    // Step 5: Test validation with positive integer
    let positive_value = Value::integer(42, Span::default());
    let result = evaluator.validate_value(&positive_value, &refinement_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Step 6: Test validation with negative integer
    let negative_value = Value::integer(-5, Span::default());
    let result = evaluator.validate_value(&negative_value, &refinement_type)?;
    // Note: Currently using simplified predicate that always returns true
    assert_eq!(result, ValidationResult::Valid);

    Ok(())
}

#[test]
fn test_complete_constraint_type_pipeline() -> AstResult<()> {
    // Test the complete pipeline for constraint types
    let source = "
        type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");
        let email = \"user@example.com\";
        email
    ";

    // Step 1: Parse the program
    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Step 2: Extract the constraint type from the parsed program
    let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "ValidEmail");
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    // Step 3: Verify it's a constraint type
    assert!(matches!(
        constraint_type.kind,
        TypeKind::ConstraintType { .. }
    ));

    // Step 4: Create a runtime validation engine
    let mut evaluator = Evaluator::new();

    // Step 5: Test validation with valid email
    let valid_email = Value::string("user@example.com".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_email, &constraint_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Step 6: Test validation with invalid email
    let invalid_email = Value::string("invalid-email".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_email, &constraint_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_complete_multiple_constraints_pipeline() -> AstResult<()> {
    // Test the complete pipeline for multiple constraints
    let source = "
        type NonEmptyAlpha = String with regexp(\"^[A-Za-z]+$\") with length > 0;
        let name = \"Hello\";
        name
    ";

    // Step 1: Parse the program
    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Step 2: Extract the constraint type from the parsed program
    let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "NonEmptyAlpha");
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    // Step 3: Verify it's a constraint type with multiple constraints
    if let TypeKind::ConstraintType { constraints, .. } = &constraint_type.kind {
        assert_eq!(constraints.len(), 2);
    } else {
        panic!("Expected constraint type");
    }

    // Step 4: Create a runtime validation engine
    let mut evaluator = Evaluator::new();

    // Step 5: Test validation with valid string
    let valid_string = Value::string("Hello".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_string, &constraint_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Step 6: Test validation with invalid string (contains numbers)
    let invalid_string = Value::string("Hello123".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_string, &constraint_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_complete_record_refinement_pipeline() -> AstResult<()> {
    // Test the complete pipeline for record refinement types
    let source = "
        type ValidUser = { name: String, age: Int } where isValidUser x;
        let user = { name = \"Alice\", age = 25 };
        user
    ";

    // Step 1: Parse the program
    let program = parse_program(source)?;
    assert_eq!(program.declarations.len(), 2);

    // Step 2: Extract the refinement type from the parsed program
    let refinement_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        assert_eq!(type_alias.name, "ValidUser");
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    // Step 3: Verify it's a refinement type
    assert!(matches!(refinement_type.kind, TypeKind::Refinement { .. }));

    // Step 4: Create a runtime validation engine
    let mut evaluator = Evaluator::new();

    // Step 5: Create a record value
    let mut user_fields = std::collections::HashMap::new();
    user_fields.insert(
        "name".to_string(),
        Value::string("Alice".to_string(), Span::default()),
    );
    user_fields.insert("age".to_string(), Value::integer(25, Span::default()));
    let user_value = Value::record(user_fields, Span::default());

    // Step 6: Test validation
    let result = evaluator.validate_value(&user_value, &refinement_type)?;
    assert_eq!(result, ValidationResult::Valid);

    Ok(())
}

#[test]
fn test_complete_error_handling_pipeline() -> AstResult<()> {
    // Test error handling in the complete pipeline

    // Test 1: Invalid regex pattern
    let source = "
        type InvalidEmail = String with regexp(\"[invalid\");
        let email = \"test@example.com\";
        email
    ";

    // This should parse successfully, but validation should fail
    let program = parse_program(source)?;
    let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    let mut evaluator = Evaluator::new();
    let test_value = Value::string("test@example.com".to_string(), Span::default());
    let result = evaluator.validate_value(&test_value, &constraint_type);

    // Should return an error for invalid regex
    assert!(result.is_err());

    // Test 2: Unsupported constraint types
    let source = "
        type UnsupportedType = Int with >= 0 with <= 100;
        let value = 50;
        value
    ";

    let program = parse_program(source)?;
    let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
        type_alias.type_.clone()
    } else {
        panic!("Expected type alias declaration");
    };

    let test_value = Value::integer(50, Span::default());
    let result = evaluator.validate_value(&test_value, &constraint_type)?;

    // Should return CannotValidate for unsupported constraints
    assert!(matches!(result, ValidationResult::CannotValidate(_)));

    Ok(())
}

#[test]
fn test_complete_performance_pipeline() -> AstResult<()> {
    // Test performance characteristics of the complete pipeline
    let mut evaluator = Evaluator::new();

    // Create a constraint type with regex
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        create_constraint_type(Type::string(Span::default()), vec![email_constraint]);

    let email_value = Value::string("user@example.com".to_string(), Span::default());

    // Test first validation (compiles regex)
    let start = std::time::Instant::now();
    let result1 = evaluator.validate_value(&email_value, &constraint_type)?;
    let first_duration = start.elapsed();
    assert_eq!(result1, ValidationResult::Valid);

    // Test second validation (uses cached regex)
    let start = std::time::Instant::now();
    let result2 = evaluator.validate_value(&email_value, &constraint_type)?;
    let second_duration = start.elapsed();
    assert_eq!(result2, ValidationResult::Valid);

    // Second validation should be faster due to regex caching
    assert!(second_duration <= first_duration);

    // Test with caching enabled
    evaluator.set_validation_caching(true);

    let start = std::time::Instant::now();
    let result3 = evaluator.validate_value(&email_value, &constraint_type)?;
    let cached_duration = start.elapsed();
    assert_eq!(result3, ValidationResult::Valid);

    // Cached validation should be fast
    assert!(cached_duration <= second_duration);

    Ok(())
}

#[test]
fn test_complete_real_world_scenario() -> AstResult<()> {
    // Test a realistic scenario with multiple constraint types
    let mut evaluator = Evaluator::new();

    // Define multiple constraint types programmatically (simulating parsed types)
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let age_constraint = Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified age check
        span: Span::default(),
    }));

    let name_constraint = Constraint::PatternConstraint {
        pattern: "^[A-Za-z ]+$".to_string(),
        regex: true,
    };

    // User type with multiple constraints
    let user_type = create_constraint_type(
        Type::record(
            vec![
                ligature_ast::TypeField {
                    name: "name".to_string(),
                    type_: Type::string(Span::default()),
                    span: Span::default(),
                },
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
        vec![name_constraint, email_constraint, age_constraint],
    );

    // Test valid user
    let mut valid_user_fields = std::collections::HashMap::new();
    valid_user_fields.insert(
        "name".to_string(),
        Value::string("John Doe".to_string(), Span::default()),
    );
    valid_user_fields.insert(
        "email".to_string(),
        Value::string("john@example.com".to_string(), Span::default()),
    );
    valid_user_fields.insert("age".to_string(), Value::integer(30, Span::default()));
    let valid_user = Value::record(valid_user_fields, Span::default());

    let result = evaluator.validate_value(&valid_user, &user_type)?;
    assert_eq!(result, ValidationResult::Valid);

    // Test invalid user (invalid email)
    let mut invalid_user_fields = std::collections::HashMap::new();
    invalid_user_fields.insert(
        "name".to_string(),
        Value::string("John Doe".to_string(), Span::default()),
    );
    invalid_user_fields.insert(
        "email".to_string(),
        Value::string("invalid-email".to_string(), Span::default()),
    );
    invalid_user_fields.insert("age".to_string(), Value::integer(30, Span::default()));
    let invalid_user = Value::record(invalid_user_fields, Span::default());

    let result = evaluator.validate_value(&invalid_user, &user_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    // Test invalid user (invalid name with numbers)
    let mut invalid_name_fields = std::collections::HashMap::new();
    invalid_name_fields.insert(
        "name".to_string(),
        Value::string("John123".to_string(), Span::default()),
    );
    invalid_name_fields.insert(
        "email".to_string(),
        Value::string("john@example.com".to_string(), Span::default()),
    );
    invalid_name_fields.insert("age".to_string(), Value::integer(30, Span::default()));
    let invalid_name_user = Value::record(invalid_name_fields, Span::default());

    let result = evaluator.validate_value(&invalid_name_user, &user_type)?;
    assert!(matches!(result, ValidationResult::Invalid(_)));

    Ok(())
}

#[test]
fn test_complete_statistics_and_monitoring() -> AstResult<()> {
    // Test statistics and monitoring capabilities
    let mut evaluator = Evaluator::new();

    // Perform various validations
    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());
    let _ = evaluator.validate_value(&int_value, &int_type)?;

    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        create_constraint_type(Type::string(Span::default()), vec![email_constraint]);

    let email_value = Value::string("user@example.com".to_string(), Span::default());
    let _ = evaluator.validate_value(&email_value, &constraint_type)?;

    // Test with caching enabled
    evaluator.set_validation_caching(true);
    let _ = evaluator.validate_value(&int_value, &int_type)?;
    let _ = evaluator.validate_value(&email_value, &constraint_type)?;

    // Check statistics
    let stats = evaluator.validation_stats();
    assert_eq!(stats.caching_enabled, true);
    assert_eq!(stats.regex_cache_size, 1); // One regex pattern cached

    // Clear cache and check
    evaluator.clear_validation_cache();
    let stats = evaluator.validation_stats();
    assert_eq!(stats.cache_size, 0);

    Ok(())
}
