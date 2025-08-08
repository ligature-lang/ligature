//! Runtime Validation Engine Example
//!
//! This example demonstrates the Phase 3 runtime validation engine for
//! constraint-based validation in the Ligature language.
//!
//! Features demonstrated:
//! - Refinement type validation: `type T = BaseType where predicate`
//! - Constraint type validation: `type T = BaseType with constraint1 with constraint2`
//! - Pattern constraint validation with regex
//! - Basic type validation
//! - Integration with the evaluator

use ligature_ast::ty::Constraint;
use ligature_ast::{Expr, ExprKind, Literal, Span, Type};
use ligature_eval::{Evaluator, Value};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Runtime Validation Engine Example ===\n");

    let mut evaluator = Evaluator::new();

    // Example 1: Basic Type Validation
    println!("1. Basic Type Validation");
    println!("------------------------");

    let int_type = Type::integer(Span::default());
    let int_value = Value::integer(42, Span::default());
    let result = evaluator.validate_value(&int_value, &int_type)?;
    println!("Validating integer 42 against Int type: {result:?}");

    let string_type = Type::string(Span::default());
    let string_value = Value::string("hello".to_string(), Span::default());
    let result = evaluator.validate_value(&string_value, &string_type)?;
    println!("Validating string 'hello' against String type: {result:?}");

    // Type mismatch
    let result = evaluator.validate_value(&int_value, &string_type)?;
    println!("Validating integer 42 against String type: {result:?}");
    println!();

    // Example 2: Refinement Type Validation
    println!("2. Refinement Type Validation");
    println!("-----------------------------");

    // Create a refinement type: PositiveInt = Int where x > 0
    let predicate = Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified predicate
        span: Span::default(),
    };

    let refinement_type = Type::refinement(
        int_type.clone(),
        predicate,
        Some("isPositive".to_string()),
        Span::default(),
    );

    let positive_value = Value::integer(42, Span::default());
    let result = evaluator.validate_value(&positive_value, &refinement_type)?;
    println!("Validating positive integer 42 against PositiveInt: {result:?}");

    let negative_value = Value::integer(-5, Span::default());
    let result = evaluator.validate_value(&negative_value, &refinement_type)?;
    println!("Validating negative integer -5 against PositiveInt: {result:?}");
    println!();

    // Example 3: Constraint Type Validation
    println!("3. Constraint Type Validation");
    println!("-----------------------------");

    // Create a constraint type: ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$")
    let email_constraint = Constraint::PatternConstraint {
        pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
        regex: true,
    };

    let constraint_type =
        Type::constraint_type(string_type.clone(), vec![email_constraint], Span::default());

    let valid_email = Value::string("user@example.com".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_email, &constraint_type)?;
    println!("Validating 'user@example.com' against ValidEmail: {result:?}");

    let invalid_email = Value::string("invalid-email".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_email, &constraint_type)?;
    println!("Validating 'invalid-email' against ValidEmail: {result:?}");
    println!();

    // Example 4: Multiple Constraints
    println!("4. Multiple Constraints");
    println!("----------------------");

    // Create a type with multiple constraints: NonEmptyAlpha = String with regexp("^[A-Za-z]+$") with length > 0
    let alpha_constraint = Constraint::PatternConstraint {
        pattern: "^[A-Za-z]+$".to_string(),
        regex: true,
    };

    let length_constraint = Constraint::ValueConstraint(Box::new(Expr {
        kind: ExprKind::Literal(Literal::Boolean(true)), // Simplified length check
        span: Span::default(),
    }));

    let multi_constraint_type = Type::constraint_type(
        string_type.clone(),
        vec![alpha_constraint, length_constraint],
        Span::default(),
    );

    let valid_alpha = Value::string("Hello".to_string(), Span::default());
    let result = evaluator.validate_value(&valid_alpha, &multi_constraint_type)?;
    println!("Validating 'Hello' against NonEmptyAlpha: {result:?}");

    let invalid_alpha = Value::string("Hello123".to_string(), Span::default());
    let result = evaluator.validate_value(&invalid_alpha, &multi_constraint_type)?;
    println!("Validating 'Hello123' against NonEmptyAlpha: {result:?}");
    println!();

    // Example 5: Validation Statistics
    println!("5. Validation Statistics");
    println!("------------------------");

    let stats = evaluator.validation_stats();
    println!("Validation cache size: {}", stats.cache_size);
    println!("Regex cache size: {}", stats.regex_cache_size);
    println!("Caching enabled: {}", stats.caching_enabled);
    println!();

    // Example 6: Complex Refinement Type
    println!("6. Complex Refinement Type");
    println!("--------------------------");

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

    let user_refinement_type = Type::refinement(
        record_type,
        user_predicate,
        Some("isValidUser".to_string()),
        Span::default(),
    );

    // Create a record value
    let mut user_fields = std::collections::HashMap::new();
    user_fields.insert(
        "name".to_string(),
        Value::string("Alice".to_string(), Span::default()),
    );
    user_fields.insert("age".to_string(), Value::integer(25, Span::default()));
    let user_value = Value::record(user_fields, Span::default());

    let result = evaluator.validate_value(&user_value, &user_refinement_type)?;
    println!("Validating user record against ValidUser: {result:?}");
    println!();

    // Example 7: Error Handling
    println!("7. Error Handling");
    println!("-----------------");

    // Test with unsupported constraint types
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

    let range_type =
        Type::constraint_type(int_type.clone(), vec![range_constraint], Span::default());

    let test_value = Value::integer(50, Span::default());
    let result = evaluator.validate_value(&test_value, &range_type)?;
    println!("Validating with range constraint (not implemented): {result:?}");
    println!();

    println!("=== Validation Engine Example Complete ===");
    println!();
    println!("Key Features Implemented:");
    println!("✓ Basic type validation");
    println!("✓ Refinement type validation");
    println!("✓ Pattern constraint validation with regex");
    println!("✓ Multiple constraint validation");
    println!("✓ Validation statistics");
    println!("✓ Error handling for unsupported constraints");
    println!();
    println!("Future Enhancements:");
    println!("- Range constraint validation");
    println!("- Custom constraint validation");
    println!("- Cross-field constraint validation");
    println!("- Complex predicate evaluation");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_validation() {
        let mut evaluator = Evaluator::new();

        let int_type = Type::integer(Span::default());
        let int_value = Value::integer(42, Span::default());
        let result = evaluator.validate_value(&int_value, &int_type).unwrap();
        assert_eq!(result, ValidationResult::Valid);
    }

    #[test]
    fn test_pattern_constraint() {
        let mut evaluator = Evaluator::new();

        let constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };

        let constraint_type = Type::constraint_type(
            Type::string(Span::default()),
            vec![constraint],
            Span::default(),
        );

        let valid_value = Value::string("Hello".to_string(), Span::default());
        let result = evaluator
            .validate_value(&valid_value, &constraint_type)
            .unwrap();
        assert_eq!(result, ValidationResult::Valid);

        let invalid_value = Value::string("Hello123".to_string(), Span::default());
        let result = evaluator
            .validate_value(&invalid_value, &constraint_type)
            .unwrap();
        assert!(matches!(result, ValidationResult::Invalid(_)));
    }
}
