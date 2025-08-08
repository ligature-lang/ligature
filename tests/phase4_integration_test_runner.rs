//! Phase 4: Integration and End-to-End Testing for Constraint-Based Validation
//!
//! This test runner verifies the complete pipeline from parsing constraint-based
//! validation syntax through AST construction to runtime validation.

use ligature_ast::ty::Constraint;
use ligature_ast::{AstResult, Expr, ExprKind, Literal, Span, Type, TypeKind};
use ligature_eval::{evaluate_program, Evaluator, ValidationResult, Value};
use ligature_parser::parse_program;
use ligature_types::type_check_program;
use std::time::Instant;

/// Test suite for Phase 4 integration testing
struct Phase4TestSuite {
    name: String,
    tests: Vec<Box<dyn Fn() -> AstResult<()>>>,
    passed: usize,
    failed: usize,
    duration: std::time::Duration,
}

impl Phase4TestSuite {
    fn new(name: String) -> Self {
        Self {
            name,
            tests: Vec::new(),
            passed: 0,
            failed: 0,
            duration: std::time::Duration::ZERO,
        }
    }

    fn add_test<F>(&mut self, test: F)
    where
        F: Fn() -> AstResult<()> + 'static,
    {
        self.tests.push(Box::new(test));
    }

    fn run(&mut self) {
        println!("Running {}...", self.name);
        let start = Instant::now();

        for (i, test) in self.tests.iter().enumerate() {
            print!("  Test {}: ", i + 1);
            match test() {
                Ok(_) => {
                    println!("✅ PASSED");
                    self.passed += 1;
                }
                Err(e) => {
                    println!("❌ FAILED - {}", e);
                    self.failed += 1;
                }
            }
        }

        self.duration = start.elapsed();
        println!(
            "  Summary: {} passed, {} failed in {:?}",
            self.passed, self.failed, self.duration
        );
        println!();
    }

    fn total_tests(&self) -> usize {
        self.passed + self.failed
    }
}

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

fn main() -> AstResult<()> {
    println!("=== Phase 4: Integration and End-to-End Testing ===");
    println!("Testing complete constraint-based validation pipeline\n");

    let mut total_passed = 0;
    let mut total_failed = 0;
    let start = Instant::now();

    // Test Suite 1: Basic Parsing and AST Construction
    let mut parsing_suite = Phase4TestSuite::new("Basic Parsing and AST Construction".to_string());

    parsing_suite.add_test(|| {
        let source = "type PositiveInt = Int where x > 0;";
        let program = parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);
        Ok(())
    });

    parsing_suite.add_test(|| {
        let source = "type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");";
        let program = parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);
        Ok(())
    });

    parsing_suite.add_test(|| {
        let source = "type NonEmptyAlpha = String with regexp(\"^[A-Za-z]+$\") with length > 0;";
        let program = parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);
        Ok(())
    });

    parsing_suite.run();
    total_passed += parsing_suite.passed;
    total_failed += parsing_suite.failed;

    // Test Suite 2: Runtime Validation Engine
    let mut validation_suite = Phase4TestSuite::new("Runtime Validation Engine".to_string());

    validation_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let int_type = Type::integer(Span::default());
        let int_value = Value::integer(42, Span::default());
        let result = evaluator.validate_value(&int_value, &int_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    validation_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let string_type = Type::string(Span::default());
        let string_value = Value::string("hello".to_string(), Span::default());
        let result = evaluator.validate_value(&string_value, &string_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    validation_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let int_type = Type::integer(Span::default());
        let string_value = Value::string("hello".to_string(), Span::default());
        let result = evaluator.validate_value(&string_value, &int_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    validation_suite.run();
    total_passed += validation_suite.passed;
    total_failed += validation_suite.failed;

    // Test Suite 3: Refinement Type Validation
    let mut refinement_suite = Phase4TestSuite::new("Refinement Type Validation".to_string());

    refinement_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let predicate = Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        };
        let refinement_type = create_refinement_type(Type::integer(Span::default()), predicate);
        let value = Value::integer(42, Span::default());
        let result = evaluator.validate_value(&value, &refinement_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    refinement_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let predicate = Expr {
            kind: ExprKind::Literal(Literal::Boolean(false)),
            span: Span::default(),
        };
        let refinement_type = create_refinement_type(Type::integer(Span::default()), predicate);
        let value = Value::integer(42, Span::default());
        let result = evaluator.validate_value(&value, &refinement_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    refinement_suite.run();
    total_passed += refinement_suite.passed;
    total_failed += refinement_suite.failed;

    // Test Suite 4: Constraint Type Validation
    let mut constraint_suite = Phase4TestSuite::new("Constraint Type Validation".to_string());

    constraint_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let email_constraint = Constraint::PatternConstraint {
            pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![email_constraint]);
        let valid_email = Value::string("user@example.com".to_string(), Span::default());
        let result = evaluator.validate_value(&valid_email, &constraint_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    constraint_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let email_constraint = Constraint::PatternConstraint {
            pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![email_constraint]);
        let invalid_email = Value::string("invalid-email".to_string(), Span::default());
        let result = evaluator.validate_value(&invalid_email, &constraint_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    constraint_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let alpha_constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![alpha_constraint]);
        let valid_alpha = Value::string("Hello".to_string(), Span::default());
        let result = evaluator.validate_value(&valid_alpha, &constraint_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    constraint_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let alpha_constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![alpha_constraint]);
        let invalid_alpha = Value::string("Hello123".to_string(), Span::default());
        let result = evaluator.validate_value(&invalid_alpha, &constraint_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    constraint_suite.run();
    total_passed += constraint_suite.passed;
    total_failed += constraint_suite.failed;

    // Test Suite 5: Multiple Constraints
    let mut multiple_constraints_suite = Phase4TestSuite::new("Multiple Constraints".to_string());

    multiple_constraints_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let alpha_constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };
        let length_constraint = Constraint::ValueConstraint(Box::new(Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        }));
        let constraint_type = create_constraint_type(
            Type::string(Span::default()),
            vec![alpha_constraint, length_constraint],
        );
        let valid_value = Value::string("Hello".to_string(), Span::default());
        let result = evaluator.validate_value(&valid_value, &constraint_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    multiple_constraints_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let alpha_constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };
        let length_constraint = Constraint::ValueConstraint(Box::new(Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        }));
        let constraint_type = create_constraint_type(
            Type::string(Span::default()),
            vec![alpha_constraint, length_constraint],
        );
        let invalid_value = Value::string("Hello123".to_string(), Span::default());
        let result = evaluator.validate_value(&invalid_value, &constraint_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    multiple_constraints_suite.run();
    total_passed += multiple_constraints_suite.passed;
    total_failed += multiple_constraints_suite.failed;

    // Test Suite 6: Error Handling
    let mut error_handling_suite = Phase4TestSuite::new("Error Handling".to_string());

    error_handling_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let invalid_regex_constraint = Constraint::PatternConstraint {
            pattern: "[invalid".to_string(),
            regex: true,
        };
        let constraint_type = create_constraint_type(
            Type::string(Span::default()),
            vec![invalid_regex_constraint],
        );
        let test_value = Value::string("test".to_string(), Span::default());
        let result = evaluator.validate_value(&test_value, &constraint_type);
        assert!(result.is_err());
        Ok(())
    });

    error_handling_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
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
        let constraint_type =
            create_constraint_type(Type::integer(Span::default()), vec![range_constraint]);
        let test_value = Value::integer(50, Span::default());
        let result = evaluator.validate_value(&test_value, &constraint_type)?;
        assert!(matches!(result, ValidationResult::CannotValidate(_)));
        Ok(())
    });

    error_handling_suite.run();
    total_passed += error_handling_suite.passed;
    total_failed += error_handling_suite.failed;

    // Test Suite 7: Performance and Caching
    let mut performance_suite = Phase4TestSuite::new("Performance and Caching".to_string());

    performance_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
        let email_constraint = Constraint::PatternConstraint {
            pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![email_constraint]);
        let email_value = Value::string("user@example.com".to_string(), Span::default());

        // First validation (compiles regex)
        let start = Instant::now();
        let result1 = evaluator.validate_value(&email_value, &constraint_type)?;
        let first_duration = start.elapsed();
        assert_eq!(result1, ValidationResult::Valid);

        // Second validation (uses cached regex)
        let start = Instant::now();
        let result2 = evaluator.validate_value(&email_value, &constraint_type)?;
        let second_duration = start.elapsed();
        assert_eq!(result2, ValidationResult::Valid);

        // Second validation should be faster due to regex caching
        assert!(second_duration <= first_duration);
        Ok(())
    });

    performance_suite.add_test(|| {
        let mut evaluator = Evaluator::new();
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
        Ok(())
    });

    performance_suite.run();
    total_passed += performance_suite.passed;
    total_failed += performance_suite.failed;

    // Test Suite 8: End-to-End Pipeline
    let mut e2e_suite = Phase4TestSuite::new("End-to-End Pipeline".to_string());

    e2e_suite.add_test(|| {
        // Test complete pipeline: parse -> extract type -> validate
        let source = "type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");";
        let program = parse_program(source)?;

        let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
            type_alias.type_.clone()
        } else {
            panic!("Expected type alias declaration");
        };

        let mut evaluator = Evaluator::new();
        let valid_email = Value::string("user@example.com".to_string(), Span::default());
        let result = evaluator.validate_value(&valid_email, &constraint_type)?;
        assert_eq!(result, ValidationResult::Valid);
        Ok(())
    });

    e2e_suite.add_test(|| {
        // Test complete pipeline with invalid data
        let source = "type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");";
        let program = parse_program(source)?;

        let constraint_type = if let Some(type_alias) = program.declarations[0].as_type_alias() {
            type_alias.type_.clone()
        } else {
            panic!("Expected type alias declaration");
        };

        let mut evaluator = Evaluator::new();
        let invalid_email = Value::string("invalid-email".to_string(), Span::default());
        let result = evaluator.validate_value(&invalid_email, &constraint_type)?;
        assert!(matches!(result, ValidationResult::Invalid(_)));
        Ok(())
    });

    e2e_suite.run();
    total_passed += e2e_suite.passed;
    total_failed += e2e_suite.failed;

    // Final Summary
    let total_duration = start.elapsed();
    println!("=== Phase 4 Test Summary ===");
    println!("Total Tests: {}", total_passed + total_failed);
    println!("Passed: {} ✅", total_passed);
    println!("Failed: {} ❌", total_failed);
    println!(
        "Success Rate: {:.1}%",
        (total_passed as f64 / (total_passed + total_failed) as f64) * 100.0
    );
    println!("Total Duration: {:?}", total_duration);
    println!();

    if total_failed == 0 {
        println!("🎉 All Phase 4 tests passed! Constraint-based validation pipeline is working correctly.");
        Ok(())
    } else {
        println!("⚠️  Some Phase 4 tests failed. Please review the failures above.");
        Err(ligature_ast::AstError::InternalError {
            message: format!("{} tests failed", total_failed),
            span: Span::default(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_phase4_integration() -> AstResult<()> {
        // Run a subset of the integration tests
        let mut evaluator = Evaluator::new();

        // Test basic validation
        let int_type = Type::integer(Span::default());
        let int_value = Value::integer(42, Span::default());
        let result = evaluator.validate_value(&int_value, &int_type)?;
        assert_eq!(result, ValidationResult::Valid);

        // Test pattern constraint validation
        let email_constraint = Constraint::PatternConstraint {
            pattern: "^[^@]+@[^@]+\\.[^@]+$".to_string(),
            regex: true,
        };
        let constraint_type =
            create_constraint_type(Type::string(Span::default()), vec![email_constraint]);
        let valid_email = Value::string("user@example.com".to_string(), Span::default());
        let result = evaluator.validate_value(&valid_email, &constraint_type)?;
        assert_eq!(result, ValidationResult::Valid);

        Ok(())
    }
}
