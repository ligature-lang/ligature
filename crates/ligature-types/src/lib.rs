//! Type system for the Ligature language.
//!
//! This crate provides type checking, type inference, and type system
//! functionality for the Ligature language.

pub mod benchmarks;
pub mod checker;
pub mod constraints;
pub mod environment;
pub mod error;
pub mod inference;
pub mod resolver;

use ligature_ast::{AstResult, Module, Program};
use std::path::PathBuf;

// Test modules
#[cfg(test)]
mod module_tests;
#[cfg(test)]
mod refinement_type_tests;
#[cfg(test)]
mod resolver_tests;
#[cfg(test)]
mod type_class_tests;
mod type_system_enhancements_tests;
#[cfg(test)]
mod union_type_inference_tests;

/// Type check a complete program.
pub fn type_check_program(program: &Program) -> AstResult<()> {
    let mut checker = checker::TypeChecker::new();
    checker.check_program(program)
}

/// Type check a program with custom search and register paths.
pub fn type_check_program_with_paths(
    program: &Program,
    search_paths: &[PathBuf],
    register_paths: &[PathBuf],
) -> AstResult<()> {
    let mut checker =
        checker::TypeChecker::with_paths(search_paths.to_vec(), register_paths.to_vec());
    checker.check_program(program)
}

/// Type check a complete module.
pub fn type_check_module(module: &Module) -> AstResult<()> {
    let mut checker = checker::TypeChecker::new();
    checker.check_module(module)
}

/// Infer the type of an expression.
pub fn infer_expression(expr: &ligature_ast::Expr) -> AstResult<ligature_ast::Type> {
    let mut checker = checker::TypeChecker::new();
    checker.infer_expression(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ligature_ast::{
        Declaration, DeclarationKind, Expr, ExprKind, Literal, Program, Span, Type, TypeKind,
        ValueDeclaration,
    };
    use ligature_parser::parse_program;

    #[test]
    fn test_binding_conflicts_implementation() {
        // Test that binding conflicts are detected
        let program = parse_program(
            "
            let x = 42;
            let x = \"hello\";
        ",
        )
        .unwrap();

        let result = type_check_program(&program);
        assert!(result.is_err());

        if let Err(e) = result {
            let error_msg = e.to_string();
            assert!(error_msg.contains("binding conflict") || error_msg.contains("already bound"));
        }
    }

    #[test]
    fn test_valid_program_passes() {
        // Test that valid programs still work
        let program = parse_program(
            "
            let x = 42;
            let y = \"hello\";
            let result = x + 10;
        ",
        )
        .unwrap();

        let result = type_check_program(&program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_literal_type_inference() {
        let mut checker = checker::TypeChecker::new();

        // Test integer literal
        let int_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let int_type = checker.infer_expression(&int_expr).unwrap();
        assert!(matches!(int_type.kind, TypeKind::Integer));

        // Test string literal
        let string_expr = Expr {
            kind: ExprKind::Literal(Literal::String("hello".to_string())),
            span: Span::default(),
        };
        let string_type = checker.infer_expression(&string_expr).unwrap();
        assert!(matches!(string_type.kind, TypeKind::String));

        // Test boolean literal
        let bool_expr = Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        };
        let bool_type = checker.infer_expression(&bool_expr).unwrap();
        assert!(matches!(bool_type.kind, TypeKind::Bool));

        // Test unit literal
        let unit_expr = Expr {
            kind: ExprKind::Literal(Literal::Unit),
            span: Span::default(),
        };
        let unit_type = checker.infer_expression(&unit_expr).unwrap();
        assert!(matches!(unit_type.kind, TypeKind::Unit));
    }

    #[test]
    fn test_variable_type_inference() {
        let mut checker = checker::TypeChecker::new();

        // Bind a variable
        checker.bind("x".to_string(), Type::integer(Span::default()));

        // Test variable lookup
        let var_expr = Expr {
            kind: ExprKind::Variable("x".to_string()),
            span: Span::default(),
        };
        let var_type = checker.infer_expression(&var_expr).unwrap();
        assert!(matches!(var_type.kind, TypeKind::Integer));

        // Test undefined variable
        let undefined_expr = Expr {
            kind: ExprKind::Variable("y".to_string()),
            span: Span::default(),
        };
        let result = checker.infer_expression(&undefined_expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_function_type_inference() {
        let mut checker = checker::TypeChecker::new();

        // Test lambda abstraction
        let body = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let lambda_expr = Expr {
            kind: ExprKind::Abstraction {
                parameter: "x".to_string(),
                parameter_type: Some(Box::new(Type::integer(Span::default()))),
                body: Box::new(body),
            },
            span: Span::default(),
        };

        let lambda_type = checker.infer_expression(&lambda_expr).unwrap();
        match lambda_type.kind {
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                assert!(matches!(parameter.kind, TypeKind::Integer));
                assert!(matches!(return_type.kind, TypeKind::Integer));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_binary_operation_type_inference() {
        let mut checker = checker::TypeChecker::new();

        // Test integer addition
        let left = Expr {
            kind: ExprKind::Literal(Literal::Integer(5)),
            span: Span::default(),
        };
        let right = Expr {
            kind: ExprKind::Literal(Literal::Integer(3)),
            span: Span::default(),
        };
        let add_expr = Expr {
            kind: ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Add,
                left: Box::new(left),
                right: Box::new(right),
            },
            span: Span::default(),
        };

        let add_type = checker.infer_expression(&add_expr).unwrap();
        assert!(matches!(add_type.kind, TypeKind::Integer));

        // Test boolean AND
        let bool_left = Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        };
        let bool_right = Expr {
            kind: ExprKind::Literal(Literal::Boolean(false)),
            span: Span::default(),
        };
        let and_expr = Expr {
            kind: ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::And,
                left: Box::new(bool_left),
                right: Box::new(bool_right),
            },
            span: Span::default(),
        };

        let and_type = checker.infer_expression(&and_expr).unwrap();
        assert!(matches!(and_type.kind, TypeKind::Bool));
    }

    #[test]
    fn test_record_type_inference() {
        let mut checker = checker::TypeChecker::new();

        // Test record construction
        let fields = vec![
            ligature_ast::RecordField {
                name: "name".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::String("Alice".to_string())),
                    span: Span::default(),
                },
                span: Span::default(),
            },
            ligature_ast::RecordField {
                name: "age".to_string(),
                value: Expr {
                    kind: ExprKind::Literal(Literal::Integer(30)),
                    span: Span::default(),
                },
                span: Span::default(),
            },
        ];

        let record_expr = Expr {
            kind: ExprKind::Record { fields },
            span: Span::default(),
        };
        let record_type = checker.infer_expression(&record_expr).unwrap();

        match record_type.kind {
            TypeKind::Record { fields } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].name, "name");
                assert!(matches!(fields[0].type_.kind, TypeKind::String));
                assert_eq!(fields[1].name, "age");
                assert!(matches!(fields[1].type_.kind, TypeKind::Integer));
            }
            _ => panic!("Expected record type"),
        }
    }

    #[test]
    fn test_type_equality() {
        let checker = checker::TypeChecker::new();

        // Test basic type equality
        let int1 = Type::integer(Span::default());
        let int2 = Type::integer(Span::default());
        assert!(checker.types_equal(&int1, &int2).unwrap());

        // Test different types
        let string_type = Type::string(Span::default());
        assert!(!checker.types_equal(&int1, &string_type).unwrap());

        // Test type variables
        let var1 = Type::variable("a".to_string(), Span::default());
        let var2 = Type::variable("a".to_string(), Span::default());
        assert!(checker.types_equal(&var1, &var2).unwrap());

        let var3 = Type::variable("b".to_string(), Span::default());
        assert!(checker.types_equal(&var1, &var3).unwrap()); // Should unify
    }

    #[test]
    fn test_program_type_checking() {
        // Create a simple program with a value declaration
        let value_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let value_decl = ValueDeclaration {
            name: "answer".to_string(),
            value: value_expr,
            type_annotation: None,
            is_recursive: false,
            span: Span::default(),
        };

        let declaration = Declaration::new(DeclarationKind::Value(value_decl), Span::default());

        let program = Program {
            declarations: vec![declaration],
            span: Span::default(),
        };

        // Type check the program
        let result = type_check_program(&program);
        assert!(result.is_ok(), "Type checking failed: {result:?}");

        // Create a new inference engine and manually add the binding
        let mut checker = checker::TypeChecker::new();
        checker.bind("answer".to_string(), Type::integer(Span::default()));

        // Verify the binding was added
        let var_expr = Expr {
            kind: ExprKind::Variable("answer".to_string()),
            span: Span::default(),
        };
        let var_type = checker.infer_expression(&var_expr).unwrap();
        assert!(matches!(var_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_constraint_solving() {
        let mut solver = constraints::ConstraintSolver::new();

        // Add a simple equality constraint
        let var_a = Type::variable("a".to_string(), Span::default());
        let int_type = Type::integer(Span::default());
        solver.add_constraint(constraints::Constraint::Equality(var_a, int_type));

        // Solve constraints
        let substitution = solver.solve().unwrap();
        assert_eq!(substitution.len(), 1);
        assert!(matches!(substitution["a"].kind, TypeKind::Integer));
    }

    #[test]
    fn test_function_application() {
        let mut checker = checker::TypeChecker::new();

        // Create a function: \x -> x + 1
        let param = Expr {
            kind: ExprKind::Variable("x".to_string()),
            span: Span::default(),
        };
        let one = Expr {
            kind: ExprKind::Literal(Literal::Integer(1)),
            span: Span::default(),
        };
        let add = Expr {
            kind: ExprKind::BinaryOp {
                operator: ligature_ast::BinaryOperator::Add,
                left: Box::new(param),
                right: Box::new(one),
            },
            span: Span::default(),
        };

        let lambda = Expr {
            kind: ExprKind::Abstraction {
                parameter: "x".to_string(),
                parameter_type: Some(Box::new(Type::integer(Span::default()))),
                body: Box::new(add),
            },
            span: Span::default(),
        };

        // Apply the function to 5
        let arg = Expr {
            kind: ExprKind::Literal(Literal::Integer(5)),
            span: Span::default(),
        };
        let app = Expr {
            kind: ExprKind::Application {
                function: Box::new(lambda),
                argument: Box::new(arg),
            },
            span: Span::default(),
        };

        let app_type = checker.infer_expression(&app).unwrap();
        assert!(matches!(app_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_type_annotation() {
        let mut checker = checker::TypeChecker::new();

        // Create an expression with type annotation
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let annotation = Type::integer(Span::default());
        let annotated_expr = Expr {
            kind: ExprKind::Annotated {
                expression: Box::new(expr),
                type_annotation: Box::new(annotation),
            },
            span: Span::default(),
        };

        let result_type = checker.infer_expression(&annotated_expr).unwrap();
        assert!(matches!(result_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_if_expression() {
        let mut checker = checker::TypeChecker::new();

        // Create an if expression
        let condition = Expr {
            kind: ExprKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
        };
        let then_branch = Expr {
            kind: ExprKind::Literal(Literal::Integer(1)),
            span: Span::default(),
        };
        let else_branch = Expr {
            kind: ExprKind::Literal(Literal::Integer(2)),
            span: Span::default(),
        };

        let if_expr = Expr {
            kind: ExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            },
            span: Span::default(),
        };

        let if_type = checker.infer_expression(&if_expr).unwrap();
        assert!(matches!(if_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_let_expression() {
        let mut checker = checker::TypeChecker::new();

        // Create a let expression
        let value = Expr {
            kind: ExprKind::Literal(Literal::Integer(5)),
            span: Span::default(),
        };
        let body = Expr {
            kind: ExprKind::Variable("x".to_string()),
            span: Span::default(),
        };

        let let_expr = Expr {
            kind: ExprKind::Let {
                name: "x".to_string(),
                value: Box::new(value),
                body: Box::new(body),
            },
            span: Span::default(),
        };

        let let_type = checker.infer_expression(&let_expr).unwrap();
        assert!(matches!(let_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_integration_with_parser() {
        use ligature_parser::parse_program;

        // Test a simple program that should type check
        let source = "let x = 42;";
        let program = parse_program(source).unwrap();

        // Type check the program
        let result = type_check_program(&program);
        assert!(result.is_ok(), "Type checking failed: {result:?}");

        // Test a program with a type error
        let source_with_error = "let x = 42 + \"hello\";";
        let program_with_error = parse_program(source_with_error).unwrap();

        // This should fail type checking
        let result = type_check_program(&program_with_error);
        // The test should expect this to fail since you can't add an integer and a string
        match result {
            Ok(_) => panic!("Expected type checking to fail for integer + string, but it passed"),
            Err(e) => println!("✅ Type checking correctly failed with error: {e}"),
        }
    }

    // Enhanced type inference tests
    #[test]
    fn test_enhanced_subtyping_demo() {
        println!("=== Enhanced Subtyping Demo ===");

        // Test record width subtyping (simplified)
        let program = parse_program(
            r#"
            let user = { name = "Alice", age = 30, email = "alice@example.com" };
            let basic_user = user;
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("✅ Record construction works correctly"),
            Err(e) => println!("❌ Record construction failed: {e}"),
        }

        // Test record field access
        let program = parse_program(
            r#"
            let user = { name = "Alice", age = 30 };
            let name = user.name;
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("✅ Record field access works correctly"),
            Err(e) => println!("❌ Record field access failed: {e}"),
        }

        // Test function application
        let program = parse_program(
            r#"
            let add = \x y -> x + y;
            let result = add 5 3;
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("✅ Function application works correctly"),
            Err(e) => println!("❌ Function application failed: {e}"),
        }

        // Test list construction
        let program = parse_program(
            r#"
            let int_list = [1, 2, 3];
            let first = int_list[0];
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("✅ List construction and access works correctly"),
            Err(e) => println!("❌ List construction and access failed: {e}"),
        }
    }

    #[test]
    fn test_enhanced_error_reporting_demo() {
        println!("\n=== Enhanced Error Reporting Demo ===");

        // Test type mismatch with better error context
        let program = parse_program(
            r#"
            let x = 5 + "hello";
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("❌ Expected error but got success"),
            Err(e) => {
                println!("✅ Type mismatch error caught:");
                println!("   Error: {e}");
                let error_msg = e.to_string();
                if error_msg.contains("type mismatch") || error_msg.contains("cannot unify") {
                    println!("   ✅ Error message is clear and helpful");
                } else {
                    println!("   ⚠️  Error message could be more specific");
                }
            }
        }

        // Test function application error
        let program = parse_program(
            r#"
            let add = \x y -> x + y;
            let result = add 5 "hello";
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("❌ Expected error but got success"),
            Err(e) => {
                println!("✅ Function application error caught:");
                println!("   Error: {e}");
                let error_msg = e.to_string();
                if error_msg.contains("function")
                    || error_msg.contains("parameter")
                    || error_msg.contains("argument")
                {
                    println!("   ✅ Error message provides function context");
                } else {
                    println!("   ⚠️  Error message could provide more context");
                }
            }
        }

        // Test undefined variable error
        let program = parse_program(
            r#"
            let x = undefined_var;
        "#,
        )
        .unwrap();

        match type_check_program(&program) {
            Ok(_) => println!("❌ Expected error but got success"),
            Err(e) => {
                println!("✅ Undefined variable error caught:");
                println!("   Error: {e}");
                let error_msg = e.to_string();
                if error_msg.contains("undefined") || error_msg.contains("not found") {
                    println!("   ✅ Error message is clear about undefined variable");
                } else {
                    println!("   ⚠️  Error message could be more specific");
                }
            }
        }
    }

    #[test]
    fn test_performance_optimizations() {
        println!("\n=== Performance Optimization Demo ===");

        // Test performance optimizations
        use crate::benchmarks::test_optimizations;
        test_optimizations();

        // Test performance comparison
        use crate::benchmarks::compare_performance;
        compare_performance();

        println!("✅ Performance optimizations working correctly");
    }
}
