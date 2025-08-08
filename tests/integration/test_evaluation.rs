use ligature_ast::{BinaryOperator, Expr, ExprKind, Literal, Span, UnaryOperator};
use ligature_eval::{evaluate_expression, evaluate_program};
use ligature_parser::parse_program;

fn main() {
    println!("🚀 Running Evaluation Engine Integration Tests\n");

    let mut passed = 0;
    let mut failed = 0;

    // Test 1: Basic literal evaluation
    println!("1. Testing basic literal evaluation...");
    if test_basic_literal_evaluation() {
        println!("   ✅ Basic literal evaluation passed");
        passed += 1;
    } else {
        println!("   ❌ Basic literal evaluation failed");
        failed += 1;
    }

    // Test 2: Arithmetic operations
    println!("2. Testing arithmetic operations...");
    if test_arithmetic_operations() {
        println!("   ✅ Arithmetic operations passed");
        passed += 1;
    } else {
        println!("   ❌ Arithmetic operations failed");
        failed += 1;
    }

    // Test 3: Comparison operations
    println!("3. Testing comparison operations...");
    if test_comparison_operations() {
        println!("   ✅ Comparison operations passed");
        passed += 1;
    } else {
        println!("   ❌ Comparison operations failed");
        failed += 1;
    }

    // Test 4: Logical operations
    println!("4. Testing logical operations...");
    if test_logical_operations() {
        println!("   ✅ Logical operations passed");
        passed += 1;
    } else {
        println!("   ❌ Logical operations failed");
        failed += 1;
    }

    // Test 5: Unary operations
    println!("5. Testing unary operations...");
    if test_unary_operations() {
        println!("   ✅ Unary operations passed");
        passed += 1;
    } else {
        println!("   ❌ Unary operations failed");
        failed += 1;
    }

    // Test 6: If expressions
    println!("6. Testing if expressions...");
    if test_if_expressions() {
        println!("   ✅ If expressions passed");
        passed += 1;
    } else {
        println!("   ❌ If expressions failed");
        failed += 1;
    }

    // Test 7: Let expressions
    println!("7. Testing let expressions...");
    if test_let_expressions() {
        println!("   ✅ Let expressions passed");
        passed += 1;
    } else {
        println!("   ❌ Let expressions failed");
        failed += 1;
    }

    // Test 8: Function application
    println!("8. Testing function application...");
    if test_function_application() {
        println!("   ✅ Function application passed");
        passed += 1;
    } else {
        println!("   ❌ Function application failed");
        failed += 1;
    }

    // Test 9: String concatenation
    println!("9. Testing string concatenation...");
    if test_string_concatenation() {
        println!("   ✅ String concatenation passed");
        passed += 1;
    } else {
        println!("   ❌ String concatenation failed");
        failed += 1;
    }

    // Test 10: Error handling
    println!("10. Testing error handling...");
    if test_error_handling() {
        println!("   ✅ Error handling passed");
        passed += 1;
    } else {
        println!("   ❌ Error handling failed");
        failed += 1;
    }

    // Test 11: Program evaluation
    println!("11. Testing program evaluation...");
    if test_program_evaluation() {
        println!("   ✅ Program evaluation passed");
        passed += 1;
    } else {
        println!("   ❌ Program evaluation failed");
        failed += 1;
    }

    // Test 12: Complex expressions
    println!("12. Testing complex expressions...");
    if test_complex_expressions() {
        println!("   ✅ Complex expressions passed");
        passed += 1;
    } else {
        println!("   ❌ Complex expressions failed");
        failed += 1;
    }

    println!("\n📊 Test Results:");
    println!("   Passed: {passed}");
    println!("   Failed: {failed}");
    println!("   Total:  {}", passed + failed);

    if failed == 0 {
        println!("\n🎉 All evaluation engine tests passed!");
    } else {
        println!("\n❌ Some tests failed. Please check the output above.");
    }
}

fn test_basic_literal_evaluation() -> bool {
    let test_cases = vec![
        (
            Expr {
                kind: ExprKind::Literal(Literal::Integer(42)),
                span: Span::default(),
            },
            Some(42),
            "integer literal",
        ),
        (
            Expr {
                kind: ExprKind::Literal(Literal::String("hello".to_string())),
                span: Span::default(),
            },
            None,
            "string literal",
        ),
        (
            Expr {
                kind: ExprKind::Literal(Literal::Boolean(true)),
                span: Span::default(),
            },
            None,
            "boolean literal",
        ),
        (
            Expr {
                kind: ExprKind::Literal(Literal::Unit),
                span: Span::default(),
            },
            None,
            "unit literal",
        ),
    ];

    for (expr, expected_int, description) in test_cases {
        match evaluate_expression(&expr) {
            Ok(value) => {
                if let Some(expected) = expected_int {
                    if value.as_integer() != Some(expected) {
                        println!("     Failed {description}: expected {expected}, got {value:?}",);
                        return false;
                    }
                } else {
                    // For non-integer literals, just check they evaluate successfully
                    if description == "string literal" && value.as_string() != Some("hello") {
                        println!("     Failed {description}: expected 'hello', got {value:?}",);
                        return false;
                    } else if description == "boolean literal" && value.as_boolean() != Some(true) {
                        println!("     Failed {description}: expected true, got {value:?}",);
                        return false;
                    } else if description == "unit literal" && !value.is_unit() {
                        println!("     Failed {description}: expected unit, got {value:?}",);
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Failed {description}: evaluation error: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_arithmetic_operations() -> bool {
    let test_cases = vec![
        (BinaryOperator::Add, 5, 3, 8, "addition"),
        (BinaryOperator::Subtract, 10, 4, 6, "subtraction"),
        (BinaryOperator::Multiply, 6, 7, 42, "multiplication"),
        (BinaryOperator::Divide, 15, 3, 5, "division"),
        (BinaryOperator::Modulo, 17, 5, 2, "modulo"),
    ];

    for (op, left, right, expected, description) in test_cases {
        let expr = Expr {
            kind: ExprKind::BinaryOp {
                operator: op,
                left: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(left)),
                    span: Span::default(),
                }),
                right: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(right)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };

        match evaluate_expression(&expr) {
            Ok(value) => {
                if value.as_integer() != Some(expected) {
                    println!("     Failed {description}: expected {expected}, got {value:?}",);
                    return false;
                }
            }
            Err(e) => {
                println!("     Failed {description}: evaluation error: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_comparison_operations() -> bool {
    let test_cases = vec![
        (BinaryOperator::Equal, 5, 5, true, "equality (true)"),
        (BinaryOperator::Equal, 5, 3, false, "equality (false)"),
        (BinaryOperator::NotEqual, 5, 3, true, "inequality (true)"),
        (BinaryOperator::NotEqual, 5, 5, false, "inequality (false)"),
        (BinaryOperator::LessThan, 3, 5, true, "less than (true)"),
        (BinaryOperator::LessThan, 5, 3, false, "less than (false)"),
        (
            BinaryOperator::GreaterThan,
            5,
            3,
            true,
            "greater than (true)",
        ),
        (
            BinaryOperator::GreaterThan,
            3,
            5,
            false,
            "greater than (false)",
        ),
    ];

    for (op, left, right, expected, description) in test_cases {
        let expr = Expr {
            kind: ExprKind::BinaryOp {
                operator: op,
                left: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(left)),
                    span: Span::default(),
                }),
                right: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(right)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };

        match evaluate_expression(&expr) {
            Ok(value) => {
                if value.as_boolean() != Some(expected) {
                    println!("     Failed {description}: expected {expected}, got {value:?}",);
                    return false;
                }
            }
            Err(e) => {
                println!("     Failed {description}: evaluation error: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_logical_operations() -> bool {
    let test_cases = vec![
        (BinaryOperator::And, true, true, true, "AND (true, true)"),
        (BinaryOperator::And, true, false, false, "AND (true, false)"),
        (BinaryOperator::And, false, true, false, "AND (false, true)"),
        (
            BinaryOperator::And,
            false,
            false,
            false,
            "AND (false, false)",
        ),
        (BinaryOperator::Or, true, true, true, "OR (true, true)"),
        (BinaryOperator::Or, true, false, true, "OR (true, false)"),
        (BinaryOperator::Or, false, true, true, "OR (false, true)"),
        (BinaryOperator::Or, false, false, false, "OR (false, false)"),
    ];

    for (op, left, right, expected, description) in test_cases {
        let expr = Expr {
            kind: ExprKind::BinaryOp {
                operator: op,
                left: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Boolean(left)),
                    span: Span::default(),
                }),
                right: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Boolean(right)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };

        match evaluate_expression(&expr) {
            Ok(value) => {
                if value.as_boolean() != Some(expected) {
                    println!("     Failed {description}: expected {expected}, got {value:?}",);
                    return false;
                }
            }
            Err(e) => {
                println!("     Failed {description}: evaluation error: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_unary_operations() -> bool {
    // Test integer negation
    let neg_expr = Expr {
        kind: ExprKind::UnaryOp {
            operator: UnaryOperator::Negate,
            operand: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&neg_expr) {
        Ok(value) => {
            if value.as_integer() != Some(-5) {
                println!("     Failed negation: expected -5, got {value:?}");
                return false;
            }
        }
        Err(e) => {
            println!("     Failed negation: evaluation error: {e:?}");
            return false;
        }
    }

    // Test logical NOT
    let not_expr = Expr {
        kind: ExprKind::UnaryOp {
            operator: UnaryOperator::Not,
            operand: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Boolean(true)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&not_expr) {
        Ok(value) => {
            if value.as_boolean() != Some(false) {
                println!("     Failed logical NOT: expected false, got {value:?}");
                return false;
            }
        }
        Err(e) => {
            println!("     Failed logical NOT: evaluation error: {e:?}");
            return false;
        }
    }

    true
}

fn test_if_expressions() -> bool {
    let test_cases = vec![
        (true, 42, 0, 42, "if with true condition"),
        (false, 42, 0, 0, "if with false condition"),
    ];

    for (condition, then_val, else_val, expected, description) in test_cases {
        let expr = Expr {
            kind: ExprKind::If {
                condition: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Boolean(condition)),
                    span: Span::default(),
                }),
                then_branch: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(then_val)),
                    span: Span::default(),
                }),
                else_branch: Box::new(Expr {
                    kind: ExprKind::Literal(Literal::Integer(else_val)),
                    span: Span::default(),
                }),
            },
            span: Span::default(),
        };

        match evaluate_expression(&expr) {
            Ok(value) => {
                if value.as_integer() != Some(expected) {
                    println!("     Failed {description}: expected {expected}, got {value:?}",);
                    return false;
                }
            }
            Err(e) => {
                println!("     Failed {description}: evaluation error: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_let_expressions() -> bool {
    let expr = Expr {
        kind: ExprKind::Let {
            name: "x".to_string(),
            value: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(42)),
                span: Span::default(),
            }),
            body: Box::new(Expr {
                kind: ExprKind::Variable("x".to_string()),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&expr) {
        Ok(value) => {
            if value.as_integer() != Some(42) {
                println!("     Failed let expression: expected 42, got {value:?}");
                return false;
            }
        }
        Err(e) => {
            println!("     Failed let expression: evaluation error: {e:?}");
            return false;
        }
    }

    true
}

fn test_function_application() -> bool {
    // Create a simple function: \x -> x + 1
    let function = Expr {
        kind: ExprKind::Abstraction {
            parameter: "x".to_string(),
            parameter_type: None,
            body: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Variable("x".to_string()),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(1)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    // Apply the function to 5
    let application = Expr {
        kind: ExprKind::Application {
            function: Box::new(function),
            argument: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&application) {
        Ok(value) => {
            if value.as_integer() != Some(6) {
                println!("     Failed function application: expected 6, got {value:?}",);
                return false;
            }
        }
        Err(e) => {
            println!("     Failed function application: evaluation error: {e:?}",);
            return false;
        }
    }

    true
}

fn test_string_concatenation() -> bool {
    let expr = Expr {
        kind: ExprKind::BinaryOp {
            operator: BinaryOperator::Concat,
            left: Box::new(Expr {
                kind: ExprKind::Literal(Literal::String("Hello, ".to_string())),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::String("World!".to_string())),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&expr) {
        Ok(value) => {
            if value.as_string() != Some("Hello, World!") {
                println!(
                    "     Failed string concatenation: expected 'Hello, World!', got {value:?}",
                );
                return false;
            }
        }
        Err(e) => {
            println!("     Failed string concatenation: evaluation error: {e:?}",);
            return false;
        }
    }

    true
}

fn test_error_handling() -> bool {
    // Test division by zero
    let div_expr = Expr {
        kind: ExprKind::BinaryOp {
            operator: BinaryOperator::Divide,
            left: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(5)),
                span: Span::default(),
            }),
            right: Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(0)),
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&div_expr) {
        Ok(_) => {
            println!("     Failed division by zero: expected error, got success");
            return false;
        }
        Err(_) => {
            // Expected error
        }
    }

    // Test undefined variable
    let var_expr = Expr {
        kind: ExprKind::Variable("undefined_var".to_string()),
        span: Span::default(),
    };

    match evaluate_expression(&var_expr) {
        Ok(_) => {
            println!("     Failed undefined variable: expected error, got success");
            return false;
        }
        Err(_) => {
            // Expected error
        }
    }

    true
}

fn test_program_evaluation() -> bool {
    let test_cases = vec![
        "let x = 42;",
        "let y = 10; let z = y + 5;",
        "let a = true; let b = false;",
    ];

    for source in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match evaluate_program(&program) {
                    Ok(value) => {
                        // Programs should return unit
                        if !value.is_unit() {
                            println!(
                                "     Failed program evaluation for '{source}': expected unit, \
                                 got {value:?}",
                            );
                            return false;
                        }
                    }
                    Err(e) => {
                        println!("     Failed program evaluation for '{source}': {e:?}");
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Failed to parse program '{source}': {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_complex_expressions() -> bool {
    // Test a complex expression: if (5 > 3) then (10 + 2) else (5 * 2)
    let expr = Expr {
        kind: ExprKind::If {
            condition: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::GreaterThan,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(5)),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(3)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
            then_branch: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Add,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(10)),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(2)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
            else_branch: Box::new(Expr {
                kind: ExprKind::BinaryOp {
                    operator: BinaryOperator::Multiply,
                    left: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(5)),
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: ExprKind::Literal(Literal::Integer(2)),
                        span: Span::default(),
                    }),
                },
                span: Span::default(),
            }),
        },
        span: Span::default(),
    };

    match evaluate_expression(&expr) {
        Ok(value) => {
            // 5 > 3 is true, so should evaluate to 10 + 2 = 12
            if value.as_integer() != Some(12) {
                println!("     Failed complex expression: expected 12, got {value:?}",);
                return false;
            }
        }
        Err(e) => {
            println!("     Failed complex expression: evaluation error: {e:?}");
            return false;
        }
    }

    true
}
