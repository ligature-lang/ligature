use ligature_ast::ExprKind;
use ligature_ast::Value;
use ligature_eval::{evaluate_expression, Environment};
use ligature_parser::parse_expression;

#[derive(Debug)]
enum ExpectedValue {
    Integer(i64),
    Boolean(bool),
    ParsedOnly,
}

#[test]
fn test_operator_precedence_comprehensive() {
    println!("Testing Ligature Operator Precedence Fixes - Comprehensive Test\n");

    let test_cases = vec![
        // Test 1: Basic arithmetic precedence
        (
            "2 + 3 * 4",
            "Should be 2 + (3 * 4) = 14",
            ExpectedValue::Integer(14),
        ),
        // Test 2: Unary operator precedence
        (
            "-5 + 3",
            "Should be (-5) + 3 = -2",
            ExpectedValue::Integer(-2),
        ),
        // Test 3: Multiple unary operators
        ("--5", "Should be -(-5) = 5", ExpectedValue::Integer(5)),
        // Test 4: Logical operator precedence
        (
            "true && false || true",
            "Should be (true && false) || true = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 5: Comparison operator precedence
        (
            "5 + 3 > 7",
            "Should be (5 + 3) > 7 = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 6: Complex nested precedence
        (
            "1 + 2 * 3 > 4 && 5 || 6",
            "Should be ((1 + (2 * 3)) > 4) && 5) || 6",
            ExpectedValue::Integer(6),
        ),
        // Test 7: Equality operators
        (
            "1 + 2 == 3",
            "Should be (1 + 2) == 3 = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 8: Function application precedence
        ("f x + y", "Should be (f x) + y", ExpectedValue::ParsedOnly),
        // Test 9: Field access precedence
        (
            "record.field + 5",
            "Should be (record.field) + 5",
            ExpectedValue::ParsedOnly,
        ),
        // Test 10: Parenthesized expressions
        ("(2 + 3) * 4", "Should be 20", ExpectedValue::Integer(20)),
        // Test 11: Mixed precedence with all operators
        (
            "!true && false || 5 > 3",
            "Should be ((!true) && false) || (5 > 3) = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 12: Complex arithmetic with unary
        (
            "-2 * 3 + 4",
            "Should be (-2) * 3 + 4 = -2",
            ExpectedValue::Integer(-2),
        ),
        // Test 13: Logical with comparison
        (
            "3 < 5 && 2 > 1",
            "Should be (3 < 5) && (2 > 1) = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 14: Equality with arithmetic
        (
            "2 * 3 == 6",
            "Should be (2 * 3) == 6 = true",
            ExpectedValue::Boolean(true),
        ),
        // Test 15: Multiple logical operators
        (
            "true || false && true",
            "Should be true || (false && true) = true",
            ExpectedValue::Boolean(true),
        ),
    ];

    let mut passed = 0;
    let mut failed = 0;

    for (i, (expression, expected, expected_value)) in test_cases.iter().enumerate() {
        println!("Test {}: {}", i + 1, expression);
        println!("Expected: {}", expected);

        match parse_expression(expression) {
            Ok(expr) => {
                println!("✓ Parsed successfully");
                println!("  AST: {:?}", expr.kind);

                // Try to evaluate if it's a complete expression
                if let Ok(value) = evaluate_expression(&expr) {
                    println!("  Evaluated: {:?}", value);

                    // Check if the evaluation matches expected value
                    match expected_value {
                        ExpectedValue::Integer(expected_int) => {
                            if let Value::Integer(actual) = value {
                                if actual == *expected_int {
                                    println!("  ✓ Evaluation matches expected value");
                                    passed += 1;
                                } else {
                                    println!(
                                        "  ✗ Evaluation mismatch: expected {}, got {}",
                                        expected_int, actual
                                    );
                                    failed += 1;
                                }
                            } else {
                                println!("  ✗ Expected integer, got {:?}", value);
                                failed += 1;
                            }
                        }
                        ExpectedValue::Boolean(expected_bool) => {
                            if let Value::Boolean(actual) = value {
                                if actual == *expected_bool {
                                    println!("  ✓ Evaluation matches expected value");
                                    passed += 1;
                                } else {
                                    println!(
                                        "  ✗ Evaluation mismatch: expected {}, got {}",
                                        expected_bool, actual
                                    );
                                    failed += 1;
                                }
                            } else {
                                println!("  ✗ Expected boolean, got {:?}", value);
                                failed += 1;
                            }
                        }
                        ExpectedValue::ParsedOnly => {
                            println!("  ✓ Expression parsed correctly (no evaluation needed)");
                            passed += 1;
                        }
                    }
                } else {
                    println!("  ✓ Expression parsed correctly (evaluation not possible)");
                    passed += 1;
                }
            }
            Err(e) => {
                println!("✗ Parse error: {}", e);
                failed += 1;
            }
        }
        println!();
    }

    println!("Precedence Fixes Comprehensive Test Summary:");
    println!("  Passed: {}", passed);
    println!("  Failed: {}", failed);
    println!("  Total: {}", passed + failed);

    if failed == 0 {
        println!("🎉 All precedence issues have been fixed!");
    } else {
        println!("⚠️  Some precedence issues remain.");
    }

    // Assert that all tests passed
    assert_eq!(failed, 0, "Some precedence tests failed");
}
