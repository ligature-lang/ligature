use ligature_parser::parse_expression;

fn main() {
    println!("Testing Ligature Operator Precedence Fixes\n");

    let test_cases = vec![
        // Test 1: Basic arithmetic precedence
        ("2 + 3 * 4", "Should be 2 + (3 * 4) = 14"),
        // Test 2: Unary operator precedence
        ("-5 + 3", "Should be (-5) + 3 = -2"),
        // Test 3: Multiple unary operators
        ("--5", "Should be -(-5) = 5"),
        // Test 4: Logical operator precedence
        (
            "true && false || true",
            "Should be (true && false) || true = true",
        ),
        // Test 5: Comparison operator precedence
        ("5 + 3 > 7", "Should be (5 + 3) > 7 = true"),
        // Test 6: Complex nested precedence
        (
            "1 + 2 * 3 > 4 && 5 || 6",
            "Should be ((1 + (2 * 3)) > 4) && 5) || 6",
        ),
        // Test 7: Equality operators
        ("1 + 2 == 3", "Should be (1 + 2) == 3 = true"),
        // Test 8: Function application precedence
        ("f x + y", "Should be (f x) + y"),
        // Test 9: Field access precedence
        ("record.field + 5", "Should be (record.field) + 5"),
        // Test 10: Parenthesized expressions
        ("(2 + 3) * 4", "Should be 20"),
    ];

    let mut passed = 0;
    let mut failed = 0;

    for (i, (expression, expected)) in test_cases.iter().enumerate() {
        println!("Test {}: {}", i + 1, expression);
        println!("Expected: {expected}");

        match parse_expression(expression) {
            Ok(expr) => {
                println!("✓ Parsed successfully");
                println!("  AST: {:?}", expr.kind);
                passed += 1;
            }
            Err(e) => {
                println!("✗ Parse error: {e}");
                failed += 1;
            }
        }
        println!();
    }

    println!("Precedence Fixes Summary:");
    println!("  Passed: {passed}");
    println!("  Failed: {failed}");
    println!("  Total: {}", passed + failed);

    if failed == 0 {
        println!("🎉 All precedence issues have been fixed!");
    } else {
        println!("⚠️  Some precedence issues remain.");
    }
}
