//! Specification compliance differential tests.
//! 
//! These tests verify that the Rust implementation correctly
//! follows the formal specification defined in Lean.

use crate::differential::*;

#[test]
fn test_literal_compliance() {
    // Test that literals are handled according to the specification
    let test_cases = vec![
        "42",
        "\"hello\"",
        "true",
        "false",
        "()",
        "3.14",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_arithmetic_compliance() {
    // Test that arithmetic operations follow the specification
    let test_cases = vec![
        "1 + 2",
        "5 - 3",
        "4 * 3",
        "10 / 2",
        "(2 + 3) * 4",
        "1 + 2 + 3",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_comparison_compliance() {
    // Test that comparison operations follow the specification
    let test_cases = vec![
        "5 > 3",
        "3 < 5",
        "5 == 5",
        "5 != 3",
        "5 >= 3",
        "3 <= 5",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_logical_compliance() {
    // Test that logical operations follow the specification
    let test_cases = vec![
        "true && true",
        "true && false",
        "false && true",
        "false && false",
        "true || true",
        "true || false",
        "false || true",
        "false || false",
        "!true",
        "!false",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_conditional_compliance() {
    // Test that conditional expressions follow the specification
    let test_cases = vec![
        "if true then 42 else 0",
        "if false then 42 else 0",
        "if 5 > 3 then \"yes\" else \"no\"",
        "if 3 > 5 then \"yes\" else \"no\"",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_let_expression_compliance() {
    // Test that let expressions follow the specification
    let test_cases = vec![
        "let x = 5 in x * 2",
        "let x = 3 in let y = 4 in x + y",
        "let x = 10 in let y = 5 in x / y",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_function_compliance() {
    // Test that function definitions and applications follow the specification
    let test_cases = vec![
        "\\x -> x + 1",
        "(\\x y -> x + y) 5 3",
        "let add = \\x y -> x + y in add 10 20",
        "let double = \\x -> x * 2 in double 7",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_record_compliance() {
    // Test that record construction and field access follow the specification
    let test_cases = vec![
        "{ name = \"Alice\", age = 30 }",
        "let user = { name = \"Bob\", age = 25 } in user.name",
        "let user = { name = \"Charlie\", age = 35 } in user.age",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_list_compliance() {
    // Test that list construction follows the specification
    let test_cases = vec![
        "[1, 2, 3]",
        "[]",
        "[true, false, true]",
        "[\"a\", \"b\", \"c\"]",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_pattern_matching_compliance() {
    // Test that pattern matching follows the specification
    let test_cases = vec![
        "match 1 { 1 => \"one\", _ => \"other\" }",
        "match 2 { 1 => \"one\", _ => \"other\" }",
        "match true { true => 1, false => 0 }",
        "match false { true => 1, false => 0 }",
    ];
    
    for test_case in test_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_type_annotation_compliance() {
    // Test that type annotations follow the specification
    let test_cases = vec![
        "let x: Integer = 42",
        "let y: String = \"hello\"",
        "let z: Boolean = true",
        "let f: Integer -> Integer = \\x -> x + 1",
    ];
    
    for test_case in test_cases {
        let result = run_type_check_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run type check differential test for: {}", test_case);
        assert!(result.unwrap(), "Type check differential test failed for: {}", test_case);
    }
}

#[test]
fn test_error_handling_compliance() {
    // Test that error handling follows the specification
    let error_cases = vec![
        "1 + \"hello\"",  // Type mismatch
        "true && 42",     // Type mismatch
        "undefined_var",  // Undefined variable
        "1 / 0",         // Division by zero
    ];
    
    for test_case in error_cases {
        let result = run_differential_test(test_case);
        // These should all fail, but the failure should be consistent with the spec
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        // Note: We might need to adjust this based on how the spec handles errors
    }
}

#[test]
fn test_termination_compliance() {
    // Test that evaluation terminates according to the specification
    let termination_cases = vec![
        "let factorial = \\n -> if n <= 1 then 1 else n * (factorial (n - 1)) in factorial 5",
        "let length = \\list -> match list { [] => 0, [head, ...tail] => 1 + (length tail) } in length [1, 2, 3]",
    ];
    
    for test_case in termination_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_complex_expression_compliance() {
    // Test that complex expressions follow the specification
    let complex_cases = vec![
        "let add = \\x y -> x + y in let multiply = \\x y -> x * y in add (multiply 2 3) 4",
        "let max = \\a b -> if a > b then a else b in max 10 5",
        "let user = { name = \"Alice\", age = 30 } in let greet = \\user -> \"Hello, \" ++ user.name in greet user",
    ];
    
    for test_case in complex_cases {
        let result = run_differential_test(test_case);
        assert!(result.is_ok(), "Failed to run differential test for: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for: {}", test_case);
    }
}

#[test]
fn test_specification_extraction() {
    // Test that we can extract test cases from the specification
    let test_cases = extract_test_cases_from_spec();
    assert!(!test_cases.is_empty(), "Should extract test cases from specification");
    
    for test_case in test_cases {
        let result = run_differential_test(&test_case);
        assert!(result.is_ok(), "Failed to run differential test for extracted case: {}", test_case);
        assert!(result.unwrap(), "Differential test failed for extracted case: {}", test_case);
    }
} 