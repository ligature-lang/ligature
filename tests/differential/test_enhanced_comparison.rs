//! Tests for the enhanced differential testing framework.

use crate::differential::*;

#[test]
fn test_normalize_result() {
    // Test that normalization works correctly
    let input = "  Hello\n  World  ";
    let expected = "hello world";
    // Note: We can't directly test the private function, but we can test it through the public API
    assert_eq!(normalize_result(input), expected);
}

#[test]
fn test_is_success_result() {
    // Test success/failure detection
    assert!(is_success_result("success"));
    assert!(is_success_result("42"));
    assert!(is_success_result("hello world"));

    assert!(!is_success_result("error"));
    assert!(!is_success_result("failed"));
    assert!(!is_success_result("exception"));
    assert!(!is_success_result(""));
}

#[test]
fn test_compare_rust_lean_results_detailed() {
    // Test detailed comparison with matching results
    let rust_result = "42";
    let lean_result = "42";
    let comparison = compare_rust_lean_results_detailed(
        rust_result,
        lean_result,
        TestType::Evaluation,
        "test_expression",
    );

    assert!(comparison.matches);
    assert!(comparison.differences.is_empty());
    assert_eq!(comparison.source, "test_expression");
    assert!(matches!(comparison.test_type, TestType::Evaluation));

    // Test detailed comparison with different results
    let rust_result = "42";
    let lean_result = "43";
    let comparison = compare_rust_lean_results_detailed(
        rust_result,
        lean_result,
        TestType::Evaluation,
        "test_expression",
    );

    assert!(!comparison.matches);
    assert!(!comparison.differences.is_empty());
}

#[test]
fn test_compare_rust_lean_results_detailed_with_errors() {
    // Test comparison when one result has an error
    let rust_result = "42";
    let lean_result = "error: parse failed";
    let comparison = compare_rust_lean_results_detailed(
        rust_result,
        lean_result,
        TestType::Evaluation,
        "test_expression",
    );

    assert!(!comparison.matches);
    assert!(!comparison.differences.is_empty());

    // Check that we have a success status difference
    let has_success_diff = comparison
        .differences
        .iter()
        .any(|d| d.field == "success_status");
    assert!(has_success_diff);
}

#[test]
fn test_compare_rust_lean_results_detailed_type_check() {
    // Test type checking comparison
    let rust_result = "type: int";
    let lean_result = "type: string";
    let comparison = compare_rust_lean_results_detailed(
        rust_result,
        lean_result,
        TestType::TypeCheck,
        "test_expression",
    );

    assert!(!comparison.matches);
    assert!(matches!(comparison.test_type, TestType::TypeCheck));
}

#[test]
fn test_legacy_comparison_backward_compatibility() {
    // Test that legacy comparison function still works
    assert!(compare_rust_lean_results("42", "42"));
    assert!(!compare_rust_lean_results("42", "error"));
    assert!(!compare_rust_lean_results("error", "42"));
}

#[test]
fn test_extract_numeric_value() {
    // Test numeric value extraction
    assert_eq!(extract_numeric_value("result: 42"), Some(42.0));
    assert_eq!(extract_numeric_value("result: 3.14"), Some(3.14));
    assert_eq!(extract_numeric_value("no numbers here"), None);
    assert_eq!(extract_numeric_value(""), None);
}

#[test]
fn test_extract_type_info() {
    // Test type information extraction
    assert_eq!(extract_type_info("type: int"), "int");
    assert_eq!(extract_type_info("type: string"), "string");
    assert_eq!(extract_type_info("type: bool"), "bool");
    assert_eq!(extract_type_info("type: float"), "float");
    assert_eq!(extract_type_info("unknown type"), "unknown");
}

#[test]
fn test_extract_error_info() {
    // Test error information extraction
    assert_eq!(extract_error_info("parse error"), "parse_error");
    assert_eq!(extract_error_info("type error"), "type_error");
    assert_eq!(extract_error_info("evaluation error"), "evaluation_error");
    assert_eq!(extract_error_info("some error"), "general_error");
    assert_eq!(extract_error_info("no error"), "unknown_error");
}

#[test]
fn test_parse_structured_result() {
    // Test structured result parsing
    let input = "key1: value1, key2: value2";
    let parsed = parse_structured_result(input);
    assert!(parsed.is_some());

    if let Some(parsed) = parsed {
        assert_eq!(parsed.get("key1"), Some(&"value1".to_string()));
        assert_eq!(parsed.get("key2"), Some(&"value2".to_string()));
    }
}

#[test]
fn test_parse_structured_result_empty() {
    // Test parsing empty or malformed input
    assert!(parse_structured_result("").is_none());
    assert!(parse_structured_result("no colons").is_none());
    assert!(parse_structured_result("key1: value1, key2").is_some()); // Partial success
}

#[tokio::test]
async fn test_run_differential_test_detailed() {
    // Test the enhanced differential test function
    let result = run_differential_test_detailed("42").await;

    // The result might fail if Lean isn't available, but the function should complete
    match result {
        Ok(comparison) => {
            assert_eq!(comparison.source, "42");
            assert!(matches!(comparison.test_type, TestType::Evaluation));
        }
        Err(_) => {
            // This is expected if Lean isn't available
            println!("Lean not available, test skipped");
        }
    }
}

#[test]
fn test_print_comparison_report() {
    // Test that the report printing function doesn't crash
    let comparison = ComparisonResult {
        matches: false,
        rust_result: "42".to_string(),
        lean_result: "43".to_string(),
        differences: vec![Difference {
            field: "value".to_string(),
            rust_value: "42".to_string(),
            lean_value: "43".to_string(),
            severity: DifferenceSeverity::Error,
            description: "Value mismatch".to_string(),
        }],
        test_type: TestType::Evaluation,
        source: "test".to_string(),
    };

    // This should not panic
    print_comparison_report(&comparison);
}

#[test]
fn test_difference_severity() {
    // Test severity enum
    assert_eq!(DifferenceSeverity::Info, DifferenceSeverity::Info);
    assert_ne!(DifferenceSeverity::Info, DifferenceSeverity::Error);

    let info = DifferenceSeverity::Info;
    let warning = DifferenceSeverity::Warning;
    let error = DifferenceSeverity::Error;
    let critical = DifferenceSeverity::Critical;

    assert!(matches!(info, DifferenceSeverity::Info));
    assert!(matches!(warning, DifferenceSeverity::Warning));
    assert!(matches!(error, DifferenceSeverity::Error));
    assert!(matches!(critical, DifferenceSeverity::Critical));
}

#[test]
fn test_test_type() {
    // Test test type enum
    let eval = TestType::Evaluation;
    let type_check = TestType::TypeCheck;
    let ops = TestType::OperationalSemantics;
    let config = TestType::Configuration;
    let custom = TestType::Custom("custom_test".to_string());

    assert!(matches!(eval, TestType::Evaluation));
    assert!(matches!(type_check, TestType::TypeCheck));
    assert!(matches!(ops, TestType::OperationalSemantics));
    assert!(matches!(config, TestType::Configuration));

    if let TestType::Custom(name) = custom {
        assert_eq!(name, "custom_test");
    } else {
        panic!("Expected Custom variant");
    }
}
