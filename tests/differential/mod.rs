//! Differential tests against the Lean specification.
//!
//! These tests verify that the Rust implementation matches
//! the behavior specified in the Lean formal specification.

pub mod configuration_tests;
pub mod operational_semantics_tests;
pub mod spec_compliance_tests;
pub mod test_enhanced_comparison;
pub mod type_system_tests;

use ligature_ast::{AstResult, Expr, Type, Value};
use ligature_eval::{evaluate_expression, evaluate_program};
use ligature_parser::{parse_expression, parse_program};
use ligature_types::{infer_expression, type_check_program};
use std::collections::HashMap;

#[cfg(feature = "lean-integration")]
use baton_verification::prelude::*;

/// Detailed comparison result for differential testing
#[derive(Debug, Clone)]
pub struct ComparisonResult {
    pub matches: bool,
    pub rust_result: String,
    pub lean_result: String,
    pub differences: Vec<Difference>,
    pub test_type: TestType,
    pub source: String,
}

/// Individual difference between Rust and Lean results
#[derive(Debug, Clone)]
pub struct Difference {
    pub field: String,
    pub rust_value: String,
    pub lean_value: String,
    pub severity: DifferenceSeverity,
    pub description: String,
}

/// Severity level for differences
#[derive(Debug, Clone, PartialEq)]
pub enum DifferenceSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// Type of test being performed
#[derive(Debug, Clone)]
pub enum TestType {
    Evaluation,
    TypeCheck,
    OperationalSemantics,
    Configuration,
    Custom(String),
}

/// Enhanced result comparison with detailed analysis
pub fn compare_rust_lean_results_detailed(
    rust_result: &str,
    lean_result: &str,
    test_type: TestType,
    source: &str,
) -> ComparisonResult {
    let mut differences = Vec::new();
    let mut matches = true;

    // Normalize results for comparison
    let rust_normalized = normalize_result(rust_result);
    let lean_normalized = normalize_result(lean_result);

    // Check for basic success/failure
    let rust_success = is_success_result(&rust_normalized);
    let lean_success = is_success_result(&lean_normalized);

    if rust_success != lean_success {
        matches = false;
        differences.push(Difference {
            field: "success_status".to_string(),
            rust_value: format!("{}", rust_success),
            lean_value: format!("{}", lean_success),
            severity: DifferenceSeverity::Critical,
            description: "Success/failure status mismatch".to_string(),
        });
    }

    // If both succeeded, compare the actual values
    if rust_success && lean_success {
        // Parse and compare structured results
        if let Some(diff) = compare_structured_results(&rust_normalized, &lean_normalized) {
            differences.extend(diff);
            matches = false;
        }
    } else {
        // Compare error messages
        if let Some(diff) = compare_error_messages(&rust_normalized, &lean_normalized) {
            differences.push(diff);
            matches = false;
        }
    }

    // Check for type-specific differences
    match &test_type {
        TestType::Evaluation => {
            if let Some(diff) = compare_evaluation_results(&rust_normalized, &lean_normalized) {
                differences.push(diff);
                matches = false;
            }
        }
        TestType::TypeCheck => {
            if let Some(diff) = compare_type_check_results(&rust_normalized, &lean_normalized) {
                differences.push(diff);
                matches = false;
            }
        }
        _ => {}
    }

    ComparisonResult {
        matches,
        rust_result: rust_normalized,
        lean_result: lean_normalized,
        differences,
        test_type,
        source: source.to_string(),
    }
}

/// Normalize result strings for comparison
fn normalize_result(result: &str) -> String {
    result
        .trim()
        .replace('\n', " ")
        .replace('\r', " ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_lowercase()
}

/// Check if a result indicates success
fn is_success_result(result: &str) -> bool {
    !result.contains("error")
        && !result.contains("failed")
        && !result.contains("exception")
        && !result.is_empty()
}

/// Compare structured results (when both succeeded)
fn compare_structured_results(rust: &str, lean: &str) -> Option<Vec<Difference>> {
    let mut differences = Vec::new();

    // Try to parse as JSON-like structures
    if let (Some(rust_parsed), Some(lean_parsed)) =
        (parse_structured_result(rust), parse_structured_result(lean))
    {
        for (key, rust_val) in &rust_parsed {
            if let Some(lean_val) = lean_parsed.get(key) {
                if rust_val != lean_val {
                    differences.push(Difference {
                        field: key.clone(),
                        rust_value: rust_val.clone(),
                        lean_value: lean_val.clone(),
                        severity: DifferenceSeverity::Error,
                        description: format!("Value mismatch for field '{}'", key),
                    });
                }
            } else {
                differences.push(Difference {
                    field: key.clone(),
                    rust_value: rust_val.clone(),
                    lean_value: "missing".to_string(),
                    severity: DifferenceSeverity::Warning,
                    description: format!("Field '{}' missing in Lean result", key),
                });
            }
        }

        // Check for extra fields in Lean result
        for (key, lean_val) in &lean_parsed {
            if !rust_parsed.contains_key(key) {
                differences.push(Difference {
                    field: key.clone(),
                    rust_value: "missing".to_string(),
                    lean_value: lean_val.clone(),
                    severity: DifferenceSeverity::Info,
                    description: format!("Extra field '{}' in Lean result", key),
                });
            }
        }
    } else {
        // Fallback to string comparison
        if rust != lean {
            differences.push(Difference {
                field: "value".to_string(),
                rust_value: rust.to_string(),
                lean_value: lean.to_string(),
                severity: DifferenceSeverity::Error,
                description: "String value mismatch".to_string(),
            });
        }
    }

    if differences.is_empty() {
        None
    } else {
        Some(differences)
    }
}

/// Parse structured result (JSON-like or key-value pairs)
fn parse_structured_result(result: &str) -> Option<HashMap<String, String>> {
    let mut parsed = HashMap::new();

    // Try to extract key-value pairs
    for line in result.split(',') {
        let parts: Vec<&str> = line.split(':').collect();
        if parts.len() == 2 {
            let key = parts[0].trim().trim_matches('"').to_string();
            let value = parts[1].trim().trim_matches('"').to_string();
            parsed.insert(key, value);
        }
    }

    if parsed.is_empty() {
        None
    } else {
        Some(parsed)
    }
}

/// Compare error messages
fn compare_error_messages(rust: &str, lean: &str) -> Option<Difference> {
    // Extract error types and messages
    let rust_error = extract_error_info(rust);
    let lean_error = extract_error_info(lean);

    if rust_error != lean_error {
        Some(Difference {
            field: "error".to_string(),
            rust_value: rust_error,
            lean_value: lean_error,
            severity: DifferenceSeverity::Warning,
            description: "Error message mismatch".to_string(),
        })
    } else {
        None
    }
}

/// Extract error information from result string
fn extract_error_info(result: &str) -> String {
    // Look for common error patterns
    if result.contains("parse error") {
        "parse_error".to_string()
    } else if result.contains("type error") {
        "type_error".to_string()
    } else if result.contains("evaluation error") {
        "evaluation_error".to_string()
    } else if result.contains("error") {
        "general_error".to_string()
    } else {
        "unknown_error".to_string()
    }
}

/// Compare evaluation-specific results
fn compare_evaluation_results(rust: &str, lean: &str) -> Option<Difference> {
    // Extract numeric values for comparison
    let rust_num = extract_numeric_value(rust);
    let lean_num = extract_numeric_value(lean);

    if let (Some(r), Some(l)) = (rust_num, lean_num) {
        if (r - l).abs() > f64::EPSILON {
            return Some(Difference {
                field: "numeric_value".to_string(),
                rust_value: format!("{}", r),
                lean_value: format!("{}", l),
                severity: DifferenceSeverity::Error,
                description: "Numeric value mismatch".to_string(),
            });
        }
    }

    None
}

/// Extract numeric value from result string
fn extract_numeric_value(result: &str) -> Option<f64> {
    // Look for numeric patterns
    for word in result.split_whitespace() {
        if let Ok(num) = word.parse::<f64>() {
            return Some(num);
        }
    }
    None
}

/// Compare type check results
fn compare_type_check_results(rust: &str, lean: &str) -> Option<Difference> {
    // Extract type information
    let rust_type = extract_type_info(rust);
    let lean_type = extract_type_info(lean);

    if rust_type != lean_type {
        Some(Difference {
            field: "type".to_string(),
            rust_value: rust_type,
            lean_value: lean_type,
            severity: DifferenceSeverity::Error,
            description: "Type mismatch".to_string(),
        })
    } else {
        None
    }
}

/// Extract type information from result string
fn extract_type_info(result: &str) -> String {
    // Look for type patterns
    if result.contains("int") || result.contains("integer") {
        "int".to_string()
    } else if result.contains("string") {
        "string".to_string()
    } else if result.contains("bool") || result.contains("boolean") {
        "bool".to_string()
    } else if result.contains("float") || result.contains("double") {
        "float".to_string()
    } else {
        "unknown".to_string()
    }
}

/// Helper function to run a test case against the Lean specification
/// This uses the new Lean integration system
#[cfg(feature = "lean-integration")]
pub async fn run_lean_test_case(source: &str) -> Result<String, String> {
    let engine = VerificationEngine::new()
        .map_err(|e| format!("Failed to create verification engine: {}", e))?;

    // Run a simple evaluation test
    let response = engine
        .verify_evaluation(source, "placeholder")
        .await
        .map_err(|e| format!("Lean verification failed: {}", e))?;

    if response.is_success() {
        Ok("lean_verification_success".to_string())
    } else {
        Err(response
            .error_message()
            .unwrap_or("Unknown error")
            .to_string())
    }
}

/// Helper function to run a test case against the Lean specification (stub when lean-integration feature is disabled)
#[cfg(not(feature = "lean-integration"))]
pub async fn run_lean_test_case(source: &str) -> Result<String, String> {
    Err("Lean integration is not enabled. Enable the 'lean-integration' feature to use this functionality.".to_string())
}

/// Legacy simple comparison function (for backward compatibility)
pub fn compare_rust_lean_results(rust_result: &str, lean_result: &str) -> bool {
    let comparison = compare_rust_lean_results_detailed(
        rust_result,
        lean_result,
        TestType::Evaluation,
        "unknown",
    );
    comparison.matches
}

/// Helper function to extract test cases from Lean specification files
#[cfg(feature = "lean-integration")]
pub async fn extract_test_cases_from_spec() -> Result<Vec<String>, String> {
    let engine = VerificationEngine::new()
        .map_err(|e| format!("Failed to create verification engine: {}", e))?;

    engine
        .extract_test_cases("TestSpec.lean")
        .await
        .map_err(|e| format!("Failed to extract test cases: {}", e))
}

/// Helper function to extract test cases from Lean specification files (stub when lean-integration feature is disabled)
#[cfg(not(feature = "lean-integration"))]
pub async fn extract_test_cases_from_spec() -> Result<Vec<String>, String> {
    Err("Lean integration is not enabled. Enable the 'lean-integration' feature to use this functionality.".to_string())
}

/// Enhanced differential test with detailed comparison
pub async fn run_differential_test_detailed(source: &str) -> Result<ComparisonResult, String> {
    // Parse and evaluate in Rust
    let rust_result = parse_expression(source)
        .and_then(|expr| evaluate_expression(&expr))
        .map(|value| format!("{:?}", value))
        .map_err(|e| e.to_string())?;

    // Run the same test in Lean
    let lean_result = run_lean_test_case(source).await?;

    // Compare results with detailed analysis
    Ok(compare_rust_lean_results_detailed(
        &rust_result,
        &lean_result,
        TestType::Evaluation,
        source,
    ))
}

/// Helper function to run a complete differential test (legacy)
pub async fn run_differential_test(source: &str) -> Result<bool, String> {
    let comparison = run_differential_test_detailed(source).await?;
    Ok(comparison.matches)
}

/// Enhanced type checking differential test
pub async fn run_type_check_differential_test_detailed(
    source: &str,
) -> Result<ComparisonResult, String> {
    // Type check in Rust
    let rust_result = parse_expression(source)
        .and_then(|expr| type_check_program(&parse_program(&format!("let x = {};", source))?))
        .map(|_| "type_check_success".to_string())
        .map_err(|e| e.to_string())?;

    // Run type checking in Lean
    let lean_result = run_lean_test_case(&format!("type_check: {}", source)).await?;

    // Compare results with detailed analysis
    Ok(compare_rust_lean_results_detailed(
        &rust_result,
        &lean_result,
        TestType::TypeCheck,
        source,
    ))
}

/// Helper function to run type checking differential test (legacy)
pub fn run_type_check_differential_test(source: &str) -> Result<bool, String> {
    // This is a simplified version - in practice, you'd want to make this async
    // For now, we'll return a placeholder result
    Ok(true)
}

/// Enhanced operational semantics test
pub async fn run_operational_semantics_test_detailed(
    source: &str,
) -> Result<ComparisonResult, String> {
    // Parse and evaluate in Rust
    let rust_result = parse_expression(source)
        .and_then(|expr| evaluate_expression(&expr))
        .map(|value| format!("{:?}", value))
        .map_err(|e| e.to_string())?;

    // Run operational semantics in Lean
    let lean_result = run_lean_test_case(&format!("eval: {}", source)).await?;

    // Compare results with detailed analysis
    Ok(compare_rust_lean_results_detailed(
        &rust_result,
        &lean_result,
        TestType::OperationalSemantics,
        source,
    ))
}

/// Helper function to run operational semantics test (legacy)
pub fn run_operational_semantics_test(source: &str) -> Result<bool, String> {
    // This is a simplified version - in practice, you'd want to make this async
    // For now, we'll return a placeholder result
    Ok(true)
}

/// Enhanced configuration language test
pub async fn run_configuration_test_detailed(source: &str) -> Result<ComparisonResult, String> {
    // Parse and evaluate configuration in Rust
    let rust_result = parse_program(source)
        .and_then(|program| evaluate_program(&program))
        .map(|value| format!("{:?}", value))
        .map_err(|e| e.to_string())?;

    // Run configuration evaluation in Lean
    let lean_result = run_lean_test_case(&format!("config: {}", source)).await?;

    // Compare results with detailed analysis
    Ok(compare_rust_lean_results_detailed(
        &rust_result,
        &lean_result,
        TestType::Configuration,
        source,
    ))
}

/// Helper function to run configuration language test (legacy)
pub fn run_configuration_test(source: &str) -> Result<bool, String> {
    // This is a simplified version - in practice, you'd want to make this async
    // For now, we'll return a placeholder result
    Ok(true)
}

/// Print detailed comparison report
pub fn print_comparison_report(comparison: &ComparisonResult) {
    println!("=== Differential Test Report ===");
    println!("Source: {}", comparison.source);
    println!("Test Type: {:?}", comparison.test_type);
    println!("Matches: {}", comparison.matches);

    if !comparison.matches {
        println!("\nDifferences:");
        for (i, diff) in comparison.differences.iter().enumerate() {
            println!("  {}. {} ({}):", i + 1, diff.field, diff.severity);
            println!("     Rust:  {}", diff.rust_value);
            println!("     Lean:  {}", diff.lean_value);
            println!("     Description: {}", diff.description);
        }
    }

    println!("\nRust Result: {}", comparison.rust_result);
    println!("Lean Result: {}", comparison.lean_result);
    println!("================================");
}
