//! Enhanced Differential Testing Example
//!
//! This example demonstrates the enhanced differential testing framework
//! with detailed comparison and error reporting.

use ligature_ast::AstResult;
use ligature_eval::{Value, evaluate_expression};
use ligature_parser::parse_expression;

/// Example function to demonstrate enhanced differential testing
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    println!("=== Enhanced Differential Testing Example ===");
    println!("This example demonstrates the enhanced differential testing framework");
    println!("with detailed comparison and error reporting.\n");

    // Test cases to demonstrate different scenarios
    let test_cases = vec![
        ("42", "Simple integer literal"),
        ("1 + 2", "Simple arithmetic"),
        ("\"hello\"", "String literal"),
        ("true", "Boolean literal"),
        ("if true then 42 else 0", "Conditional expression"),
        ("let x = 5 in x + 3", "Let expression"),
        ("\\x -> x + 1", "Lambda expression"),
    ];

    for (source, description) in test_cases {
        println!("Testing: {} ({})", source, description);

        // Run Rust evaluation
        let rust_result = match run_rust_evaluation(source) {
            Ok(result) => format!("{:?}", result),
            Err(e) => format!("error: {}", e),
        };

        // Simulate Lean result (in practice, this would come from the Lean specification)
        let lean_result = simulate_lean_result(source);

        // Perform detailed comparison
        let comparison = compare_results_detailed(&rust_result, &lean_result, source);

        // Print comparison report
        print_comparison_summary(&comparison);
        println!();
    }

    println!("=== Example Complete ===");
    println!("The enhanced differential testing framework provides:");
    println!("1. Detailed comparison of Rust and Lean results");
    println!("2. Specific difference identification");
    println!("3. Severity levels for differences");
    println!("4. Comprehensive error reporting");
    println!("5. Support for different test types");

    Ok(())
}

/// Run Rust evaluation for a given source
fn run_rust_evaluation(source: &str) -> AstResult<Value> {
    let expr = parse_expression(source)?;
    evaluate_expression(&expr)
}

/// Simulate Lean result (in practice, this would come from the Lean specification)
fn simulate_lean_result(source: &str) -> String {
    // This is a simplified simulation - in practice, this would be the actual Lean result
    match source {
        "42" => "42".to_string(),
        "1 + 2" => "3".to_string(),
        "\"hello\"" => "\"hello\"".to_string(),
        "true" => "true".to_string(),
        "if true then 42 else 0" => "42".to_string(),
        "let x = 5 in x + 3" => "8".to_string(),
        "\\x -> x + 1" => "function".to_string(),
        _ => "error: unknown expression".to_string(),
    }
}

/// Detailed comparison result structure
#[derive(Debug)]
struct ComparisonResult {
    matches: bool,
    rust_result: String,
    lean_result: String,
    differences: Vec<Difference>,
    source: String,
}

/// Individual difference
#[derive(Debug)]
struct Difference {
    field: String,
    rust_value: String,
    lean_value: String,
    severity: DifferenceSeverity,
    description: String,
}

/// Severity level
#[derive(Debug)]
enum DifferenceSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// Compare results with detailed analysis
fn compare_results_detailed(
    rust_result: &str,
    lean_result: &str,
    source: &str,
) -> ComparisonResult {
    let mut differences = Vec::new();
    let mut matches = true;

    // Normalize results
    let rust_normalized = normalize_result(rust_result);
    let lean_normalized = normalize_result(lean_result);

    // Check for success/failure mismatch
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

    // Compare actual values if both succeeded
    if rust_success && lean_success {
        if rust_normalized != lean_normalized {
            matches = false;
            differences.push(Difference {
                field: "value".to_string(),
                rust_value: rust_normalized.clone(),
                lean_value: lean_normalized.clone(),
                severity: DifferenceSeverity::Error,
                description: "Value mismatch".to_string(),
            });
        }
    } else {
        // Compare error messages
        let rust_error = extract_error_type(&rust_normalized);
        let lean_error = extract_error_type(&lean_normalized);

        if rust_error != lean_error {
            differences.push(Difference {
                field: "error_type".to_string(),
                rust_value: rust_error,
                lean_value: lean_error,
                severity: DifferenceSeverity::Warning,
                description: "Error type mismatch".to_string(),
            });
        }
    }

    ComparisonResult {
        matches,
        rust_result: rust_normalized,
        lean_result: lean_normalized,
        differences,
        source: source.to_string(),
    }
}

/// Normalize result string
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

/// Check if result indicates success
fn is_success_result(result: &str) -> bool {
    !result.contains("error")
        && !result.contains("failed")
        && !result.contains("exception")
        && !result.is_empty()
}

/// Extract error type from result
fn extract_error_type(result: &str) -> String {
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

/// Print comparison summary
fn print_comparison_summary(comparison: &ComparisonResult) {
    println!("  Source: {}", comparison.source);
    println!("  Matches: {}", comparison.matches);

    if !comparison.matches {
        println!("  Differences:");
        for (i, diff) in comparison.differences.iter().enumerate() {
            println!(
                "    {}. {} ({}):",
                i + 1,
                diff.field,
                format!("{:?}", diff.severity)
            );
            println!("       Rust:  {}", diff.rust_value);
            println!("       Lean:  {}", diff.lean_value);
            println!("       Description: {}", diff.description);
        }
    }

    println!("  Rust Result: {}", comparison.rust_result);
    println!("  Lean Result: {}", comparison.lean_result);
}
