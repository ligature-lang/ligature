//! Example demonstrating the enhanced LSP features for Ligature.
//!
//! This example shows how to use the enhanced diagnostics, completion, and code actions
//! features to provide better IDE integration.

use ligature_lsp::{
    CodeActionsProvider, EnhancedCompletionConfig, EnhancedCompletionProvider,
    EnhancedDiagnosticsConfig, EnhancedDiagnosticsProvider,
};
use lsp_types::{DiagnosticSeverity, Position, Range};

#[tokio::main]
async fn main() {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    println!("Enhanced LSP Features Example");
    println!("=============================");

    // Example 1: Enhanced Diagnostics
    example_enhanced_diagnostics().await;

    // Example 2: Enhanced Completion
    example_enhanced_completion().await;

    // Example 3: Code Actions
    example_code_actions().await;

    println!("\nAll examples completed successfully!");
}

async fn example_enhanced_diagnostics() {
    println!("\n1. Enhanced Diagnostics Example");
    println!("-------------------------------");

    // Create enhanced diagnostics provider with custom configuration
    let config = EnhancedDiagnosticsConfig {
        enable_detailed_explanations: true,
        enable_fix_suggestions: true,
        enable_security_warnings: true,
        enable_style_suggestions: true,
        ..Default::default()
    };

    let mut diagnostics = EnhancedDiagnosticsProvider::with_config(config);

    // Example Ligature code with various issues
    let code = r#"
import add from "stdlib/core"

let password = "secret123"  // Security warning
let unused_var = 42        // Unused variable warning
let long_line = "This is a very long line that exceeds the recommended length and should be wrapped for better readability"  // Style warning

fun calculate(x: Int) -> Int = 
  add x 5  // Missing semicolon

type MyType = 
  Constructor1 | Constructor2

match someValue of
  Constructor1 => "first"
  Constructor2 => "second"
"#;

    // Compute diagnostics
    if let Some(diagnostics_list) = diagnostics
        .compute_enhanced_diagnostics("file:///example.lig", code, None)
        .await
    {
        println!("Found {} diagnostics:", diagnostics_list.len());

        for diagnostic in diagnostics_list {
            let severity = diagnostic.severity.unwrap_or(DiagnosticSeverity::ERROR);
            let severity_str = match severity {
                DiagnosticSeverity::ERROR => "ERROR",
                DiagnosticSeverity::WARNING => "WARNING",
                DiagnosticSeverity::INFORMATION => "INFO",
                DiagnosticSeverity::HINT => "HINT",
                _ => "UNKNOWN",
            };

            println!(
                "  [{}] {}: {}",
                severity_str,
                diagnostic
                    .code
                    .as_ref()
                    .map(|code| format!("{code:?}"))
                    .unwrap_or_else(|| "UNKNOWN".to_string()),
                diagnostic.message
            );
        }
    } else {
        println!("No diagnostics found");
    }
}

async fn example_enhanced_completion() {
    println!("\n2. Enhanced Completion Example");
    println!("-------------------------------");

    // Create enhanced completion provider with custom configuration
    let config = EnhancedCompletionConfig {
        enable_context_aware: true,
        enable_type_aware: true,
        enable_fuzzy_matching: true,
        enable_auto_import: true,
        enable_snippets: true,
        ..Default::default()
    };

    let completion = EnhancedCompletionProvider::with_config(config);

    // Example code for different contexts
    let function_context = r#"
fun myFunction(x: Int) -> Int = 
  let result = 
"#;

    let type_context = r#"
type MyType = 
"#;

    let pattern_context = r#"
match someValue of
"#;

    // Test completions in different contexts
    let contexts = vec![
        (
            "Function context",
            function_context,
            Position {
                line: 2,
                character: 10,
            },
        ),
        (
            "Type context",
            type_context,
            Position {
                line: 1,
                character: 10,
            },
        ),
        (
            "Pattern context",
            pattern_context,
            Position {
                line: 1,
                character: 10,
            },
        ),
    ];

    for (context_name, code, position) in contexts {
        println!("\n  Testing {context_name}:");

        let completions = completion
            .provide_enhanced_completion("file:///example.lig", code, position, None)
            .await;

        if let lsp_types::CompletionResponse::Array(items) = completions {
            println!("    Found {} completions:", items.len());
            for item in items.iter().take(5) {
                // Show first 5 completions
                println!("      - {} ({:?})", item.label, item.kind);
            }
            if items.len() > 5 {
                println!("      ... and {} more", items.len() - 5);
            }
        }
    }
}

async fn example_code_actions() {
    println!("\n3. Code Actions Example");
    println!("------------------------");

    // Create code actions provider
    let code_actions = CodeActionsProvider::new();

    // Example code with issues that can be fixed
    let code = r#"
import unused from "stdlib/core"

let x = 42
let y = add x 5

fun calculate(a: Int, b: Int) -> Int = 
  let result = add a b
  result

type MyType = 
  Constructor1 | Constructor2

match someValue of
  Constructor1 => "first"
  Constructor2 => "second"
"#;

    // Create a diagnostic to trigger code actions
    let diagnostic = lsp_types::Diagnostic {
        range: Range {
            start: Position {
                line: 1,
                character: 0,
            },
            end: Position {
                line: 1,
                character: 20,
            },
        },
        severity: Some(DiagnosticSeverity::WARNING),
        code: Some(lsp_types::NumberOrString::String("W001".to_string())),
        code_description: None,
        source: Some("ligature-semantic".to_string()),
        message: "Unused import: unused".to_string(),
        related_information: None,
        tags: None,
        data: None,
    };

    let context = lsp_types::CodeActionContext {
        diagnostics: vec![diagnostic],
        only: None,
        trigger_kind: None,
    };

    // Get code actions
    let actions = code_actions
        .provide_code_actions(
            "file:///example.lig",
            code,
            Range {
                start: Position {
                    line: 1,
                    character: 0,
                },
                end: Position {
                    line: 1,
                    character: 20,
                },
            },
            &context,
        )
        .await;

    println!("  Found {} code actions:", actions.len());

    for action in actions {
        if let lsp_types::CodeActionOrCommand::CodeAction(code_action) = action {
            println!(
                "    - {} ({:?})",
                code_action.title,
                code_action
                    .kind
                    .as_ref()
                    .unwrap_or(&lsp_types::CodeActionKind::QUICKFIX)
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_enhanced_diagnostics_creation() {
        let config = EnhancedDiagnosticsConfig::default();
        let diagnostics = EnhancedDiagnosticsProvider::with_config(config);
        assert!(true); // Just test that it can be created
    }

    #[tokio::test]
    async fn test_enhanced_completion_creation() {
        let config = EnhancedCompletionConfig::default();
        let completion = EnhancedCompletionProvider::with_config(config);
        assert!(true); // Just test that it can be created
    }

    #[tokio::test]
    async fn test_code_actions_creation() {
        let code_actions = CodeActionsProvider::new();
        assert!(true); // Just test that it can be created
    }
}
