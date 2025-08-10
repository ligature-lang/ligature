//! Comprehensive tests for the Ligature LSP server.
//! 
//! These tests verify that all LSP features work correctly, including:
//! - Basic LSP functionality
//! - Async evaluation integration
//! - Symbol finding and navigation
//! - Code completion and diagnostics
//! - Formatting and code actions

use ligature_lsp::{
    server::LigatureLspServer,
    config::LspConfiguration,
    async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService},
    workspace::WorkspaceManager,
    symbols::SymbolsProvider,
    completion::CompletionProvider,
    diagnostics::DiagnosticsProvider,
    formatting::FormattingProvider,
    code_actions::CodeActionsProvider,
    hover::HoverProvider,
    references::ReferencesProvider,
    definition::DefinitionProvider,
    rename::RenameProvider,
    inlay_hints::InlayHintsProvider,
};
use lsp_types::{
    Position, Range, TextDocumentIdentifier, TextDocumentItem, VersionedTextDocumentIdentifier,
    InitializeParams, ClientCapabilities, WorkspaceFolder, Uri,
};
use std::sync::Arc;
use tokio::sync::RwLock;

/// Test basic LSP server initialization and configuration
#[tokio::test]
async fn test_lsp_server_initialization() {
    // Test with default configuration
    let config = LspConfiguration::default();
    let server = LigatureLspServer::new(config);
    assert!(server.is_ok());

    // Test with async evaluation enabled
    let mut config = LspConfiguration::default();
    config.async_evaluation.enable_async_evaluation = true;
    let server = LigatureLspServer::new(config);
    assert!(server.is_ok());
}

/// Test async evaluation service integration
#[tokio::test]
async fn test_async_evaluation_integration() {
    let config = AsyncEvaluationConfig::default();
    let eval_service = AsyncEvaluationService::new(config);
    assert!(eval_service.is_ok());

    let eval_service = eval_service.unwrap();
    
    // Test simple program evaluation
    let program_str = "let x = 42;";
    let program = ligature_parser::parse_program(program_str).unwrap();
    
    let result = eval_service.evaluate_program(&program, Some("test")).await;
    assert!(result.is_ok());
    
    let evaluation_result = result.unwrap();
    assert!(evaluation_result.success);
    assert_eq!(evaluation_result.values.len(), 1);
}

/// Test workspace management with async evaluation
#[tokio::test]
async fn test_workspace_management() {
    let config = AsyncEvaluationConfig::default();
    let eval_service = AsyncEvaluationService::new(config).unwrap();
    
    let workspace = WorkspaceManager::with_async_evaluation(eval_service);
    
    // Test adding a workspace folder
    let folder = WorkspaceFolder {
        uri: Uri::from_file_path("/test/workspace").unwrap(),
        name: "test".to_string(),
    };
    
    workspace.add_workspace_folder(folder).await;
    
    // Test indexing a file
    let content = "let x = 42; let y = x + 1;";
    let uri = "file:///test/workspace/test.lig";
    
    workspace.index_file(uri, content).await;
    
    // Verify the file was indexed
    let files = workspace.get_files().await;
    assert!(files.contains_key(uri));
}

/// Test symbol finding and navigation
#[tokio::test]
async fn test_symbol_finding() {
    let symbols_provider = SymbolsProvider::with_async_evaluation();
    
    let content = r#"
        let x = 42;
        let y = x + 1;
        let z = y * 2;
    "#;
    
    let symbols = symbols_provider.get_document_symbols("test.lig", content).await;
    assert!(!symbols.is_empty());
    
    // Should find symbols for x, y, and z
    let symbol_names: Vec<String> = symbols.iter()
        .map(|s| s.name.clone())
        .collect();
    
    assert!(symbol_names.contains(&"x".to_string()));
    assert!(symbol_names.contains(&"y".to_string()));
    assert!(symbol_names.contains(&"z".to_string()));
}

/// Test code completion
#[tokio::test]
async fn test_code_completion() {
    let completion_provider = CompletionProvider::with_async_evaluation();
    
    let content = r#"
        let x = 42;
        let y = 
    "#;
    
    let position = Position {
        line: 2,
        character: 8,
    };
    
    let completions = completion_provider
        .provide_completions("test.lig", content, position)
        .await;
    
    // Should suggest 'x' as a completion
    let completion_labels: Vec<String> = completions.iter()
        .map(|c| c.label.clone())
        .collect();
    
    assert!(completion_labels.contains(&"x".to_string()));
}

/// Test diagnostics
#[tokio::test]
async fn test_diagnostics() {
    let diagnostics_provider = DiagnosticsProvider::new();
    
    // Test with valid code
    let valid_content = "let x = 42;";
    let diagnostics = diagnostics_provider
        .compute_diagnostics("test.lig", valid_content)
        .await;
    
    assert!(diagnostics.is_empty());
    
    // Test with invalid code
    let invalid_content = "let x = ;"; // Missing expression
    let diagnostics = diagnostics_provider
        .compute_diagnostics("test.lig", invalid_content)
        .await;
    
    assert!(!diagnostics.is_empty());
}

/// Test formatting
#[tokio::test]
async fn test_formatting() {
    let formatting_provider = FormattingProvider::with_async_evaluation();
    
    let unformatted_content = "let x=42;let y=x+1;";
    let edits = formatting_provider
        .format_document("test.lig", unformatted_content)
        .await;
    
    assert!(!edits.is_empty());
    
    // Apply the formatting edits
    let mut formatted_content = unformatted_content.to_string();
    for edit in edits {
        // Simple text replacement for testing
        formatted_content = edit.new_text;
    }
    
    // Should be properly formatted
    assert!(formatted_content.contains("let x = 42;"));
    assert!(formatted_content.contains("let y = x + 1;"));
}

/// Test code actions
#[tokio::test]
async fn test_code_actions() {
    let code_actions_provider = CodeActionsProvider::with_async_evaluation();
    
    let content = "let x = 42;";
    let range = Range {
        start: Position { line: 0, character: 0 },
        end: Position { line: 0, character: 10 },
    };
    
    let actions = code_actions_provider
        .provide_code_actions("test.lig", content, range, &Default::default())
        .await;
    
    // Should provide some code actions
    assert!(!actions.is_empty());
}

/// Test hover information
#[tokio::test]
async fn test_hover() {
    let hover_provider = HoverProvider::with_async_evaluation();
    
    let content = "let x = 42;";
    let position = Position {
        line: 0,
        character: 6, // Position on 'x'
    };
    
    let hover = hover_provider
        .provide_hover("test.lig", content, position)
        .await;
    
    // Should provide hover information for the variable
    assert!(hover.is_some());
}

/// Test references finding
#[tokio::test]
async fn test_references() {
    let references_provider = ReferencesProvider::new();
    
    let content = r#"
        let x = 42;
        let y = x + 1;
        let z = x * 2;
    "#;
    
    let position = Position {
        line: 1,
        character: 6, // Position on 'x'
    };
    
    let references = references_provider
        .find_references("test.lig", content, position)
        .await;
    
    // Should find references to 'x' in lines 1, 2, and 3
    assert_eq!(references.len(), 3);
}

/// Test definition finding
#[tokio::test]
async fn test_definitions() {
    let definition_provider = DefinitionProvider::with_async_evaluation();
    
    let content = r#"
        let x = 42;
        let y = x + 1;
    "#;
    
    let position = Position {
        line: 2,
        character: 6, // Position on 'x' in the usage
    };
    
    let definition = definition_provider
        .find_definition_enhanced("test.lig", content, position)
        .await;
    
    // Should find the definition of 'x'
    assert!(definition.is_some());
    
    let def = definition.unwrap();
    assert_eq!(def.range.start.line, 1); // Definition is on line 1
}

/// Test rename functionality
#[tokio::test]
async fn test_rename() {
    let rename_provider = RenameProvider::with_async_evaluation();
    
    let content = r#"
        let x = 42;
        let y = x + 1;
    "#;
    
    let position = Position {
        line: 1,
        character: 6, // Position on 'x'
    };
    
    // Test prepare rename
    let prepare_response = rename_provider
        .prepare_rename_enhanced("test.lig", position, content)
        .await;
    
    assert!(prepare_response.is_some());
    
    // Test actual rename
    let workspace_edit = rename_provider
        .rename_symbol_enhanced("test.lig", content, position, "newX")
        .await;
    
    assert!(workspace_edit.is_some());
}

/// Test inlay hints
#[tokio::test]
async fn test_inlay_hints() {
    let inlay_hints_provider = InlayHintsProvider::with_async_evaluation();
    
    let content = "let x = 42;";
    let range = Range {
        start: Position { line: 0, character: 0 },
        end: Position { line: 0, character: 10 },
    };
    
    let hints = inlay_hints_provider
        .provide_inlay_hints("test.lig", content, range)
        .await;
    
    // Should provide some inlay hints
    assert!(!hints.is_empty());
}

/// Test end-to-end LSP workflow
#[tokio::test]
async fn test_end_to_end_lsp_workflow() {
    // Initialize server with async evaluation
    let mut config = LspConfiguration::default();
    config.async_evaluation.enable_async_evaluation = true;
    let server = LigatureLspServer::new(config).unwrap();
    
    // Simulate document open
    let document = TextDocumentItem {
        uri: Uri::from_file_path("/test/workspace/test.lig").unwrap(),
        language_id: "ligature".to_string(),
        version: 1,
        text: r#"
            let x = 42;
            let y = x + 1;
            let z = y * 2;
        "#.to_string(),
    };
    
    // Test document symbols
    let symbols = server.workspace.get_document_symbols(&document.uri, &document.text).await;
    assert_eq!(symbols.len(), 3);
    
    // Test completion at position
    let position = Position { line: 2, character: 8 };
    let completions = server.completion.provide_completions(&document.uri, &document.text, position).await;
    assert!(!completions.is_empty());
    
    // Test diagnostics
    let diagnostics = server.diagnostics.compute_diagnostics(&document.uri, &document.text).await;
    assert!(diagnostics.is_empty()); // Should be valid code
    
    // Test formatting
    let edits = server.formatting.format_document(&document.uri, &document.text).await;
    assert!(!edits.is_empty());
    
    // Test hover
    let hover_position = Position { line: 1, character: 6 };
    let hover = server.hover.provide_hover(&document.uri, &document.text, hover_position).await;
    assert!(hover.is_some());
}

/// Test async evaluation performance
#[tokio::test]
async fn test_async_evaluation_performance() {
    let config = AsyncEvaluationConfig {
        enable_async_evaluation: true,
        max_evaluation_time: std::time::Duration::from_millis(100),
        show_progress: false,
        enable_caching: true,
        max_cache_size: 1000,
    };
    
    let eval_service = AsyncEvaluationService::new(config).unwrap();
    
    // Test with a larger program
    let program_str = r#"
        let x = 42;
        let y = x + 1;
        let z = y * 2;
        let w = z / 3;
        let result = w - 5;
    "#;
    
    let program = ligature_parser::parse_program(program_str).unwrap();
    
    let start = std::time::Instant::now();
    let result = eval_service.evaluate_program(&program, Some("perf_test")).await;
    let duration = start.elapsed();
    
    assert!(result.is_ok());
    assert!(duration < std::time::Duration::from_millis(50)); // Should be fast
    
    // Test caching
    let start = std::time::Instant::now();
    let result2 = eval_service.evaluate_program(&program, Some("perf_test")).await;
    let duration2 = start.elapsed();
    
    assert!(result2.is_ok());
    assert!(duration2 < duration); // Cached result should be faster
}

/// Test error handling in LSP server
#[tokio::test]
async fn test_error_handling() {
    let server = LigatureLspServer::new(LspConfiguration::default()).unwrap();
    
    // Test with invalid content
    let invalid_content = "let x = ;"; // Invalid syntax
    
    // Should handle parsing errors gracefully
    let diagnostics = server.diagnostics.compute_diagnostics("test.lig", invalid_content).await;
    assert!(!diagnostics.is_empty());
    
    // Test with empty content
    let empty_content = "";
    let diagnostics = server.diagnostics.compute_diagnostics("test.lig", empty_content).await;
    assert!(diagnostics.is_empty());
    
    // Test with very large content
    let large_content = "let x = 42;".repeat(1000);
    let diagnostics = server.diagnostics.compute_diagnostics("test.lig", &large_content).await;
    // Should handle large content without panicking
    assert!(diagnostics.is_empty());
}

/// Test configuration updates
#[tokio::test]
async fn test_configuration_updates() {
    let mut config = LspConfiguration::default();
    config.async_evaluation.enable_async_evaluation = false;
    
    let mut server = LigatureLspServer::new(config).unwrap();
    
    // Update configuration
    let new_config = LspConfiguration::default();
    server.update_config(new_config).await;
    
    // Verify configuration was updated
    let current_config = server.get_config();
    assert!(current_config.async_evaluation.enable_async_evaluation);
}

/// Test workspace folder management
#[tokio::test]
async fn test_workspace_folder_management() {
    let server = LigatureLspServer::new(LspConfiguration::default()).unwrap();
    
    // Add workspace folder
    let folder = WorkspaceFolder {
        uri: Uri::from_file_path("/test/workspace").unwrap(),
        name: "test".to_string(),
    };
    
    server.workspace.add_workspace_folder(folder).await;
    
    // Verify folder was added
    let folders = server.workspace.get_workspace_folders().await;
    assert_eq!(folders.len(), 1);
    assert_eq!(folders[0].name, "test");
    
    // Remove workspace folder
    server.workspace.remove_workspace_folder(&Uri::from_file_path("/test/workspace").unwrap()).await;
    
    // Verify folder was removed
    let folders = server.workspace.get_workspace_folders().await;
    assert_eq!(folders.len(), 0);
}
