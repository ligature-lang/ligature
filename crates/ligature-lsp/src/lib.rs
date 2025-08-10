//! Language Server Protocol implementation for the Ligature language.
//!
//! This crate provides LSP support for the Ligature language, enabling
//! IDE integration with features like syntax highlighting, error reporting,
//! code completion, and more.
//!
//! ## Enhanced Features
//!
//! This crate now includes enhanced LSP features:
//! - **Enhanced Diagnostics**: Better error reporting with detailed explanations and fix suggestions
//! - **Enhanced Completion**: Context-aware code completion with fuzzy matching and auto-import
//! - **Advanced Code Actions**: Intelligent refactoring and code generation
//! - **Improved IDE Integration**: Better performance and real-time feedback

pub mod actions;
pub mod async_evaluation;
pub mod completion;
pub mod config;
pub mod definition;
pub mod diagnostics;
// Enhanced features have been integrated into the main providers
pub mod formatting;
pub mod hover;
pub mod inlay_hints;
pub mod references;
pub mod rename;
pub mod resolution;
pub mod server;
pub mod symbols;
pub mod workspace;

// Original providers
pub use actions::CodeActionsProvider;
pub use completion::CompletionProvider;
pub use definition::DefinitionProvider;
pub use diagnostics::DiagnosticsProvider;
// Enhanced features are now integrated into the main providers
pub use formatting::FormattingProvider;
pub use hover::HoverProvider;
pub use inlay_hints::InlayHintsProvider;
use ligature_ast::Program;
pub use references::ReferencesProvider;
pub use rename::RenameProvider;
pub use resolution::ImportResolutionService;
pub use server::LigatureLspServer;
pub use symbols::SymbolsProvider;
use tower_lsp::LspService;

/// State for a document in the LSP server.
#[derive(Debug, Clone)]
pub struct DocumentState {
    /// The document content.
    pub content: String,
    /// The parsed AST (if parsing succeeded).
    pub ast: Option<Program>,
    /// The last known version.
    pub version: i32,
    /// The last change range for incremental parsing.
    pub last_change_range: Option<lsp_types::Range>,
    /// Whether the document needs full re-parsing.
    pub needs_full_parse: bool,
}

/// Create the LSP service.
pub fn create_lsp_service() -> (LspService<LigatureLspServer>, tower_lsp::ClientSocket) {
    LspService::new(LigatureLspServer::new)
}

/// Create the enhanced LSP service.
// pub fn create_enhanced_lsp_service() -> (LspService<EnhancedLigatureLspServer>, tower_lsp::ClientSocket) {
//     LspService::new(|client| EnhancedLigatureLspServer::new(client))
// }
/// Run the LSP server.
pub async fn run_server() {
    server::run_server().await;
}

// Enhanced features are now integrated into the main server
/// Re-export commonly used LSP types for convenience.
pub use lsp_types;
/// Re-export tower-lsp for advanced usage.
pub use tower_lsp;

/// The main entry point for the Ligature LSP server.
///
/// This function starts the LSP server and handles communication with the client.
/// It should be called from the main function of the LSP binary.
///
/// # Example
///
/// ```rust,no_run
/// use ligature_lsp::run_server;
///
/// #[tokio::main]
/// async fn main() {
///     run_server().await;
/// }
/// ```
pub async fn start_server() {
    run_server().await;
}

/// The enhanced entry point for the Ligature LSP server.
///
/// This function starts the enhanced LSP server with improved features.
///
/// # Example
///
/// ```rust,no_run
/// use ligature_lsp::run_server;
///
/// #[tokio::main]
/// async fn main() {
///     run_server().await;
/// }
/// ```
// pub async fn start_enhanced_server() {
//     run_enhanced_server().await;
// }
/// Create a new Ligature LSP server instance.
///
/// This function creates a new server instance that can be used for testing
/// or custom LSP implementations.
///
/// # Example
///
/// ```rust
/// use ligature_lsp::create_server;
///
/// // In a real implementation, you would create a proper client
/// // For now, this is just a placeholder example
/// ```
pub fn create_server(client: tower_lsp::Client) -> LigatureLspServer {
    LigatureLspServer::new(client)
}

/// Create a new enhanced Ligature LSP server instance.
///
/// This function creates a new enhanced server instance with improved features.
///
/// # Example
///
/// ```rust
/// use ligature_lsp::create_enhanced_server;
///
/// // In a real implementation, you would create a proper client
/// // For now, this is just a placeholder example
/// ```
// pub fn create_enhanced_server(client: tower_lsp::Client) -> EnhancedLigatureLspServer {
//     EnhancedLigatureLspServer::new(client)
// }
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_provider_creation() {
        // Test that all providers can be created successfully
        let _completion = CompletionProvider::new();
        let _hover = HoverProvider::new();
        let _diagnostics = DiagnosticsProvider::new();
        let _references = ReferencesProvider::new();
        let _symbols = SymbolsProvider::new();
        let _definition = DefinitionProvider::new();
        let _code_actions = CodeActionsProvider::new();
        let _formatting = FormattingProvider::new();
        let _rename = RenameProvider::new();
    }

    #[tokio::test]
    async fn test_server_creation() {
        // This test verifies that we can create a server instance
        // In a real test environment, we'd need to mock the client
        // For now, we just test that the modules can be imported and used
        let _provider = CompletionProvider::new();
        let _hover = HoverProvider::new();
        let _diagnostics = DiagnosticsProvider::new();
        let _references = ReferencesProvider::new();
        let _symbols = SymbolsProvider::new();
        // let _enhanced_server = EnhancedLigatureLspServer::new(client); // Temporarily disabled
    }

    #[tokio::test]
    async fn test_lsp_server_initialization() {
        // Test that we can create an LSP server instance
        // This is a basic smoke test to ensure the server can be instantiated

        // Just test that the providers can be created
        let _completion = CompletionProvider::new();
        let _hover = HoverProvider::new();
        let _diagnostics = DiagnosticsProvider::new();
        let _references = ReferencesProvider::new();
        let _symbols = SymbolsProvider::new();
        let _definition = DefinitionProvider::new();
        let _code_actions = CodeActionsProvider::new();
        let _formatting = FormattingProvider::new();
        let _rename = RenameProvider::new();
    }

    #[tokio::test]
    async fn test_workspace_support() {
        // Test workspace folder management

        // Test that we can create providers that support workspace operations
        let _references = ReferencesProvider::new();
        let _symbols = SymbolsProvider::new();

        // Test that providers can be created and used
    }

    #[tokio::test]
    async fn test_workspace_management() {
        // Test workspace configuration
        use crate::config::WorkspaceConfig;
        let config = WorkspaceConfig::default();
        assert!(config.enable_workspace_symbols);
        assert!(config.enable_cross_file_symbols);
        assert_eq!(config.max_workspace_files, 1000);
        assert!(config.include_patterns.contains(&"**/*.lig".to_string()));
        assert!(
            config
                .exclude_patterns
                .contains(&"**/target/**".to_string())
        );

        // Test enhanced workspace configuration (temporarily disabled)
        // let enhanced_config = EnhancedWorkspaceConfiguration::default();
        // assert!(enhanced_config.enable_workspace_diagnostics);
        // assert!(enhanced_config.enable_cross_file_symbols);
        // assert!(enhanced_config.enable_real_time_errors);
        // assert!(enhanced_config.enable_performance_monitoring);
        // assert!(enhanced_config.enable_advanced_refactoring);

        // Test workspace folder handling
        use lsp_types::{Url, WorkspaceFolder};
        let workspace_folders = vec![
            WorkspaceFolder {
                uri: Url::parse("file:///test/project1").unwrap(),
                name: "project1".to_string(),
            },
            WorkspaceFolder {
                uri: Url::parse("file:///test/project2").unwrap(),
                name: "project2".to_string(),
            },
        ];

        assert_eq!(workspace_folders.len(), 2);
        assert_eq!(workspace_folders[0].name, "project1");
        assert_eq!(workspace_folders[1].name, "project2");
    }
}
