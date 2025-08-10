//! Workspace management for the Ligature LSP server.

pub mod evaluation;
pub mod indexing;
pub mod manager;
pub mod symbols;
pub mod types;

// Re-export main types and functionality
pub use evaluation::{
    find_implementations_with_evaluation, find_symbol_definition_with_evaluation,
    find_symbol_references_with_evaluation, find_type_definition_with_evaluation,
    get_workspace_stats_with_evaluation, get_workspace_symbols_with_evaluation,
    update_file_with_evaluation,
};
// Re-export for backward compatibility
pub use indexing::{
    index_file, index_file_with_evaluation, index_workspace_internal,
    index_workspace_internal_with_evaluation, scan_directory,
};
pub use manager::WorkspaceManager;
pub use symbols::{
    constraint_references_symbol, convert_to_lsp_symbol, create_symbol_from_declaration,
    expression_references_symbol, extract_symbols_from_program,
    extract_symbols_from_program_with_evaluation, is_constant_expression, is_function_expression,
    pattern_references_symbol, span_to_location, type_references_symbol,
};
pub use types::*;

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tokio::sync::RwLock;

    use super::*;
    use crate::config::LspConfiguration;
    use crate::workspace::indexing::matches_pattern;

    #[tokio::test]
    async fn test_workspace_manager_creation() {
        let config = Arc::new(RwLock::new(LspConfiguration::default()));
        let manager = WorkspaceManager::new(config);
        assert_eq!(manager.folders.read().await.len(), 0);
    }

    #[tokio::test]
    async fn test_workspace_manager_with_async_evaluation() {
        let config = Arc::new(RwLock::new(LspConfiguration::default()));
        let manager = WorkspaceManager::with_async_evaluation(config);
        assert_eq!(manager.folders.read().await.len(), 0);
        // Note: async_evaluation field is private, so we can't test it directly
    }

    #[test]
    fn test_pattern_matching() {
        assert!(matches_pattern("/path/to/file.lig", "file.lig"));
        assert!(!matches_pattern("/path/to/file.lig", "other.lig"));
    }
}
