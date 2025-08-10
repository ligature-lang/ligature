//! Workspace manager for handling workspace operations.

use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::lsp_types::WorkspaceFolder;

use super::evaluation::*;
use super::indexing::*;
use super::symbols::*;
use super::types::*;
use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};
use crate::config::LspConfiguration;

/// Workspace manager for handling workspace operations
pub struct WorkspaceManager {
    /// Workspace configuration
    config: Arc<RwLock<LspConfiguration>>,
    /// Workspace files
    #[allow(clippy::type_complexity)]
    files: Arc<RwLock<HashMap<String, WorkspaceFile>>>,
    /// Workspace symbols
    #[allow(clippy::type_complexity)]
    symbols: Arc<RwLock<HashMap<String, Vec<WorkspaceSymbolWithMetadata>>>>,
    /// Workspace folders
    pub folders: Arc<RwLock<Vec<WorkspaceFolder>>>,
    /// File watchers
    #[allow(clippy::type_complexity)]
    watchers: Arc<RwLock<HashMap<String, tokio::task::JoinHandle<()>>>>,
    /// Indexing status
    indexing_status: Arc<RwLock<IndexingStatus>>,
    /// Async evaluation service for evaluation-based indexing
    async_evaluation: Option<AsyncEvaluationService>,
}

impl WorkspaceManager {
    /// Create a new workspace manager
    pub fn new(config: Arc<RwLock<LspConfiguration>>) -> Self {
        Self {
            config,
            files: Arc::new(RwLock::new(HashMap::new())),
            symbols: Arc::new(RwLock::new(HashMap::new())),
            folders: Arc::new(RwLock::new(Vec::new())),
            watchers: Arc::new(RwLock::new(HashMap::new())),
            indexing_status: Arc::new(RwLock::new(IndexingStatus::default())),
            async_evaluation: None,
        }
    }

    /// Create a new workspace manager with async evaluation
    pub fn with_async_evaluation(config: Arc<RwLock<LspConfiguration>>) -> Self {
        let async_evaluation = AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        Self {
            config,
            files: Arc::new(RwLock::new(HashMap::new())),
            symbols: Arc::new(RwLock::new(HashMap::new())),
            folders: Arc::new(RwLock::new(Vec::new())),
            watchers: Arc::new(RwLock::new(HashMap::new())),
            indexing_status: Arc::new(RwLock::new(IndexingStatus::default())),
            async_evaluation,
        }
    }

    /// Add workspace folders
    pub async fn add_workspace_folders(&self, folders: Vec<WorkspaceFolder>) {
        let mut current_folders = self.folders.write().await;
        for folder in folders {
            if !current_folders.iter().any(|f| f.uri == folder.uri) {
                current_folders.push(folder);
            }
        }
        drop(current_folders);

        // Start indexing with evaluation support
        self.index_workspace_with_evaluation().await;
    }

    /// Remove workspace folders
    pub async fn remove_workspace_folders(&self, folders: Vec<WorkspaceFolder>) {
        let mut current_folders = self.folders.write().await;
        current_folders.retain(|f| !folders.iter().any(|rf| rf.uri == f.uri));
        drop(current_folders);

        // Re-index remaining folders
        self.index_workspace_with_evaluation().await;
    }

    /// Index workspace with evaluation support
    pub async fn index_workspace_with_evaluation(&self) {
        let folders = self.folders.read().await.clone();
        if folders.is_empty() {
            return;
        }

        let mut status = self.indexing_status.write().await;
        status.indexing = true;
        status.files_indexed = 0;
        status.errors.clear();
        status.evaluation_progress = Some(EvaluationProgress {
            files_evaluated: 0,
            total_files_to_evaluate: 0,
            current_evaluation_time_ms: 0,
            avg_evaluation_time_ms: 0,
        });
        drop(status);

        // Start indexing in background
        let files = self.files.clone();
        let symbols = self.symbols.clone();
        let indexing_status = self.indexing_status.clone();
        let async_evaluation = self.async_evaluation.clone();

        tokio::spawn(async move {
            index_workspace_internal_with_evaluation(
                folders,
                files,
                symbols,
                indexing_status,
                async_evaluation,
            )
            .await;
        });
    }

    /// Index workspace (original method)
    pub async fn index_workspace(&self) {
        let folders = self.folders.read().await.clone();
        if folders.is_empty() {
            return;
        }

        let mut status = self.indexing_status.write().await;
        status.indexing = true;
        status.files_indexed = 0;
        status.errors.clear();
        drop(status);

        // Start indexing in background
        let files = self.files.clone();
        let symbols = self.symbols.clone();
        let indexing_status = self.indexing_status.clone();

        tokio::spawn(async move {
            index_workspace_internal(folders, files, symbols, indexing_status).await;
        });
    }

    /// Get workspace symbols with evaluation metadata
    pub async fn get_workspace_symbols_with_evaluation(
        &self,
        query: &str,
    ) -> Vec<WorkspaceSymbolWithMetadata> {
        let symbols = self.symbols.read().await;
        get_workspace_symbols_with_evaluation(&symbols, query).await
    }

    /// Get workspace symbols (original method)
    pub async fn get_workspace_symbols(&self, query: &str) -> Vec<WorkspaceSymbolWithMetadata> {
        let symbols = self.symbols.read().await;
        let mut result = Vec::new();

        for symbol_list in symbols.values() {
            for symbol in symbol_list {
                if symbol.name.to_lowercase().contains(&query.to_lowercase()) {
                    result.push(symbol.clone());
                }
            }
        }

        result
    }

    /// Find symbol definition with evaluation support
    pub async fn find_symbol_definition_with_evaluation(
        &self,
        symbol_name: &str,
    ) -> Option<tower_lsp::lsp_types::Location> {
        let symbols = self.symbols.read().await;
        find_symbol_definition_with_evaluation(&symbols, symbol_name).await
    }

    /// Find symbol definition (original method)
    pub async fn find_symbol_definition(
        &self,
        symbol_name: &str,
    ) -> Option<tower_lsp::lsp_types::Location> {
        let symbols = self.symbols.read().await;

        for symbol_list in symbols.values() {
            for symbol in symbol_list {
                if symbol.name == symbol_name {
                    return Some(symbol.location.clone());
                }
            }
        }

        None
    }

    /// Find symbol references with evaluation support
    pub async fn find_symbol_references_with_evaluation(
        &self,
        symbol_name: &str,
    ) -> Vec<tower_lsp::lsp_types::Location> {
        let files = self.files.read().await;
        find_symbol_references_with_evaluation(&files, symbol_name).await
    }

    /// Find symbol references (original method)
    pub async fn find_symbol_references(
        &self,
        symbol_name: &str,
    ) -> Vec<tower_lsp::lsp_types::Location> {
        let mut references = Vec::new();
        let files = self.files.read().await;

        for file in files.values() {
            if let Some(program) = &file.ast {
                for declaration in &program.declarations {
                    if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                        if expression_references_symbol(&value_decl.value, symbol_name) {
                            references.push(span_to_location(&declaration.span, &file.uri));
                        }
                    }
                }
            }
        }

        references
    }

    /// Find type definition with evaluation support
    pub async fn find_type_definition_with_evaluation(
        &self,
        symbol_name: &str,
    ) -> Option<tower_lsp::lsp_types::Location> {
        let symbols = self.symbols.read().await;
        find_type_definition_with_evaluation(&symbols, symbol_name).await
    }

    /// Find type definition (original method)
    pub async fn find_type_definition(
        &self,
        symbol_name: &str,
    ) -> Option<tower_lsp::lsp_types::Location> {
        let symbols = self.symbols.read().await;

        for symbol_list in symbols.values() {
            for symbol in symbol_list {
                if symbol.name == symbol_name
                    && symbol.kind == tower_lsp::lsp_types::SymbolKind::TYPE_PARAMETER
                {
                    return Some(symbol.location.clone());
                }
            }
        }

        None
    }

    /// Find implementations with evaluation support
    pub async fn find_implementations_with_evaluation(
        &self,
        symbol_name: &str,
    ) -> Vec<tower_lsp::lsp_types::Location> {
        let symbols = self.symbols.read().await;
        find_implementations_with_evaluation(&symbols, symbol_name).await
    }

    /// Find implementations (original method)
    pub async fn find_implementations(
        &self,
        symbol_name: &str,
    ) -> Vec<tower_lsp::lsp_types::Location> {
        let mut implementations = Vec::new();
        let symbols = self.symbols.read().await;

        for symbol_list in symbols.values() {
            for symbol in symbol_list {
                if symbol.name == symbol_name
                    && symbol.kind == tower_lsp::lsp_types::SymbolKind::METHOD
                {
                    implementations.push(symbol.location.clone());
                }
            }
        }

        implementations
    }

    /// Update file with evaluation support
    pub async fn update_file_with_evaluation(&self, uri: &str, content: String) {
        let mut files = self.files.write().await;
        let mut symbols = self.symbols.write().await;

        update_file_with_evaluation(
            uri,
            content,
            &mut files,
            &mut symbols,
            self.async_evaluation.as_ref(),
        )
        .await;
    }

    /// Update file (original method)
    pub async fn update_file(&self, uri: &str, content: String) {
        let mut files = self.files.write().await;
        let mut symbols = self.symbols.write().await;

        if let Some(file) = files.get_mut(uri) {
            file.content = content.clone();
            file.ast = ligature_parser::parse_program(&content).ok();
            file.last_modified = std::time::SystemTime::now();

            let new_symbols = extract_symbols_from_program(&file.ast, uri);
            symbols.insert(uri.to_string(), new_symbols);
        }
    }

    /// Remove file
    pub async fn remove_file(&self, uri: &str) {
        let mut files = self.files.write().await;
        let mut symbols = self.symbols.write().await;

        files.remove(uri);
        symbols.remove(uri);
    }

    /// Get indexing status
    pub async fn get_indexing_status(&self) -> IndexingStatus {
        self.indexing_status.read().await.clone()
    }

    /// Get workspace stats with evaluation information
    pub async fn get_workspace_stats_with_evaluation(&self) -> WorkspaceStatsWithEvaluation {
        let files = self.files.read().await;
        let symbols = self.symbols.read().await;
        let folders = self.folders.read().await;

        get_workspace_stats_with_evaluation(&files, &symbols, &folders).await
    }

    /// Get workspace stats (original method)
    pub async fn get_workspace_stats(&self) -> WorkspaceStats {
        let files = self.files.read().await;
        let symbols = self.symbols.read().await;
        let folders = self.folders.read().await;

        WorkspaceStats {
            total_files: files.len(),
            total_symbols: symbols.values().map(|s| s.len()).sum(),
            total_size: files.values().map(|f| f.size).sum(),
            folder_count: folders.len(),
        }
    }
}

impl Clone for WorkspaceManager {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            files: self.files.clone(),
            symbols: self.symbols.clone(),
            folders: self.folders.clone(),
            watchers: self.watchers.clone(),
            indexing_status: self.indexing_status.clone(),
            async_evaluation: self.async_evaluation.clone(),
        }
    }
}
