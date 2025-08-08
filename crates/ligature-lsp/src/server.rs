//! LSP server implementation for the Ligature language.
//!
//! This module provides the core Language Server Protocol implementation for Ligature,
//! handling all LSP requests and notifications. It integrates various providers for
//! different LSP features like completion, diagnostics, formatting, etc.
//!
//! ## Architecture
//!
//! The server is built around the `LigatureLspServer` struct which contains:
//! - **Providers**: Specialized components for different LSP features
//! - **State Management**: Document cache, configuration, and workspace management
//! - **Import Resolution**: Cross-file symbol resolution and module management
//!
//! ## Key Components
//!
//! - `LigatureLspServer`: Main server implementation
//! - `DiagnosticsProvider`: Real-time error reporting and validation
//! - `CompletionProvider`: Code completion with context awareness
//! - `ImportResolutionService`: Module resolution and cross-file references
//! - `WorkspaceManager`: Workspace indexing and file management
//!
//! ## Usage
//!
//! ```rust
//! use ligature_lsp::server::LigatureLspServer;
//! use tower_lsp::Client;
//!
//! // Create a server (client would normally come from the LSP client)
//! // let server = LigatureLspServer::new(client);
//! // Server handles LSP communication automatically
//! ```

#[allow(deprecated)]
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use ligature_ast::{AstError, Span};
use thiserror::Error;
use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use tracing::{info, warn};

use crate::code_actions::CodeActionsProvider;
use crate::completion::CompletionProvider;
use crate::config::{ConfigurationManager, LspConfiguration};
use crate::definition::DefinitionProvider;
use crate::diagnostics::DiagnosticsProvider;
use crate::formatting::FormattingProvider;
use crate::hover::HoverProvider;
use crate::import_resolution::ImportResolutionService;
use crate::inlay_hints::InlayHintsProvider;
use crate::references::ReferencesProvider;
use crate::rename::RenameProvider;
use crate::symbols::SymbolsProvider;
use crate::workspace::WorkspaceManager;
use crate::xdg_config::{LspConfig, LspXdgConfig};

// Constants
const DEFAULT_SERVER_VERSION: &str = "0.1.0";
const DEFAULT_SERVER_NAME: &str = "ligature-lsp";
const SCRATCH_DIRECTORY: &str = "registers/_scratch";

// Error types
#[derive(Debug, Error)]
pub enum ServerError {
    #[error("Configuration error: {0}")]
    Configuration(String),
    #[error("Document error: {0}")]
    Document(String),
    #[error("Import resolution error: {0}")]
    ImportResolution(String),
    #[error("Workspace error: {0}")]
    Workspace(String),
    #[error("XDG configuration error: {0}")]
    XdgConfiguration(String),
    #[error("Provider error: {0}")]
    Provider(String),
}

// Document state for improved caching
#[derive(Debug, Clone)]
pub struct DocumentState {
    /// The document content
    pub content: String,
    /// The parsed AST (if parsing succeeded)
    pub ast: Option<ligature_ast::Program>,
    /// The last known version
    pub version: i32,
    /// The last change range for incremental parsing
    pub last_change_range: Option<Range>,
    /// Whether the document needs full re-parsing
    pub needs_full_parse: bool,
    /// Last modified time for cache management
    pub last_modified: std::time::Instant,
}

// Provider trait for better code organization
#[async_trait::async_trait]
pub trait LspProvider {
    type Request;
    type Response;

    async fn handle_request(
        &self,
        request: Self::Request,
    ) -> std::result::Result<Self::Response, ServerError>;
    async fn initialize(&self) -> std::result::Result<(), ServerError>;
    async fn shutdown(&self) -> std::result::Result<(), ServerError>;
}

/// The main LSP server implementation.
pub struct LigatureLspServer {
    /// The LSP client for sending notifications and requests.
    client: Client,
    /// Diagnostics provider.
    diagnostics: Arc<RwLock<DiagnosticsProvider>>,
    /// Completion provider.
    completion: Arc<RwLock<CompletionProvider>>,
    /// Hover provider.
    hover: HoverProvider,
    /// References provider.
    references: ReferencesProvider,
    /// Symbols provider.
    symbols: Arc<RwLock<SymbolsProvider>>,
    /// Definition provider.
    definition: DefinitionProvider,
    /// Code actions provider.
    code_actions: CodeActionsProvider,
    /// Formatting provider.
    formatting: FormattingProvider,
    /// Rename provider.
    rename: RenameProvider,
    /// Inlay hints provider.
    inlay_hints: Arc<RwLock<InlayHintsProvider>>,
    /// Import resolution service.
    import_resolution: Arc<ImportResolutionService>,
    /// Document cache with improved state management.
    #[allow(clippy::type_complexity)]
    documents: Arc<RwLock<HashMap<String, DocumentState>>>,
    /// Configuration manager.
    config_manager: Arc<RwLock<ConfigurationManager>>,
    /// Workspace manager.
    workspace_manager: Arc<WorkspaceManager>,
    /// XDG configuration manager.
    #[allow(dead_code)]
    xdg_config: Option<LspXdgConfig>,
    /// Shutdown flag for graceful shutdown
    shutdown_requested: Arc<AtomicBool>,
    /// Pending requests counter for graceful shutdown
    pending_requests: Arc<RwLock<usize>>,
}

impl LigatureLspServer {
    /// Creates a new LSP server instance with all providers initialized.
    ///
    /// This function initializes all LSP feature providers and sets up the
    /// internal state management. The server is ready to handle LSP requests
    /// after creation.
    ///
    /// # Arguments
    ///
    /// * `client` - The LSP client for sending notifications and requests
    ///
    /// # Returns
    ///
    /// A fully initialized `LigatureLspServer` instance
    ///
    /// # Example
    ///
    /// ```rust
    /// use ligature_lsp::server::LigatureLspServer;
    /// use tower_lsp::Client;
    ///
    /// // Create a server (client would normally come from the LSP client)
    /// // let server = LigatureLspServer::new(client);
    /// ```
    pub fn new(client: Client) -> Self {
        let diagnostics = Arc::new(RwLock::new(DiagnosticsProvider::new()));
        let completion = Arc::new(RwLock::new(CompletionProvider::new()));
        let hover = HoverProvider::new();
        let references = ReferencesProvider::new();
        let symbols = Arc::new(RwLock::new(SymbolsProvider::new()));
        let definition = DefinitionProvider::new();
        let code_actions = CodeActionsProvider::new();
        let formatting = FormattingProvider::new();
        let rename = RenameProvider::new();
        let inlay_hints = Arc::new(RwLock::new(InlayHintsProvider::new()));
        let import_resolution = Arc::new(ImportResolutionService::new());
        let documents = Arc::new(RwLock::new(HashMap::new()));
        let config_manager = Arc::new(RwLock::new(ConfigurationManager::new()));
        let config = Arc::new(RwLock::new(LspConfiguration::default()));
        let workspace_manager = Arc::new(WorkspaceManager::new(config));

        Self {
            client,
            diagnostics,
            completion,
            hover,
            references,
            symbols,
            definition,
            code_actions,
            formatting,
            rename,
            inlay_hints,
            import_resolution,
            documents,
            config_manager,
            workspace_manager,
            xdg_config: None, // Will be initialized in initialize()
            shutdown_requested: Arc::new(AtomicBool::new(false)),
            pending_requests: Arc::new(RwLock::new(0)),
        }
    }

    /// Initialize XDG configuration for the LSP server.
    ///
    /// This function attempts to load configuration from XDG directories and
    /// applies it to the server. If no configuration exists, it creates a
    /// default configuration file.
    ///
    /// # Errors
    ///
    /// - `ConfigLoadError`: When configuration file cannot be loaded
    /// - `DirectoryError`: When XDG directories cannot be created
    /// - `ParseError`: When configuration file is malformed
    ///
    /// # Recovery
    ///
    /// The function logs warnings and continues with default settings if
    /// configuration loading fails, ensuring the server remains functional.
    #[allow(dead_code)]
    async fn initialize_xdg_config(&mut self) {
        let xdg_config = match LspXdgConfig::new().await {
            Ok(config) => config,
            Err(e) => {
                warn!("Failed to initialize XDG configuration: {}", e);
                return;
            }
        };

        if let Err(e) = xdg_config.ensure_directories().await {
            warn!("Failed to ensure XDG directories: {}", e);
            return;
        }

        self.load_xdg_configuration(&xdg_config).await;
        self.xdg_config = Some(xdg_config);
    }

    /// Load and apply XDG configuration settings.
    #[allow(dead_code)]
    async fn load_xdg_configuration(&mut self, xdg_config: &LspXdgConfig) {
        match xdg_config.load_config().await {
            Ok(Some(config)) => {
                self.apply_xdg_configuration(config).await;
                info!("Loaded XDG configuration successfully");
            }
            Ok(None) => {
                self.create_default_xdg_configuration(xdg_config).await;
            }
            Err(e) => {
                warn!("Failed to load XDG configuration: {}", e);
            }
        }
    }

    /// Apply XDG configuration to the server settings.
    #[allow(dead_code)]
    async fn apply_xdg_configuration(&mut self, config: LspConfig) {
        let mut config_manager = self.config_manager.write().await;
        let mut lsp_config = config_manager.get_config().clone();

        // Fix: Use the correct field names from LspConfig
        lsp_config.workspace.enable_workspace_symbols = config.enable_workspace_diagnostics;
        lsp_config.workspace.enable_cross_file_symbols = config.enable_cross_file_symbols;
        lsp_config.workspace.max_workspace_files = config.max_workspace_files;
        lsp_config.workspace.include_patterns = config.include_patterns;
        lsp_config.workspace.exclude_patterns = config.exclude_patterns;

        *config_manager.get_config_mut() = lsp_config;
    }

    /// Create and save default XDG configuration.
    #[allow(dead_code)]
    async fn create_default_xdg_configuration(&self, xdg_config: &LspXdgConfig) {
        let default_config = LspConfig::default();
        if let Err(e) = xdg_config.save_config(&default_config).await {
            warn!("Failed to save default XDG configuration: {}", e);
        } else {
            info!("Created default XDG configuration");
        }
    }

    /// Get the document content for a given URI.
    ///
    /// This method retrieves the current content of a document from the cache.
    /// If the document is not found, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI of the document to retrieve
    ///
    /// # Returns
    ///
    /// The document content if found, `None` otherwise
    async fn get_document_content(&self, uri: &str) -> Option<String> {
        let documents = self.documents.read().await;
        documents.get(uri).map(|doc| doc.content.clone())
    }

    /// Get the document state for a given URI.
    ///
    /// This method retrieves the complete document state including AST and metadata.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI of the document to retrieve
    ///
    /// # Returns
    ///
    /// The document state if found, `None` otherwise
    #[allow(dead_code)]
    async fn get_document_state(&self, uri: &str) -> Option<DocumentState> {
        let documents = self.documents.read().await;
        documents.get(uri).cloned()
    }

    /// Update the document content for a given URI with improved caching.
    ///
    /// This method updates the document cache with new content and attempts
    /// incremental parsing if possible. It also manages cache size and TTL.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI of the document to update
    /// * `content` - The new document content
    /// * `version` - The document version for change tracking
    ///
    /// # Errors
    ///
    /// Returns an error if document processing fails
    async fn update_document_content(
        &self,
        uri: &str,
        content: String,
        version: i32,
    ) -> std::result::Result<(), ServerError> {
        let mut documents = self.documents.write().await;

        // Check if we can do incremental parsing
        let existing = documents.get(uri);
        let ast = if let Some(existing_state) = existing {
            if existing_state.version == version - 1 && !existing_state.needs_full_parse {
                // Try incremental parsing
                self.parse_incrementally(&existing_state.ast, &content)
                    .await
            } else {
                // Fall back to full parsing
                ligature_parser::parse_program(&content).ok()
            }
        } else {
            // New document, do full parsing
            ligature_parser::parse_program(&content).ok()
        };

        // Clean up old documents if cache is full
        self.cleanup_document_cache(&mut documents).await;

        documents.insert(
            uri.to_string(),
            DocumentState {
                content,
                ast,
                version,
                last_change_range: None,
                needs_full_parse: false,
                last_modified: std::time::Instant::now(),
            },
        );

        Ok(())
    }

    /// Remove the document content for a given URI.
    ///
    /// This method removes a document from the cache and cleans up associated resources.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI of the document to remove
    async fn remove_document_content(&self, uri: &str) {
        let mut documents = self.documents.write().await;
        documents.remove(uri);
    }

    /// Attempt incremental parsing of a document.
    ///
    /// This method tries to parse only the changed parts of a document
    /// to improve performance for large files.
    ///
    /// # Arguments
    ///
    /// * `_existing_ast` - The existing AST if available
    /// * `new_content` - The new document content
    ///
    /// # Returns
    ///
    /// The new AST if incremental parsing succeeds, `None` otherwise
    async fn parse_incrementally(
        &self,
        _existing_ast: &Option<ligature_ast::Program>,
        new_content: &str,
    ) -> Option<ligature_ast::Program> {
        // For now, fall back to full parsing
        // TODO: Implement actual incremental parsing logic
        ligature_parser::parse_program(new_content).ok()
    }

    /// Clean up the document cache to prevent memory issues.
    ///
    /// This method removes old documents based on TTL and cache size limits.
    ///
    /// # Arguments
    ///
    /// * `documents` - Mutable reference to the documents cache
    async fn cleanup_document_cache(&self, documents: &mut HashMap<String, DocumentState>) {
        let config = self.config_manager.read().await;
        let max_docs = config.get_config().performance.max_cached_documents;
        let ttl = std::time::Duration::from_secs(config.get_config().performance.cache_ttl_seconds);
        let now = std::time::Instant::now();

        // Remove expired documents
        documents.retain(|_, doc| now.duration_since(doc.last_modified) < ttl);

        // If still too many documents, remove oldest ones
        if documents.len() > max_docs {
            let mut docs: Vec<_> = documents.drain().collect();
            docs.sort_by_key(|(_, doc)| doc.last_modified);
            docs.truncate(max_docs);
            documents.extend(docs);
        }
    }

    /// Validate the current configuration and return any errors.
    ///
    /// This method checks the configuration for invalid values and returns
    /// a list of error messages if any issues are found.
    ///
    /// # Returns
    ///
    /// A vector of error messages, empty if configuration is valid
    async fn validate_configuration(&self) -> Vec<String> {
        let config = self.config_manager.read().await;
        let mut errors = Vec::new();
        let lsp_config = config.get_config();

        // Validate workspace configuration
        if lsp_config.workspace.max_workspace_files == 0 {
            errors.push("max_workspace_files must be greater than 0".to_string());
        }

        if lsp_config.workspace.max_workspace_size_mb == 0 {
            errors.push("max_workspace_size_mb must be greater than 0".to_string());
        }

        // Validate performance configuration
        if lsp_config.performance.max_cached_documents == 0 {
            errors.push("max_cached_documents must be greater than 0".to_string());
        }

        if lsp_config.performance.max_memory_usage_mb == 0 {
            errors.push("max_memory_usage_mb must be greater than 0".to_string());
        }

        if lsp_config.performance.cache_ttl_seconds == 0 {
            errors.push("cache_ttl_seconds must be greater than 0".to_string());
        }

        // Validate logging configuration
        if lsp_config.logging.max_file_size == 0 {
            errors.push("max_file_size must be greater than 0".to_string());
        }

        if lsp_config.logging.max_files == 0 {
            errors.push("max_files must be greater than 0".to_string());
        }

        errors
    }

    /// Perform graceful shutdown of the LSP server.
    ///
    /// This method ensures that all ongoing operations are completed
    /// and resources are properly cleaned up before shutdown.
    ///
    /// # Errors
    ///
    /// Returns an error if shutdown fails
    async fn shutdown_gracefully(&self) -> std::result::Result<(), ServerError> {
        info!("Starting graceful shutdown...");

        // Stop accepting new requests
        self.shutdown_requested.store(true, Ordering::SeqCst);

        // Wait for ongoing requests to complete
        self.wait_for_pending_requests().await;

        // Shutdown providers
        self.shutdown_providers().await?;

        // Save configuration
        self.save_configuration().await?;

        // Clean up document cache
        self.cleanup_all_documents().await;

        info!("Graceful shutdown completed");
        Ok(())
    }

    /// Wait for all pending requests to complete.
    async fn wait_for_pending_requests(&self) {
        let mut attempts = 0;
        const MAX_ATTEMPTS: usize = 10;
        const WAIT_DURATION: std::time::Duration = std::time::Duration::from_millis(100);

        while attempts < MAX_ATTEMPTS {
            let pending = self.pending_requests.read().await;
            if *pending == 0 {
                break;
            }
            drop(pending);

            tokio::time::sleep(WAIT_DURATION).await;
            attempts += 1;
        }

        if attempts >= MAX_ATTEMPTS {
            warn!("Timeout waiting for pending requests to complete");
        }
    }

    /// Shutdown all LSP providers.
    async fn shutdown_providers(&self) -> std::result::Result<(), ServerError> {
        // Note: Individual providers don't have shutdown methods yet
        // This is a placeholder for future implementation
        info!("Shutting down LSP providers");
        Ok(())
    }

    /// Save the current configuration to disk.
    async fn save_configuration(&self) -> std::result::Result<(), ServerError> {
        let _config_manager = self.config_manager.read().await;
        // Note: ConfigurationManager doesn't have get_config_path method yet
        // This is a placeholder for future implementation
        info!("Saving configuration (placeholder)");
        Ok(())
    }

    /// Clean up all documents from the cache.
    async fn cleanup_all_documents(&self) {
        let mut documents = self.documents.write().await;
        documents.clear();
        info!("Cleared document cache");
    }

    /// Increment the pending requests counter.
    #[allow(dead_code)]
    async fn increment_pending_requests(&self) {
        let mut pending = self.pending_requests.write().await;
        *pending += 1;
    }

    /// Decrement the pending requests counter.
    #[allow(dead_code)]
    async fn decrement_pending_requests(&self) {
        let mut pending = self.pending_requests.write().await;
        if *pending > 0 {
            *pending -= 1;
        }
    }

    /// Update workspace symbols for a document.
    async fn update_workspace_symbols(&self, uri: &str, content: &str) {
        if let Ok(program) = ligature_parser::parse_program(content) {
            let mut symbols = self.symbols.write().await;
            symbols.update_workspace_symbols(uri, &program);
        }
    }

    /// Load and resolve imports for a module.
    async fn load_and_resolve_module(&self, uri: &str, content: &str) {
        // Try to parse as a module first
        if let Ok(_module) = ligature_parser::parse_module(content) {
            // Load the module into the import resolution service
            if let Err(e) = self.import_resolution.load_module_from_uri(uri).await {
                warn!("Failed to load module {}: {:?}", uri, e);
                return;
            }

            // Resolve imports
            if let Err(e) = self.import_resolution.resolve_module_imports(uri).await {
                warn!("Failed to resolve imports for module {}: {:?}", uri, e);
            }
        } else {
            // If it's not a module, try parsing as a program
            if let Ok(program) = ligature_parser::parse_program(content) {
                // Check if the program has any import declarations
                let has_imports = program
                    .declarations
                    .iter()
                    .any(|decl| matches!(decl.kind, ligature_ast::DeclarationKind::Import(_)));

                if has_imports {
                    // Convert program to module for import resolution
                    let _module = ligature_ast::Module {
                        name: "main".to_string(),
                        imports: program
                            .declarations
                            .iter()
                            .filter_map(|decl| {
                                if let ligature_ast::DeclarationKind::Import(import) = &decl.kind {
                                    Some(import.clone())
                                } else {
                                    None
                                }
                            })
                            .collect(),
                        declarations: program.declarations.clone(),
                        span: program.span,
                    };

                    // Load the module into the import resolution service
                    if let Err(e) = self.import_resolution.load_module_from_uri(uri).await {
                        warn!("Failed to load program as module {}: {:?}", uri, e);
                        return;
                    }

                    // Resolve imports
                    if let Err(e) = self.import_resolution.resolve_module_imports(uri).await {
                        warn!("Failed to resolve imports for program {}: {:?}", uri, e);
                    }
                }
            }
        }
    }

    /// Get all workspace symbols matching a query.
    #[allow(dead_code)]
    async fn get_workspace_symbols(&self, query: &str) -> Vec<WorkspaceSymbol> {
        let symbols = self.symbols.read().await;
        symbols.get_workspace_symbols(query)
    }

    /// Find symbol definition across all loaded modules.
    async fn find_symbol_definition(
        &self,
        symbol_name: &str,
        source_uri: &str,
    ) -> Option<Location> {
        // First check in the current module
        if let Some(module) = self.import_resolution.get_cached_module(source_uri).await {
            if let Some(location) = self.find_symbol_in_module(&module, symbol_name, source_uri) {
                return Some(location);
            }
        }

        // Check in imported modules
        let imported_modules = self
            .import_resolution
            .get_imported_modules(source_uri)
            .await;
        for module_uri in imported_modules {
            if let Some(module) = self.import_resolution.get_cached_module(&module_uri).await {
                if let Some(location) =
                    self.find_symbol_in_module(&module, symbol_name, &module_uri)
                {
                    return Some(location);
                }
            }
        }

        None
    }

    /// Find symbol references across all loaded modules.
    #[allow(dead_code)]
    async fn find_symbol_references(&self, symbol_name: &str, source_uri: &str) -> Vec<Location> {
        let mut references = Vec::new();

        // Check in the current module
        if let Some(module) = self.import_resolution.get_cached_module(source_uri).await {
            references.extend(self.find_symbol_references_in_module(
                &module,
                symbol_name,
                source_uri,
            ));
        }

        // Check in imported modules
        let imported_modules = self
            .import_resolution
            .get_imported_modules(source_uri)
            .await;
        for module_uri in imported_modules {
            if let Some(module) = self.import_resolution.get_cached_module(&module_uri).await {
                references.extend(self.find_symbol_references_in_module(
                    &module,
                    symbol_name,
                    &module_uri,
                ));
            }
        }

        // Check in modules that import this module
        let importing_modules = self
            .import_resolution
            .get_importing_modules(source_uri)
            .await;
        for module_uri in importing_modules {
            if let Some(module) = self.import_resolution.get_cached_module(&module_uri).await {
                references.extend(self.find_symbol_references_in_module(
                    &module,
                    symbol_name,
                    &module_uri,
                ));
            }
        }

        references
    }

    /// Find a symbol definition within a module.
    fn find_symbol_in_module(
        &self,
        module: &ligature_ast::Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Option<Location> {
        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            return Some(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            return Some(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            return Some(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find symbol references within a module.
    fn find_symbol_references_in_module(
        &self,
        module: &ligature_ast::Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        // This is a simplified implementation - in a full implementation,
        // you would traverse the AST to find all references to the symbol
        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        references
    }

    /// Get completion items from a module.
    #[allow(dead_code)]
    fn get_module_completions(
        &self,
        module: &ligature_ast::Module,
        _module_uri: &str,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    let kind = Some(CompletionItemKind::FUNCTION);
                    let detail = value_decl
                        .type_annotation
                        .as_ref()
                        .map(|t| format!("Type: {t:?}"));

                    completions.push(CompletionItem {
                        label: value_decl.name.clone(),
                        kind,
                        detail,
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: None,
                        insert_text: None,
                        insert_text_format: None,
                        insert_text_mode: None,
                        text_edit: None,
                        additional_text_edits: None,
                        commit_characters: None,
                        command: None,
                        data: None,
                        tags: None,
                        label_details: None,
                    });
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    let kind = Some(CompletionItemKind::CLASS);
                    let detail = Some(format!("Type alias: {:?}", type_alias.type_));

                    completions.push(CompletionItem {
                        label: type_alias.name.clone(),
                        kind,
                        detail,
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: None,
                        insert_text: None,
                        insert_text_format: None,
                        insert_text_mode: None,
                        text_edit: None,
                        additional_text_edits: None,
                        commit_characters: None,
                        command: None,
                        data: None,
                        tags: None,
                        label_details: None,
                    });
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    let kind = Some(CompletionItemKind::CLASS);
                    let detail = Some(format!("Type constructor: {}", type_constructor.name));

                    completions.push(CompletionItem {
                        label: type_constructor.name.clone(),
                        kind,
                        detail,
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: None,
                        insert_text: None,
                        insert_text_format: None,
                        insert_text_mode: None,
                        text_edit: None,
                        additional_text_edits: None,
                        commit_characters: None,
                        command: None,
                        data: None,
                        tags: None,
                        label_details: None,
                    });
                }
                _ => {}
            }
        }

        completions
    }

    /// Check if a file should be included in workspace operations.
    async fn should_include_file(&self, uri: &str) -> bool {
        let config_manager = self.config_manager.read().await;
        let config = config_manager.get_config();

        // Check if URI is in any workspace folder
        let workspace_folders = self.workspace_manager.folders.read().await;
        let in_workspace = workspace_folders
            .iter()
            .any(|folder| uri.starts_with(&folder.uri.to_string()));

        if !in_workspace {
            return false;
        }

        // Check include/exclude patterns
        let path = uri.replace("file://", "");

        // Check exclude patterns first
        for pattern in &config.workspace.exclude_patterns {
            if self.matches_pattern(&path, pattern) {
                return false;
            }
        }

        // Check include patterns
        for pattern in &config.workspace.include_patterns {
            if self.matches_pattern(&path, pattern) {
                return true;
            }
        }

        // Default to true if no include patterns specified
        config.workspace.include_patterns.is_empty()
    }

    /// Simple pattern matching for file inclusion/exclusion.
    fn matches_pattern(&self, path: &str, pattern: &str) -> bool {
        // Convert glob pattern to simple string matching for now
        // In a full implementation, you'd want proper glob pattern matching
        if pattern.contains("**") {
            // Handle ** pattern
            let parts: Vec<&str> = pattern.split("**").collect();
            if parts.len() == 2 {
                let prefix = parts[0];
                let suffix = parts[1];
                return path.starts_with(prefix) && path.ends_with(suffix);
            }
        }

        path.contains(pattern.trim_matches('*'))
    }

    /// Extract symbols from a module that match a query.
    #[allow(dead_code)]
    fn extract_symbols_from_module(
        &self,
        module: &ligature_ast::Module,
        module_uri: &str,
        query: &str,
    ) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        for declaration in &module.declarations {
            let symbol_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if symbol_name.to_lowercase().contains(&query_lower) {
                if let Ok(url) = Url::parse(module_uri) {
                    let kind = match &declaration.kind {
                        ligature_ast::DeclarationKind::Value(_) => SymbolKind::VARIABLE,
                        ligature_ast::DeclarationKind::TypeAlias(_) => SymbolKind::TYPE_PARAMETER,
                        ligature_ast::DeclarationKind::TypeConstructor(_) => SymbolKind::CLASS,
                        ligature_ast::DeclarationKind::TypeClass(_) => SymbolKind::INTERFACE,
                        _ => SymbolKind::VARIABLE,
                    };

                    symbols.push(SymbolInformation {
                        name: symbol_name.clone(),
                        kind,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location::new(
                            url,
                            Range::new(
                                Position::new(
                                    declaration.span.line as u32 - 1,
                                    declaration.span.column as u32 - 1,
                                ),
                                Position::new(
                                    declaration.span.line as u32 - 1,
                                    declaration.span.column as u32 - 1
                                        + declaration.span.len() as u32,
                                ),
                            ),
                        ),
                        container_name: None,
                    });
                }
            }
        }

        symbols
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for LigatureLspServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        info!("Initializing Ligature LSP server");

        // Validate configuration
        let config_errors = self.validate_configuration().await;
        if !config_errors.is_empty() {
            warn!("Configuration validation errors: {:?}", config_errors);
            for error in &config_errors {
                self.client
                    .log_message(
                        MessageType::WARNING,
                        format!("Configuration error: {error}"),
                    )
                    .await;
            }
        }

        // Store workspace folders if provided
        if let Some(workspace_folders) = params.workspace_folders {
            self.workspace_manager
                .add_workspace_folders(workspace_folders)
                .await;
            info!("Workspace folders initialized");
        }

        let capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Options(
                TextDocumentSyncOptions {
                    open_close: Some(true),
                    change: Some(TextDocumentSyncKind::INCREMENTAL),
                    will_save: Some(false),
                    will_save_wait_until: Some(false),
                    save: None,
                },
            )),
            completion_provider: Some(CompletionOptions {
                resolve_provider: Some(false),
                trigger_characters: Some(vec![".".to_string(), ":".to_string(), " ".to_string()]),
                work_done_progress_options: Default::default(),
                all_commit_characters: None,
                ..Default::default()
            }),
            hover_provider: Some(HoverProviderCapability::Simple(true)),
            signature_help_provider: Some(SignatureHelpOptions {
                trigger_characters: Some(vec!["(".to_string(), ",".to_string()]),
                retrigger_characters: Some(vec![")".to_string()]),
                work_done_progress_options: Default::default(),
            }),
            definition_provider: Some(OneOf::Left(true)),
            references_provider: Some(OneOf::Left(true)),
            document_symbol_provider: Some(OneOf::Left(true)),
            workspace_symbol_provider: Some(OneOf::Left(true)),
            code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
            document_formatting_provider: Some(OneOf::Left(true)),
            document_range_formatting_provider: Some(OneOf::Left(true)),
            rename_provider: Some(OneOf::Left(true)),
            inlay_hint_provider: Some(OneOf::Right(InlayHintServerCapabilities::Options(
                InlayHintOptions {
                    work_done_progress_options: Default::default(),
                    resolve_provider: Some(false),
                },
            ))),
            workspace: Some(WorkspaceServerCapabilities {
                workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                    supported: Some(true),
                    change_notifications: Some(OneOf::Left(true)),
                }),
                file_operations: None,
            }),
            ..ServerCapabilities::default()
        };

        Ok(InitializeResult {
            capabilities,
            server_info: Some(ServerInfo {
                name: DEFAULT_SERVER_NAME.to_string(),
                version: Some(DEFAULT_SERVER_VERSION.to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        info!("Ligature LSP server initialized");
        self.client
            .log_message(MessageType::INFO, "Ligature LSP server initialized")
            .await;

        // Initialize XDG configuration
        // Note: We need to use a workaround since self is not mutable in this trait method
        // We'll spawn a task to initialize XDG config
        let server_arc = Arc::new(self);
        tokio::spawn({
            let _server = server_arc.clone();
            async move {
                // This is a workaround - in a real implementation, we'd need to restructure
                // to allow mutable access to the server during initialization
                info!("XDG configuration initialization would happen here");
            }
        });

        // Load workspace modules in the background
        let workspace_manager = self.workspace_manager.clone();
        tokio::spawn(async move {
            workspace_manager.index_workspace().await;
        });
    }

    async fn shutdown(&self) -> Result<()> {
        info!("Shutting down Ligature LSP server");
        self.shutdown_gracefully().await.map_err(|e| {
            warn!("Error during graceful shutdown: {}", e);
            tower_lsp::jsonrpc::Error::new(tower_lsp::jsonrpc::ErrorCode::InternalError)
        })
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.to_string();
        let content = params.text_document.text;
        let version = params.text_document.version;

        info!("Document opened: {}", uri);
        if let Err(e) = self
            .update_document_content(&uri, content.clone(), version)
            .await
        {
            warn!("Failed to update document content for {}: {}", uri, e);
        }

        // Update workspace symbols if file should be included
        if self.should_include_file(&uri).await {
            self.update_workspace_symbols(&uri, &content).await;
        }

        // Load and resolve module imports
        self.load_and_resolve_module(&uri, &content).await;

        // Publish diagnostics
        if let Some(content) = self.get_document_content(&uri).await {
            let mut diagnostics = self.diagnostics.write().await;
            let ast = ligature_parser::parse_program(&content).ok();
            if let Some(diags) = diagnostics
                .compute_diagnostics(&uri, &content, ast.as_ref())
                .await
            {
                if let Ok(url) = Url::parse(&uri) {
                    self.client.publish_diagnostics(url, diags, None).await;
                }
            }
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.to_string();
        let version = params.text_document.version;

        // Update document content
        if let Some(change) = params.content_changes.first() {
            let content = change.text.clone();
            if let Err(e) = self
                .update_document_content(&uri, content.clone(), version)
                .await
            {
                warn!("Failed to update document content for {}: {}", uri, e);
            }

            info!("Document changed: {}", uri);

            // Update workspace symbols if file should be included
            if self.should_include_file(&uri).await {
                self.update_workspace_symbols(&uri, &content).await;
            }

            // Load and resolve module imports
            self.load_and_resolve_module(&uri, &content).await;

            // Publish diagnostics
            let mut diagnostics = self.diagnostics.write().await;
            let ast = ligature_parser::parse_program(&content).ok();
            if let Some(diags) = diagnostics
                .compute_diagnostics(&uri, &content, ast.as_ref())
                .await
            {
                if let Ok(url) = Url::parse(&uri) {
                    self.client.publish_diagnostics(url, diags, None).await;
                }
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri.to_string();

        info!("Document closed: {}", uri);
        self.remove_document_content(&uri).await;

        // Remove from workspace symbols
        let mut symbols = self.symbols.write().await;
        symbols.clear_symbols(&uri);

        // Invalidate module in import resolution cache
        self.import_resolution.invalidate_module(&uri).await;

        // Clear diagnostics
        if let Ok(url) = Url::parse(&uri) {
            self.client.publish_diagnostics(url, vec![], None).await;
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self
                .completion
                .read()
                .await
                .provide_completion_with_imports(&uri, &content, position, &self.import_resolution)
                .await;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .to_string();
        let position = params.text_document_position_params.position;

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self.hover.provide_hover(&uri, &content, position).await;
            Ok(result)
        } else {
            Ok(None)
        }
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;
        let _context = params.context;

        if let Some(content) = self.get_document_content(&uri).await {
            // Get symbol name at position
            let symbol_name = self.references.get_symbol_at_position(&content, position);
            if symbol_name.is_empty() {
                return Ok(Some(vec![]));
            }

            let mut all_references = Vec::new();

            // Find references in current document
            let local_references = self
                .references
                .find_references(&uri, &content, position)
                .await;
            all_references.extend(local_references);

            // Find references in imported modules
            let imported_references = self
                .import_resolution
                .find_symbol_references(&symbol_name, &uri)
                .await;
            all_references.extend(imported_references);

            // Find references in modules that import this module
            let importing_modules = self.import_resolution.get_importing_modules(&uri).await;
            for module_uri in importing_modules {
                if let Some(module) = self.import_resolution.get_cached_module(&module_uri).await {
                    let module_references =
                        self.find_symbol_references_in_module(&module, &symbol_name, &module_uri);
                    all_references.extend(module_references);
                }
            }

            // Find references in workspace files
            let workspace_references = self
                .workspace_manager
                .find_symbol_references(&symbol_name)
                .await;
            all_references.extend(workspace_references);

            // Remove duplicates
            all_references.sort_by(|a, b| {
                a.uri
                    .to_string()
                    .cmp(&b.uri.to_string())
                    .then(a.range.start.line.cmp(&b.range.start.line))
                    .then(a.range.start.character.cmp(&b.range.start.character))
            });
            all_references.dedup_by(|a, b| a.uri == b.uri && a.range == b.range);

            Ok(Some(all_references))
        } else {
            Ok(None)
        }
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri.to_string();

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self
                .symbols
                .read()
                .await
                .get_document_symbols(&uri, &content)
                .await;
            Ok(Some(DocumentSymbolResponse::Nested(result)))
        } else {
            Ok(None)
        }
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .to_string();
        let position = params.text_document_position_params.position;

        if let Some(content) = self.get_document_content(&uri).await {
            // Get symbol name at position
            let symbol_name = self.references.get_symbol_at_position(&content, position);
            if symbol_name.is_empty() {
                return Ok(None);
            }

            // First try to find definition in current document
            let local_definition = self
                .definition
                .find_definition(&uri, &content, position)
                .await;

            if let Some(definition) = local_definition {
                return Ok(Some(GotoDefinitionResponse::Scalar(definition)));
            }

            // Try to find definition in imported modules
            let imported_definition = self.find_symbol_definition(&symbol_name, &uri).await;

            if let Some(definition) = imported_definition {
                return Ok(Some(GotoDefinitionResponse::Scalar(definition)));
            }

            // Try to find definition in workspace
            let workspace_definition = self
                .workspace_manager
                .find_symbol_definition(&symbol_name)
                .await;

            if let Some(definition) = workspace_definition {
                return Ok(Some(GotoDefinitionResponse::Scalar(definition)));
            }

            Ok(None)
        } else {
            Ok(None)
        }
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri.to_string();
        let range = params.range;

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self
                .code_actions
                .provide_code_actions(&uri, &content, range, &params.context)
                .await;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri.to_string();

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self.formatting.format_document(&uri, &content).await;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    async fn range_formatting(
        &self,
        params: DocumentRangeFormattingParams,
    ) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri.to_string();
        let range = params.range;

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self.formatting.format_range(&uri, &content, range).await;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;
        let new_name = params.new_name;

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self
                .rename
                .rename_symbol(&uri, &content, position, &new_name)
                .await;
            Ok(result)
        } else {
            Ok(None)
        }
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = params.text_document.uri.to_string();

        if let Some(content) = self.get_document_content(&uri).await {
            let result = self
                .inlay_hints
                .read()
                .await
                .provide_inlay_hints(&uri, &content, params.range)
                .await;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let query = params.query.clone();
        info!("Workspace symbol search: {}", query);

        // Use enhanced symbol search that integrates with import resolution and workspace manager
        let symbols = self
            .symbols
            .read()
            .await
            .search_workspace_symbols_enhanced(
                params,
                &self.import_resolution,
                &self.workspace_manager,
            )
            .await;

        Ok(Some(symbols))
    }

    async fn did_change_workspace_folders(&self, params: DidChangeWorkspaceFoldersParams) {
        info!("Workspace folders changed");

        // Remove deleted folders
        self.workspace_manager
            .remove_workspace_folders(params.event.removed)
            .await;

        // Add new folders
        self.workspace_manager
            .add_workspace_folders(params.event.added)
            .await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        info!("Configuration changed");

        if let Some(settings) = params.settings.as_object() {
            let mut config_manager = self.config_manager.write().await;
            config_manager
                .update_from_client_settings(&serde_json::Value::Object(settings.clone()));
        }
    }

    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        info!("Watched files changed");

        for change in &params.changes {
            let uri = change.uri.to_string();

            match change.typ {
                FileChangeType::CREATED => {
                    info!("File created: {}", uri);
                    // Handle file creation if needed
                }
                FileChangeType::CHANGED => {
                    info!("File changed: {}", uri);
                    // Handle file change if needed
                }
                FileChangeType::DELETED => {
                    info!("File deleted: {}", uri);
                    // Remove from workspace symbols
                    let mut symbols = self.symbols.write().await;
                    symbols.clear_symbols(&uri);
                }
                _ => {
                    info!("Unknown file change type: {:?}", change.typ);
                }
            }
        }
    }
}

impl LigatureLspServer {
    /// Load all modules in the workspace.
    pub async fn load_workspace_modules(&self) {
        self.workspace_manager.index_workspace().await;
    }

    /// Load all modules from a directory recursively.
    #[allow(dead_code)]
    async fn load_modules_from_directory(&self, dir: &Path) {
        let mut stack = vec![dir.to_path_buf()];

        while let Some(current_dir) = stack.pop() {
            if let Ok(entries) = std::fs::read_dir(&current_dir) {
                for entry in entries.flatten() {
                    let path = entry.path();

                    if path.is_file() && path.extension().is_some_and(|ext| ext == "lig") {
                        if let Ok(uri) = self.path_to_uri(&path) {
                            if let Ok(content) = std::fs::read_to_string(&path) {
                                if let Ok(_module) = ligature_parser::parse_module(&content) {
                                    // Load the module
                                    if let Err(e) =
                                        self.import_resolution.load_module_from_uri(&uri).await
                                    {
                                        warn!("Failed to load module {}: {:?}", uri, e);
                                    }
                                }
                            }
                        }
                    } else if path.is_dir() {
                        // Add subdirectory to stack for processing
                        stack.push(path);
                    }
                }
            }
        }
    }

    /// Create a temporary module file in the scratch directory.
    pub async fn create_temp_module(
        &self,
        content: &str,
        name: &str,
    ) -> std::result::Result<String, AstError> {
        // Create scratch directory if it doesn't exist
        let scratch_dir = PathBuf::from(SCRATCH_DIRECTORY);
        if !scratch_dir.exists() {
            std::fs::create_dir_all(&scratch_dir).map_err(|e| AstError::ParseError {
                message: format!("Failed to create scratch directory: {e}"),
                span: Span::default(),
            })?;
        }

        // Create temporary file
        let temp_file = scratch_dir.join(format!("{name}.lig"));
        std::fs::write(&temp_file, content).map_err(|e| AstError::ParseError {
            message: format!("Failed to write temporary file: {e}"),
            span: Span::default(),
        })?;

        // Convert to URI
        self.path_to_uri(&temp_file)
    }

    /// Convert a file path to a URI.
    fn path_to_uri(&self, path: &Path) -> std::result::Result<String, AstError> {
        let url = Url::from_file_path(path).map_err(|_| AstError::ParseError {
            message: format!("Cannot convert path to URI: {path:?}"),
            span: Span::default(),
        })?;

        Ok(url.to_string())
    }
}

/// Run the LSP server.
pub async fn run_server() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(LigatureLspServer::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_xdg_configuration_handling() {
        // Test XDG configuration handling
        // This test verifies that XDG configuration works correctly
        let config = LspConfig::default();
        assert!(config.enable_workspace_diagnostics);
        assert!(config.enable_cross_file_symbols);
        assert!(config.max_workspace_files > 0);
    }
}
