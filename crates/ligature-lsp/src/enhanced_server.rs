//! Enhanced LSP server implementation for the Ligature language with improved features.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use tracing::{info, warn};

use crate::{
    code_actions::CodeActionsProvider,
    definition::DefinitionProvider,
    enhanced_completion::EnhancedCompletionProvider,
    enhanced_diagnostics::EnhancedDiagnosticsProvider,
    formatting::FormattingProvider,
    hover::HoverProvider,
    import_resolution::ImportResolutionService,
    inlay_hints::InlayHintsProvider,
    references::ReferencesProvider,
    rename::RenameProvider,
    symbols::SymbolsProvider,
    xdg_config::{LspConfig, LspXdgConfig},
};
use ligature_ast::{AstError, Module, Span};

/// Enhanced LSP server implementation with improved features.
pub struct EnhancedLigatureLspServer {
    /// The LSP client for sending notifications and requests.
    client: Client,
    /// Enhanced diagnostics provider.
    diagnostics: Arc<RwLock<EnhancedDiagnosticsProvider>>,
    /// Enhanced completion provider.
    completion: Arc<RwLock<EnhancedCompletionProvider>>,
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
    /// Document cache.
    documents: Arc<RwLock<HashMap<String, String>>>,
    /// Workspace folders.
    workspace_folders: Arc<RwLock<Vec<WorkspaceFolder>>>,
    /// Enhanced workspace configuration.
    workspace_config: Arc<RwLock<EnhancedWorkspaceConfiguration>>,
    /// XDG configuration manager.
    xdg_config: Option<LspXdgConfig>,
}

/// Enhanced workspace configuration for the LSP server.
#[derive(Debug, Clone)]
pub struct EnhancedWorkspaceConfiguration {
    /// Whether to enable workspace-wide diagnostics.
    pub enable_workspace_diagnostics: bool,
    /// Whether to enable cross-file symbol resolution.
    pub enable_cross_file_symbols: bool,
    /// Maximum number of files to scan for workspace symbols.
    pub max_workspace_files: usize,
    /// File patterns to include in workspace operations.
    pub include_patterns: Vec<String>,
    /// File patterns to exclude from workspace operations.
    pub exclude_patterns: Vec<String>,
    /// Enhanced diagnostics configuration.
    pub diagnostics_config: crate::enhanced_diagnostics::EnhancedDiagnosticsConfig,
    /// Enhanced completion configuration.
    pub completion_config: crate::enhanced_completion::EnhancedCompletionConfig,
    /// Whether to enable real-time error reporting.
    pub enable_real_time_errors: bool,
    /// Whether to enable performance monitoring.
    pub enable_performance_monitoring: bool,
    /// Whether to enable advanced refactoring.
    pub enable_advanced_refactoring: bool,
}

impl Default for EnhancedWorkspaceConfiguration {
    fn default() -> Self {
        Self {
            enable_workspace_diagnostics: true,
            enable_cross_file_symbols: true,
            max_workspace_files: 1000,
            include_patterns: vec!["**/*.lig".to_string()],
            exclude_patterns: vec!["**/target/**".to_string(), "**/node_modules/**".to_string()],
            diagnostics_config: crate::enhanced_diagnostics::EnhancedDiagnosticsConfig::default(),
            completion_config: crate::enhanced_completion::EnhancedCompletionConfig::default(),
            enable_real_time_errors: true,
            enable_performance_monitoring: true,
            enable_advanced_refactoring: true,
        }
    }
}

impl EnhancedLigatureLspServer {
    /// Create a new enhanced LSP server instance.
    pub fn new(client: Client) -> Self {
        let diagnostics = Arc::new(RwLock::new(EnhancedDiagnosticsProvider::new()));
        let completion = Arc::new(RwLock::new(EnhancedCompletionProvider::new()));
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
        let workspace_folders = Arc::new(RwLock::new(Vec::new()));
        let workspace_config = Arc::new(RwLock::new(EnhancedWorkspaceConfiguration::default()));

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
            workspace_folders,
            workspace_config,
            xdg_config: None,
        }
    }

    /// Initialize XDG configuration.
    async fn initialize_xdg_config(&mut self) {
        match LspXdgConfig::new().await {
            Ok(config) => {
                self.xdg_config = Some(config);
                info!("XDG configuration initialized successfully");
            }
            Err(e) => {
                warn!("Failed to initialize XDG configuration: {}", e);
            }
        }
    }

    /// Get document content from cache.
    async fn get_document_content(&self, uri: &str) -> Option<String> {
        self.documents.read().await.get(uri).cloned()
    }

    /// Update document content in cache.
    async fn update_document_content(&self, uri: &str, content: String) {
        self.documents
            .write()
            .await
            .insert(uri.to_string(), content);
    }

    /// Remove document content from cache.
    async fn remove_document_content(&self, uri: &str) {
        self.documents.write().await.remove(uri);
    }

    /// Update workspace symbols when a document changes.
    async fn update_workspace_symbols(&self, uri: &str, content: &str) {
        if let Ok(program) = ligature_parser::parse_program(content) {
            self.symbols
                .write()
                .await
                .update_workspace_symbols(uri, &program);
        }
    }

    /// Load and resolve a module.
    async fn load_and_resolve_module(&self, uri: &str, content: &str) {
        if let Ok(program) = ligature_parser::parse_program(content) {
            // Process imports and resolve dependencies
            for declaration in &program.declarations {
                if let ligature_ast::DeclarationKind::Import(import_decl) = &declaration.kind {
                    let module_path = &import_decl.path;
                    if let Err(e) = self.import_resolution.resolve_module_imports(uri).await {
                        warn!("Failed to resolve import {}: {}", module_path, e);
                    }
                }
            }
        }
    }

    /// Get workspace symbols.
    async fn get_workspace_symbols(&self, query: &str) -> Vec<WorkspaceSymbol> {
        self.symbols.read().await.get_workspace_symbols(query)
    }

    /// Find symbol definition.
    async fn find_symbol_definition(
        &self,
        symbol_name: &str,
        source_uri: &str,
    ) -> Option<Location> {
        // First, try to find in the current document
        if let Some(content) = self.get_document_content(source_uri).await {
            if let Ok(program) = ligature_parser::parse_program(&content) {
                // Implement symbol finding in program
                if let Some(location) =
                    self.find_symbol_in_program(&program, symbol_name, source_uri)
                {
                    return Some(location);
                }
            }
        }

        // Then, try to find in imported modules
        if let Some(module) = self.import_resolution.get_cached_module(source_uri).await {
            if let Some(location) = self.find_symbol_in_module(&module, symbol_name, source_uri) {
                return Some(location);
            }
        }

        // Try to find in workspace
        let workspace_symbols = self.get_workspace_symbols(symbol_name).await;
        for symbol in workspace_symbols {
            if symbol.name == symbol_name {
                if let lsp_types::OneOf::Left(location) = symbol.location {
                    return Some(location);
                }
            }
        }

        None
    }

    /// Find symbol in program.
    fn find_symbol_in_program(
        &self,
        program: &ligature_ast::Program,
        symbol_name: &str,
        uri: &str,
    ) -> Option<Location> {
        for declaration in &program.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        return Some(Location {
                            uri: uri.parse().unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: declaration.span.column as u32 - 1,
                                },
                                end: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32
                                        - 1,
                                },
                            },
                        });
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_decl) => {
                    if type_decl.name == symbol_name {
                        return Some(Location {
                            uri: uri.parse().unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: declaration.span.column as u32 - 1,
                                },
                                end: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32
                                        - 1,
                                },
                            },
                        });
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => {
                    if type_ctor.name == symbol_name {
                        return Some(Location {
                            uri: uri.parse().unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: declaration.span.column as u32 - 1,
                                },
                                end: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32
                                        - 1,
                                },
                            },
                        });
                    }
                }
                ligature_ast::DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        return Some(Location {
                            uri: uri.parse().unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: declaration.span.column as u32 - 1,
                                },
                                end: Position {
                                    line: declaration.span.line as u32 - 1,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32
                                        - 1,
                                },
                            },
                        });
                    }
                }
                _ => continue,
            }
        }
        None
    }

    /// Find symbol references.
    async fn find_symbol_references(&self, symbol_name: &str, source_uri: &str) -> Vec<Location> {
        let mut references = Vec::new();

        // Find references in the current document
        if let Some(content) = self.get_document_content(source_uri).await {
            if let Ok(program) = ligature_parser::parse_program(&content) {
                // Implement symbol references in program
                references.extend(self.find_symbol_references_in_program(
                    &program,
                    symbol_name,
                    source_uri,
                ));
            }
        }

        // Find references in workspace files
        let workspace_config = self.workspace_config.read().await;
        if workspace_config.enable_cross_file_symbols {
            // Find references in imported modules
            let loaded_modules = self.import_resolution.get_loaded_modules().await;
            for module_uri in loaded_modules {
                if let Some(module) = self.import_resolution.get_cached_module(&module_uri).await {
                    references.extend(self.find_symbol_references_in_module(
                        &module,
                        symbol_name,
                        &module_uri,
                    ));
                }
            }
        }

        references
    }

    /// Find symbol references in program.
    fn find_symbol_references_in_program(
        &self,
        program: &ligature_ast::Program,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        // Find references in expressions
        for declaration in &program.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if let Some(expr) = &value_decl.value {
                        references.extend(self.find_symbol_references_in_expression(
                            expr,
                            symbol_name,
                            uri,
                        ));
                    }
                }
                _ => continue,
            }
        }

        references
    }

    /// Find symbol references in expression.
    fn find_symbol_references_in_expression(
        &self,
        expr: &ligature_ast::Expr,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        match &expr.kind {
            ligature_ast::ExprKind::Identifier(name) => {
                if name == symbol_name {
                    references.push(Location {
                        uri: uri.parse().unwrap_or_else(|_| "file:///".parse().unwrap()),
                        range: Range {
                            start: Position {
                                line: expr.span.line as u32 - 1,
                                character: expr.span.column as u32 - 1,
                            },
                            end: Position {
                                line: expr.span.line as u32 - 1,
                                character: (expr.span.column + expr.span.len()) as u32 - 1,
                            },
                        },
                    });
                }
            }
            ligature_ast::ExprKind::Application {
                function,
                arguments,
            } => {
                references.extend(self.find_symbol_references_in_expression(
                    function,
                    symbol_name,
                    uri,
                ));
                for arg in arguments {
                    references.extend(self.find_symbol_references_in_expression(
                        arg,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ligature_ast::ExprKind::BinaryOp { left, right, .. } => {
                references.extend(self.find_symbol_references_in_expression(
                    left,
                    symbol_name,
                    uri,
                ));
                references.extend(self.find_symbol_references_in_expression(
                    right,
                    symbol_name,
                    uri,
                ));
            }
            ligature_ast::ExprKind::UnaryOp { operand, .. } => {
                references.extend(self.find_symbol_references_in_expression(
                    operand,
                    symbol_name,
                    uri,
                ));
            }
            ligature_ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                references.extend(self.find_symbol_references_in_expression(
                    condition,
                    symbol_name,
                    uri,
                ));
                references.extend(self.find_symbol_references_in_expression(
                    then_branch,
                    symbol_name,
                    uri,
                ));
                if let Some(else_expr) = else_branch {
                    references.extend(self.find_symbol_references_in_expression(
                        else_expr,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ligature_ast::ExprKind::Let { value, body, .. } => {
                references.extend(self.find_symbol_references_in_expression(
                    value,
                    symbol_name,
                    uri,
                ));
                references.extend(self.find_symbol_references_in_expression(
                    body,
                    symbol_name,
                    uri,
                ));
            }
            ligature_ast::ExprKind::Lambda { body, .. } => {
                references.extend(self.find_symbol_references_in_expression(
                    body,
                    symbol_name,
                    uri,
                ));
            }
            ligature_ast::ExprKind::Match { scrutinee, cases } => {
                references.extend(self.find_symbol_references_in_expression(
                    scrutinee,
                    symbol_name,
                    uri,
                ));
                for case in cases {
                    references.extend(self.find_symbol_references_in_expression(
                        &case.body,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ligature_ast::ExprKind::FieldAccess { record, .. } => {
                references.extend(self.find_symbol_references_in_expression(
                    record,
                    symbol_name,
                    uri,
                ));
            }
            ligature_ast::ExprKind::Record { fields } => {
                for field in fields {
                    references.extend(self.find_symbol_references_in_expression(
                        &field.value,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ligature_ast::ExprKind::Literal(_) => {
                // No symbol references in literals
            }
        }

        references
    }

    /// Find symbol in module.
    fn find_symbol_in_module(
        &self,
        module: &Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Option<Location> {
        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        return Some(Location {
                            uri: module_uri
                                .parse()
                                .unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32,
                                    character: declaration.span.column as u32,
                                },
                                end: Position {
                                    line: declaration.span.line as u32,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32,
                                },
                            },
                        });
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_decl) => {
                    if type_decl.name == symbol_name {
                        return Some(Location {
                            uri: module_uri
                                .parse()
                                .unwrap_or_else(|_| "file:///".parse().unwrap()),
                            range: Range {
                                start: Position {
                                    line: declaration.span.line as u32,
                                    character: declaration.span.column as u32,
                                },
                                end: Position {
                                    line: declaration.span.line as u32,
                                    character: (declaration.span.column + declaration.span.len())
                                        as u32,
                                },
                            },
                        });
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find symbol references in module.
    fn find_symbol_references_in_module(
        &self,
        module: &Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        // This is a simplified implementation
        // In a full implementation, you would traverse the AST to find all references

        references
    }

    /// Check if a file should be included in workspace operations.
    async fn should_include_file(&self, uri: &str) -> bool {
        let workspace_config = self.workspace_config.read().await;

        // Check if the file matches any include patterns
        let mut should_include = workspace_config.include_patterns.is_empty();
        for pattern in &workspace_config.include_patterns {
            if self.matches_pattern(uri, pattern) {
                should_include = true;
                break;
            }
        }

        // Check if the file matches any exclude patterns
        for pattern in &workspace_config.exclude_patterns {
            if self.matches_pattern(uri, pattern) {
                should_include = false;
                break;
            }
        }

        should_include
    }

    /// Check if a path matches a pattern.
    fn matches_pattern(&self, path: &str, pattern: &str) -> bool {
        // This is a simplified implementation
        // In a full implementation, you would use proper glob matching
        path.contains(pattern.trim_start_matches("**/").trim_end_matches("/**"))
    }
}

impl LanguageServer for EnhancedLigatureLspServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        info!("Initializing enhanced Ligature LSP server");

        // Update workspace configuration from client capabilities
        if let Some(_capabilities) = &params.capabilities {
            let mut workspace_config = self.workspace_config.write().await;

            // Check if the client supports enhanced features
            if let Some(text_document) = &capabilities.text_document {
                if let Some(completion) = &text_document.completion {
                    workspace_config.completion_config.enable_context_aware =
                        completion.context_support.unwrap_or(false);
                }

                if let Some(diagnostic) = &text_document.diagnostic {
                    workspace_config
                        .diagnostics_config
                        .enable_detailed_explanations =
                        diagnostic.related_document_support.unwrap_or(false);
                }
            }
        }

        // Store workspace folders
        if let Some(folders) = params.workspace_folders {
            *self.workspace_folders.write().await = folders;
        }

        // Initialize XDG configuration
        let mut server = self.clone();
        tokio::spawn(async move {
            server.initialize_xdg_config().await;
        });

        Ok(InitializeResult {
            server_info: Some(ServerInfo {
                name: "ligature-lsp".to_string(),
                version: Some("1.0.0".to_string()),
            }),
            capabilities: ServerCapabilities {
                position_encoding: None,
                workspace_symbol_provider: Some(OneOf::Left(true)),
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        will_save: Some(true),
                        will_save_wait_until: Some(true),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(true),
                        })),
                    },
                )),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                    all_commit_characters: Some(vec![".".to_string(), ":".to_string()]),
                    resolve_provider: Some(true),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                    trigger_characters: Some(vec![
                        ".".to_string(),
                        ":".to_string(),
                        "(".to_string(),
                        " ".to_string(),
                    ]),
                    all_commit_characters: None,
                    completion_item: None,
                }),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                signature_help_provider: None,
                declaration_provider: None,
                definition_provider: Some(OneOf::Left(true)),
                type_definition_provider: None,
                implementation_provider: None,
                references_provider: Some(OneOf::Left(true)),
                document_highlight_provider: None,
                document_symbol_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Options(
                    CodeActionOptions {
                        code_action_kinds: Some(vec![
                            CodeActionKind::QUICKFIX,
                            CodeActionKind::REFACTOR,
                            CodeActionKind::REFACTOR_EXTRACT,
                            CodeActionKind::REFACTOR_INLINE,
                            CodeActionKind::REFACTOR_REWRITE,
                            CodeActionKind::SOURCE,
                            CodeActionKind::SOURCE_ORGANIZE_IMPORTS,
                        ]),
                        resolve_provider: Some(true),
                        work_done_progress_options: WorkDoneProgressOptions {
                            work_done_progress: Some(true),
                        },
                    },
                )),
                code_lens_provider: None,
                document_link_provider: None,
                color_provider: None,
                document_formatting_provider: Some(OneOf::Left(true)),
                document_range_formatting_provider: Some(OneOf::Left(true)),
                document_on_type_formatting_provider: None,
                rename_provider: Some(OneOf::Left(true)),
                folding_range_provider: None,
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec![
                        "ligature.extractFunction".to_string(),
                        "ligature.inlineVariable".to_string(),
                        "ligature.renameSymbol".to_string(),
                        "ligature.organizeImports".to_string(),
                        "ligature.fixAll".to_string(),
                    ],
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: Some(true),
                    },
                }),
                selection_range_provider: None,
                linked_editing_range_provider: None,
                call_hierarchy_provider: None,
                semantic_tokens_provider: None,
                moniker_provider: None,
                // type_hierarchy_provider: None, // Not available in current LSP types
                inline_value_provider: None,
                inlay_hint_provider: Some(OneOf::Left(true)),
                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: Some("ligature".to_string()),
                        inter_file_dependencies: true,
                        workspace_diagnostics: true,
                        work_done_progress_options: WorkDoneProgressOptions {
                            work_done_progress: Some(true),
                        },
                    },
                )),
                workspace: Some(WorkspaceServerCapabilities {
                    workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                        supported: Some(true),
                        change_notifications: Some(OneOf::Left(true)),
                    }),
                    file_operations: None,
                }),
                experimental: None,
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        info!("Enhanced Ligature LSP server initialized");

        // Load workspace modules
        self.load_workspace_modules().await;

        // Send a notification that the server is ready
        if let Err(_e) = self
            .client
            .log_message(MessageType::INFO, "Enhanced Ligature LSP server is ready")
            .await
        {
            warn!("Failed to send ready notification");
        }
    }

    async fn shutdown(&self) -> Result<()> {
        info!("Shutting down enhanced Ligature LSP server");
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.to_string();
        let content = params.text_document.text;

        info!("Document opened: {}", uri);

        // Update document content
        self.update_document_content(&uri, content.clone()).await;

        // Update workspace symbols
        self.update_workspace_symbols(&uri, &content).await;

        // Load and resolve module
        self.load_and_resolve_module(&uri, &content).await;

        // Compute and publish diagnostics
        if let Some(ast) = ligature_parser::parse_program(&content).ok() {
            if let Some(diagnostics) = self
                .diagnostics
                .write()
                .await
                .compute_enhanced_diagnostics(&uri, &content, Some(&ast))
                .await
            {
                if let Err(_e) = self
                    .client
                    .publish_diagnostics(uri.parse().unwrap(), diagnostics, None)
                    .await
                {
                    warn!("Failed to publish diagnostics");
                }
            }
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.to_string();

        // Update document content
        if let Some(change) = params.content_changes.first() {
            let content = change.text.clone();
            self.update_document_content(&uri, content.clone()).await;

            // Update workspace symbols
            self.update_workspace_symbols(&uri, &content).await;

            // Compute and publish diagnostics
            if let Some(ast) = ligature_parser::parse_program(&content).ok() {
                if let Some(diagnostics) = self
                    .diagnostics
                    .write()
                    .await
                    .compute_enhanced_diagnostics(&uri, &content, Some(&ast))
                    .await
                {
                    if let Err(_e) = self
                        .client
                        .publish_diagnostics(uri.parse().unwrap(), diagnostics, None)
                        .await
                    {
                        warn!("Failed to publish diagnostics");
                    }
                }
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri.to_string();

        info!("Document closed: {}", uri);

        // Remove document content
        self.remove_document_content(&uri).await;

        // Clear diagnostics
        self.diagnostics.write().await.clear_diagnostics(&uri);

        // Clear symbols
        self.symbols.write().await.clear_symbols(&uri);

        // Publish empty diagnostics to clear them
        if let Err(_e) = self
            .client
            .publish_diagnostics(uri.parse().unwrap(), vec![], None)
            .await
        {
            warn!("Failed to clear diagnostics");
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;
        let context = params.context;

        if let Some(content) = self.get_document_content(&uri).await {
            let completion_response = self
                .completion
                .read()
                .await
                .provide_enhanced_completion(&uri, &content, position, context)
                .await;
            Ok(Some(completion_response))
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
            Ok(self.hover.provide_hover(&uri, &content, position).await)
        } else {
            Ok(None)
        }
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;

        // Get the symbol at the position
        if let Some(content) = self.get_document_content(&uri).await {
            let symbol_name = self.get_symbol_at_position(&content, position);
            if !symbol_name.is_empty() {
                let references = self.find_symbol_references(&symbol_name, &uri).await;
                Ok(Some(references))
            } else {
                Ok(None)
            }
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
            if let Ok(program) = ligature_parser::parse_program(&content) {
                let symbols = self
                    .symbols
                    .read()
                    .await
                    .get_document_symbols(&uri, &content)
                    .await;
                Ok(Some(DocumentSymbolResponse::Flat(
                    symbols
                        .into_iter()
                        .map(|s| SymbolInformation {
                            name: s.name,
                            kind: s.kind,
                            tags: s.tags,
                            deprecated: None,
                            location: Location::new(
                                Url::parse(&uri)
                                    .unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                                s.range,
                            ),
                            container_name: None,
                        })
                        .collect(),
                )))
            } else {
                Ok(None)
            }
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

        // Get the symbol at the position
        if let Some(content) = self.get_document_content(&uri).await {
            let symbol_name = self.get_symbol_at_position(&content, position);
            if !symbol_name.is_empty() {
                if let Some(location) = self.find_symbol_definition(&symbol_name, &uri).await {
                    Ok(Some(GotoDefinitionResponse::Scalar(location)))
                } else {
                    Ok(None)
                }
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri.to_string();
        let range = params.range;
        let context = params.context;

        if let Some(content) = self.get_document_content(&uri).await {
            let ast = ligature_parser::parse_program(&content).ok();
            let actions = self
                .code_actions
                .provide_code_actions(&uri, &content, range, &context)
                .await;
            Ok(Some(actions))
        } else {
            Ok(None)
        }
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri.to_string();

        if let Some(content) = self.get_document_content(&uri).await {
            Ok(Some(self.formatting.format_document(&uri, &content).await))
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
            Ok(Some(
                self.formatting.format_range(&uri, &content, range).await,
            ))
        } else {
            Ok(None)
        }
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri.to_string();
        let position = params.text_document_position.position;
        let new_name = params.new_name;

        if let Some(content) = self.get_document_content(&uri).await {
            Ok(self
                .rename
                .rename_symbol(&uri, &content, position, &new_name)
                .await)
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
        info!("Enhanced workspace symbol search: {}", query);

        // Use enhanced symbol search with import resolution
        let symbols = self
            .symbols
            .read()
            .await
            .search_workspace_symbols_enhanced(
                params,
                &self.import_resolution,
                &self.workspace_folders, // Assuming workspace_folders is the correct source for workspace symbols
            )
            .await;

        Ok(Some(symbols))
    }

    async fn did_change_workspace_folders(&self, params: DidChangeWorkspaceFoldersParams) {
        let mut workspace_folders = self.workspace_folders.write().await;

        // Remove removed folders
        for folder in params.event.removed {
            workspace_folders.retain(|f| f.uri != folder.uri);
        }

        // Add added folders
        for folder in params.event.added {
            workspace_folders.push(folder);
        }

        // Reload workspace modules
        self.load_workspace_modules().await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        if let Some(settings) = params.settings {
            if let Ok(config) = serde_json::from_value::<LspConfig>(settings) {
                // Update workspace configuration
                let mut workspace_config = self.workspace_config.write().await;

                // Update diagnostics configuration
                workspace_config.diagnostics_config =
                    crate::enhanced_diagnostics::EnhancedDiagnosticsConfig::default();

                // Update completion configuration
                workspace_config.completion_config =
                    crate::enhanced_completion::EnhancedCompletionConfig::default();

                // Update provider configurations
                self.diagnostics
                    .write()
                    .await
                    .update_config(workspace_config.diagnostics_config.clone());
                self.completion
                    .write()
                    .await
                    .update_config(workspace_config.completion_config.clone());
            }
        }
    }

    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        for change in params.changes {
            let uri = change.uri.to_string();

            match change.typ {
                FileChangeType::CREATED => {
                    info!("File created: {}", uri);
                    // Handle file creation
                }
                FileChangeType::CHANGED => {
                    info!("File changed: {}", uri);
                    // Handle file change
                }
                FileChangeType::DELETED => {
                    info!("File deleted: {}", uri);
                    // Handle file deletion
                    self.remove_document_content(&uri).await;
                    self.diagnostics.write().await.clear_diagnostics(&uri);
                    self.symbols.write().await.clear_symbols(&uri);
                }
                _ => {
                    info!("Unknown file change type: {:?}", change.typ);
                }
            }
        }
    }
}

impl EnhancedLigatureLspServer {
    /// Load workspace modules.
    pub async fn load_workspace_modules(&self) {
        let workspace_folders = self.workspace_folders.read().await;

        for folder in workspace_folders.iter() {
            if let Ok(path) = folder.uri.to_file_path() {
                self.load_modules_from_directory(&path).await;
            }
        }
    }

    /// Load modules from a directory.
    async fn load_modules_from_directory(&self, dir: &Path) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();

                if path.is_file() && path.extension().map_or(false, |ext| ext == "lig") {
                    if let Ok(content) = std::fs::read_to_string(&path) {
                        if let Ok(uri) = self.path_to_uri(&path) {
                            self.update_document_content(&uri, content).await;
                        }
                    }
                } else if path.is_dir() {
                    Box::pin(self.load_modules_from_directory(&path)).await;
                }
            }
        }
    }

    /// Create a temporary module for testing.
    pub async fn create_temp_module(
        &self,
        content: &str,
        name: &str,
    ) -> std::result::Result<String, AstError> {
        let temp_dir = std::env::temp_dir();
        let file_path = temp_dir.join(format!("{}.lig", name));

        std::fs::write(&file_path, content).map_err(|e| AstError::ParseError {
            message: e.to_string(),
            span: ligature_ast::Span {
                line: 0,
                column: 0,
                start: 0,
                end: 0,
            },
        })?;

        let uri = self.path_to_uri(&file_path)?;
        self.update_document_content(&uri, content.to_string())
            .await;

        Ok(uri)
    }

    /// Convert a path to a URI.
    fn path_to_uri(&self, path: &Path) -> std::result::Result<String, AstError> {
        path.to_str()
            .ok_or_else(|| AstError::ParseError {
                message: "Invalid path".to_string(),
                span: Span::default(),
            })
            .map(|s| format!("file://{}", s))
    }

    /// Get symbol at position.
    fn get_symbol_at_position(&self, content: &str, position: Position) -> String {
        let lines: Vec<&str> = content.lines().collect();
        if let Some(line) = lines.get(position.line as usize) {
            let char_pos = position.character as usize;
            if char_pos <= line.len() {
                let before_cursor = &line[..char_pos];
                let after_cursor = &line[char_pos..];

                let word_start = before_cursor
                    .rfind(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(|i| i + 1)
                    .unwrap_or(0);

                let word_end = after_cursor
                    .find(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(|i| char_pos + i)
                    .unwrap_or(line.len());

                return line[word_start..word_end].to_string();
            }
        }
        String::new()
    }
}

/// Run the enhanced LSP server.
pub async fn run_enhanced_server() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| EnhancedLigatureLspServer::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
}
