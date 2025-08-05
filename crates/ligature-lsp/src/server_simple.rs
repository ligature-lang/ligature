//! Simplified LSP server implementation for the Ligature language.

use tower_lsp::{LspService, Server};
use lsp_types::{
    InitializeParams, InitializeResult, ServerCapabilities, TextDocumentSyncKind,
    TextDocumentSyncOptions, CompletionOptions, HoverProviderCapability, SignatureHelpOptions,
    InlayHintOptions,
    MessageType, CompletionParams, CompletionResponse, HoverParams, Hover,
    TextDocumentItem, DidOpenTextDocumentParams, DidChangeTextDocumentParams, DidCloseTextDocumentParams, 
    VersionedTextDocumentIdentifier, Url, GotoDefinitionResponse, GotoDefinitionParams,
    CodeActionParams, CodeActionOrCommand, DocumentFormattingParams, DocumentRangeFormattingParams,
    RenameParams, ReferenceParams, Location, WorkspaceFolder, InlayHintParams,
};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use ligature_ast::Program;
use ligature_parser::parse_program;
use tracing::{info, warn, debug, instrument, span, Level};
use crate::{
    diagnostics::DiagnosticsProvider,
    completion::CompletionProvider,
    hover::HoverProvider,
    references::ReferencesProvider,
    symbols::SymbolsProvider,
    definition::DefinitionProvider,
    code_actions::CodeActionsProvider,
    formatting::FormattingProvider,
    rename::RenameProvider,
    inlay_hints::InlayHintsProvider,
};

/// LSP server for the Ligature language.
pub struct LigatureLspServer {
    /// Client for sending notifications back to the client.
    client: tower_lsp::Client,
    /// Document contents indexed by URI.
    documents: Arc<RwLock<HashMap<String, DocumentState>>>,
    /// Workspace folders.
    workspace_folders: Arc<RwLock<HashMap<String, WorkspaceFolder>>>,
    /// Diagnostics provider.
    diagnostics: Arc<RwLock<DiagnosticsProvider>>,
    /// Completion provider.
    completion: Arc<RwLock<CompletionProvider>>,
    /// Hover provider.
    hover: HoverProvider,
    /// References provider.
    references: ReferencesProvider,
    /// Symbols provider.
    symbols: SymbolsProvider,
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
}

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

impl LigatureLspServer {
    /// Create a new LSP server.
    pub fn new(client: tower_lsp::Client) -> Self {
        info!("Creating new Ligature LSP server instance");
        Self {
            client,
            documents: Arc::new(RwLock::new(HashMap::new())),
            workspace_folders: Arc::new(RwLock::new(HashMap::new())),
            diagnostics: Arc::new(RwLock::new(DiagnosticsProvider::new())),
            completion: Arc::new(RwLock::new(CompletionProvider::new())),
            hover: HoverProvider::new(),
            references: ReferencesProvider::new(),
            symbols: SymbolsProvider::new(),
            definition: DefinitionProvider::new(),
            code_actions: CodeActionsProvider::new(),
            formatting: FormattingProvider::new(),
            rename: RenameProvider::new(),
            inlay_hints: Arc::new(RwLock::new(InlayHintsProvider::new())),
        }
    }

    /// Get a document by URI.
    pub async fn get_document(&self, uri: &str) -> Option<DocumentState> {
        self.documents.read().await.get(uri).cloned()
    }

    /// Update a document's content with incremental parsing support.
    pub async fn update_document(&mut self, uri: String, content: String, version: i32) {
        let mut documents = self.documents.write().await;
        
        // Check if we can do incremental parsing
        let should_incremental_parse = if let Some(existing_doc) = documents.get(&uri) {
            !existing_doc.needs_full_parse && 
            existing_doc.version + 1 == version &&
            content.len() > existing_doc.content.len() // Simple heuristic
        } else {
            false
        };

        let ast = if should_incremental_parse {
            // Try incremental parsing
            self.try_incremental_parse(&uri, &content, documents.get(&uri).unwrap())
        } else {
            // Fall back to full parsing
            ligature_parser::parse_program(&content).ok()
        };
        
        documents.insert(uri.clone(), DocumentState {
            content: content.clone(),
            ast: ast.clone(),
            version,
            last_change_range: None,
            needs_full_parse: false,
        });
        
        // Publish diagnostics
        let diagnostics = {
            let mut diagnostics_provider = self.diagnostics.write().await;
            diagnostics_provider.compute_diagnostics(&uri, &content, ast.as_ref()).await
        };
        if let Some(diagnostics) = diagnostics {
            if let Ok(url) = lsp_types::Url::parse(&uri) {
                self.client.publish_diagnostics(url, diagnostics, Some(version)).await;
            }
        }
    }

    /// Try to perform incremental parsing.
    fn try_incremental_parse(
        &self,
        uri: &str,
        new_content: &str,
        _old_doc: &DocumentState,
    ) -> Option<Program> {
        // This is a simplified incremental parsing implementation
        // In a full implementation, you would:
        // 1. Compare the old and new content to find changed ranges
        // 2. Only re-parse the changed sections
        // 3. Merge the new AST with the existing one
        
        // For now, we'll fall back to full parsing but mark it as incremental
        // to avoid unnecessary re-parsing in the future
        ligature_parser::parse_program(new_content).ok()
    }

    /// Mark a document as needing full re-parsing.
    pub async fn mark_for_full_parse(&self, uri: &str) {
        let mut documents = self.documents.write().await;
        if let Some(doc) = documents.get_mut(uri) {
            doc.needs_full_parse = true;
        }
    }

    /// Remove a document from the server.
    pub async fn remove_document(&self, uri: &str) {
        let mut documents = self.documents.write().await;
        documents.remove(uri);
        
        // Clear diagnostics
        if let Ok(url) = lsp_types::Url::parse(uri) {
            self.client.publish_diagnostics(url, vec![], None).await;
        }
    }

    /// Get all documents.
    pub async fn get_all_documents(&self) -> HashMap<String, DocumentState> {
        self.documents.read().await.clone()
    }

    /// Add a workspace folder.
    pub async fn add_workspace_folder(&self, folder: WorkspaceFolder) {
        let mut folders = self.workspace_folders.write().await;
        folders.insert(folder.uri.to_string(), folder);
    }

    /// Remove a workspace folder.
    pub async fn remove_workspace_folder(&self, uri: &str) {
        let mut folders = self.workspace_folders.write().await;
        folders.remove(uri);
    }

    /// Get all workspace folders.
    pub async fn get_workspace_folders(&self) -> Vec<WorkspaceFolder> {
        self.workspace_folders.read().await.values().cloned().collect()
    }

    /// Check if a URI is in the workspace.
    pub async fn is_in_workspace(&self, uri: &str) -> bool {
        let folders = self.workspace_folders.read().await;
        folders.values().any(|folder| {
            uri.starts_with(&folder.uri.to_string())
        })
    }
}

// Simple placeholder implementation for now
#[tower_lsp::async_trait]
impl tower_lsp::LanguageServer for LigatureLspServer {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult, tower_lsp::jsonrpc::Error> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities::default(),
            server_info: Some(lsp_types::ServerInfo {
                name: "ligature-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: lsp_types::InitializedParams) {
        info!("Ligature LSP server initialized successfully");
    }

    async fn shutdown(&self) -> Result<(), tower_lsp::jsonrpc::Error> {
        info!("Shutting down Ligature LSP server");
        Ok(())
    }

    async fn did_open(&self, _params: DidOpenTextDocumentParams) {
        info!("Document opened");
    }

    async fn did_change(&self, _params: DidChangeTextDocumentParams) {
        info!("Document changed");
    }

    async fn did_close(&self, _params: DidCloseTextDocumentParams) {
        info!("Document closed");
    }
}

pub async fn run_server() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| LigatureLspServer::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
} 