//! Symbols provider for the Ligature LSP server.

#[allow(deprecated)]
use ligature_ast::{Declaration, DeclarationKind, Program, Span, ValueDeclaration};
use lsp_types::{
    DocumentSymbol, Location, Position, Range, SymbolInformation, SymbolKind, SymbolTag, Url,
    WorkspaceSymbol, WorkspaceSymbolParams,
};
use std::collections::HashMap;

/// Provider for document and workspace symbols.
pub struct SymbolsProvider {
    /// Cache of symbols by document URI.
    symbols_cache: HashMap<String, Vec<DocumentSymbol>>,
    /// Cache of workspace symbols.
    workspace_symbols: HashMap<String, Vec<SymbolInformation>>,
}

impl SymbolsProvider {
    /// Create a new symbols provider.
    pub fn new() -> Self {
        Self {
            symbols_cache: HashMap::new(),
            workspace_symbols: HashMap::new(),
        }
    }

    /// Get document symbols for a program.
    pub async fn get_document_symbols(&self, uri: &str, content: &str) -> Vec<DocumentSymbol> {
        // Try to parse the program for symbols
        let ast = ligature_parser::parse_program(content).ok();

        if let Some(program) = ast {
            let mut symbols = Vec::new();

            for decl in &program.declarations {
                if let Some(symbol) = self.declaration_to_symbol(decl, uri) {
                    symbols.push(symbol);
                }
            }

            // Note: Caching is disabled in async version to avoid mutable reference issues
            // self.symbols_cache.insert(uri.to_string(), symbols.clone());

            symbols
        } else {
            vec![]
        }
    }

    /// Get document symbols for a program (original method).
    pub fn get_document_symbols_sync(
        &mut self,
        uri: &str,
        program: &Program,
    ) -> Vec<DocumentSymbol> {
        let mut symbols = Vec::new();

        for decl in &program.declarations {
            if let Some(symbol) = self.declaration_to_symbol(decl, uri) {
                symbols.push(symbol);
            }
        }

        // Cache the symbols
        self.symbols_cache.insert(uri.to_string(), symbols.clone());

        symbols
    }

    /// Search workspace symbols matching a query.
    pub async fn search_workspace_symbols(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Vec<SymbolInformation> {
        let query = params.query;
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        for symbol_infos in self.workspace_symbols.values() {
            for symbol_info in symbol_infos {
                if symbol_info.name.to_lowercase().contains(&query_lower) {
                    symbols.push(symbol_info.clone());
                }
            }
        }

        symbols
    }

    /// Search workspace symbols matching a query with enhanced cross-file support.
    pub async fn search_workspace_symbols_enhanced(
        &self,
        params: WorkspaceSymbolParams,
        import_resolution: &crate::import_resolution::ImportResolutionService,
        workspace_manager: &crate::workspace::WorkspaceManager,
    ) -> Vec<SymbolInformation> {
        let query = params.query;
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        // Get symbols from current workspace symbols cache
        for symbol_infos in self.workspace_symbols.values() {
            for symbol_info in symbol_infos {
                if symbol_info.name.to_lowercase().contains(&query_lower) {
                    symbols.push(symbol_info.clone());
                }
            }
        }

        // Get symbols from import resolution service
        let loaded_modules = import_resolution.get_loaded_modules().await;
        for module_uri in loaded_modules {
            if let Some(module) = import_resolution.get_cached_module(&module_uri).await {
                let module_symbols =
                    self.extract_symbols_from_module(&module, &module_uri, &query_lower);
                symbols.extend(module_symbols);
            }
        }

        // Get symbols from workspace manager
        let workspace_symbols = workspace_manager.get_workspace_symbols(&query).await;
        for ws in workspace_symbols {
            symbols.push(SymbolInformation {
                name: ws.name,
                kind: ws.kind,
                tags: Some(ws.tags),
                #[allow(deprecated)]
                deprecated: None,
                location: ws.location,
                container_name: ws.container_name,
            });
        }

        // Remove duplicates and sort
        symbols.sort_by(|a, b| a.name.cmp(&b.name));
        symbols.dedup_by(|a, b| a.name == b.name && a.location.uri == b.location.uri);

        symbols
    }

    /// Extract symbols from a module that match a query.
    fn extract_symbols_from_module(
        &self,
        module: &ligature_ast::Module,
        module_uri: &str,
        query: &str,
    ) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();

        for declaration in &module.declarations {
            let symbol_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if symbol_name.to_lowercase().contains(query) {
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

    /// Get workspace symbols matching a query.
    pub fn get_workspace_symbols(&self, query: &str) -> Vec<WorkspaceSymbol> {
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        for symbol_infos in self.workspace_symbols.values() {
            for symbol_info in symbol_infos {
                if symbol_info.name.to_lowercase().contains(&query_lower) {
                    symbols.push(WorkspaceSymbol {
                        name: symbol_info.name.clone(),
                        kind: symbol_info.kind,
                        tags: symbol_info.tags.clone(),
                        location: lsp_types::OneOf::Left(symbol_info.location.clone()),
                        container_name: symbol_info.container_name.clone(),
                        data: None,
                    });
                }
            }
        }

        symbols
    }

    /// Convert a declaration to a document symbol.
    fn declaration_to_symbol(&self, decl: &Declaration, _uri: &str) -> Option<DocumentSymbol> {
        match &decl.kind {
            DeclarationKind::Value(value_decl) => Some(DocumentSymbol {
                name: value_decl.name.clone(),
                detail: self.get_value_detail(value_decl),
                kind: SymbolKind::VARIABLE,
                tags: None,
                #[allow(deprecated)]
                deprecated: None,
                range: self.span_to_range(value_decl.span),
                selection_range: self.span_to_range(value_decl.span),
                children: None,
            }),
            DeclarationKind::TypeAlias(type_alias) => Some(DocumentSymbol {
                name: type_alias.name.clone(),
                detail: Some(format!("type alias = {:?}", type_alias.type_)),
                kind: SymbolKind::TYPE_PARAMETER,
                tags: None,
                #[allow(deprecated)]
                deprecated: None,
                range: self.span_to_range(type_alias.span),
                selection_range: self.span_to_range(type_alias.span),
                children: None,
            }),
            DeclarationKind::TypeConstructor(type_ctor) => Some(DocumentSymbol {
                name: type_ctor.name.clone(),
                detail: Some("data type".to_string()),
                kind: SymbolKind::CLASS,
                tags: None,
                #[allow(deprecated)]
                deprecated: None,
                range: self.span_to_range(type_ctor.span),
                selection_range: self.span_to_range(type_ctor.span),
                children: None,
            }),
            DeclarationKind::TypeClass(type_class) => {
                let mut children = Vec::new();
                for method in &type_class.methods {
                    children.push(DocumentSymbol {
                        name: method.name.clone(),
                        detail: Some(format!(": {:?}", method.type_)),
                        kind: SymbolKind::METHOD,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        range: self.span_to_range(method.span),
                        selection_range: self.span_to_range(method.span),
                        children: None,
                    });
                }

                Some(DocumentSymbol {
                    name: type_class.name.clone(),
                    detail: Some("type class".to_string()),
                    kind: SymbolKind::INTERFACE,
                    tags: None,
                    #[allow(deprecated)]
                    deprecated: None,
                    range: self.span_to_range(type_class.span),
                    selection_range: self.span_to_range(type_class.span),
                    children: Some(children),
                })
            }
            DeclarationKind::Instance(instance) => {
                Some(DocumentSymbol {
                    name: format!(
                        "instance {} for {}",
                        instance.class_name,
                        instance
                            .type_arguments
                            .iter()
                            .map(|t| format!("{t:?}"))
                            .collect::<Vec<_>>()
                            .join(" ")
                    ),
                    detail: Some("type class instance".to_string()),
                    kind: SymbolKind::CLASS,
                    tags: Some(vec![SymbolTag::DEPRECATED]), // Instances are typically not shown in outline
                    #[allow(deprecated)]
                    deprecated: None,
                    range: self.span_to_range(instance.span),
                    selection_range: self.span_to_range(instance.span),
                    children: None,
                })
            }
            DeclarationKind::Import(import) => Some(DocumentSymbol {
                name: format!("import {}", import.path),
                detail: import.alias.as_ref().map(|alias| format!("as {alias}")),
                kind: SymbolKind::NAMESPACE,
                tags: None,
                #[allow(deprecated)]
                deprecated: None,
                range: self.span_to_range(import.span),
                selection_range: self.span_to_range(import.span),
                children: None,
            }),
            DeclarationKind::Export(export) => Some(DocumentSymbol {
                name: "exports".to_string(),
                detail: Some(format!("{} items", export.items.len())),
                kind: SymbolKind::NAMESPACE,
                tags: None,
                #[allow(deprecated)]
                deprecated: None,
                range: self.span_to_range(export.span),
                selection_range: self.span_to_range(export.span),
                children: None,
            }),
        }
    }

    /// Get detail information for a value declaration.
    fn get_value_detail(&self, value_decl: &ValueDeclaration) -> Option<String> {
        if let Some(ref type_ann) = value_decl.type_annotation {
            Some(format!(": {type_ann:?}"))
        } else {
            Some(": <inferred>".to_string())
        }
    }

    /// Update workspace symbols for a document.
    pub fn update_workspace_symbols(&mut self, uri: &str, program: &Program) {
        let mut symbol_infos = Vec::new();

        for decl in &program.declarations {
            if let Some(symbol_info) = self.declaration_to_symbol_info(decl, uri) {
                symbol_infos.push(symbol_info);
            }
        }

        self.workspace_symbols.insert(uri.to_string(), symbol_infos);
    }

    /// Convert a declaration to a symbol information.
    fn declaration_to_symbol_info(
        &self,
        decl: &Declaration,
        uri: &str,
    ) -> Option<SymbolInformation> {
        match &decl.kind {
            DeclarationKind::Value(value_decl) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: value_decl.name.clone(),
                        kind: SymbolKind::VARIABLE,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(value_decl.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::TypeAlias(type_alias) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: type_alias.name.clone(),
                        kind: SymbolKind::TYPE_PARAMETER,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(type_alias.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::TypeConstructor(type_ctor) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: type_ctor.name.clone(),
                        kind: SymbolKind::CLASS,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(type_ctor.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::TypeClass(type_class) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: type_class.name.clone(),
                        kind: SymbolKind::INTERFACE,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(type_class.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::Instance(instance) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: format!(
                            "instance {} for {}",
                            instance.class_name,
                            instance
                                .type_arguments
                                .iter()
                                .map(|t| format!("{t:?}"))
                                .collect::<Vec<_>>()
                                .join(" ")
                        ),
                        kind: SymbolKind::CLASS,
                        tags: Some(vec![SymbolTag::DEPRECATED]),
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(instance.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::Import(import) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: format!("import {}", import.path),
                        kind: SymbolKind::NAMESPACE,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(import.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
            DeclarationKind::Export(export) => {
                if let Ok(url) = Url::parse(uri) {
                    Some(SymbolInformation {
                        name: "exports".to_string(),
                        kind: SymbolKind::NAMESPACE,
                        tags: None,
                        #[allow(deprecated)]
                        deprecated: None,
                        location: Location {
                            uri: url,
                            range: self.span_to_range(export.span),
                        },
                        container_name: None,
                    })
                } else {
                    None
                }
            }
        }
    }

    /// Convert a Ligature span to an LSP range.
    fn span_to_range(&self, span: Span) -> Range {
        Range {
            start: Position {
                line: span.line as u32 - 1,        // Convert to 0-indexed
                character: span.column as u32 - 1, // Convert to 0-indexed
            },
            end: Position {
                line: span.line as u32 - 1, // For now, assume single line
                character: span.column as u32 - 1 + span.len() as u32,
            },
        }
    }

    /// Get cached document symbols for a document.
    pub fn get_cached_document_symbols(&self, uri: &str) -> Option<&Vec<DocumentSymbol>> {
        self.symbols_cache.get(uri)
    }

    /// Clear symbols for a document.
    pub fn clear_symbols(&mut self, uri: &str) {
        self.symbols_cache.remove(uri);
        self.workspace_symbols.remove(uri);
    }

    /// Get all workspace symbols.
    pub fn get_all_workspace_symbols(&self) -> Vec<WorkspaceSymbol> {
        let mut symbols = Vec::new();

        for symbol_infos in self.workspace_symbols.values() {
            for symbol_info in symbol_infos {
                symbols.push(WorkspaceSymbol {
                    name: symbol_info.name.clone(),
                    kind: symbol_info.kind,
                    tags: symbol_info.tags.clone(),
                    location: lsp_types::OneOf::Left(symbol_info.location.clone()),
                    container_name: symbol_info.container_name.clone(),
                    data: None,
                });
            }
        }

        symbols
    }
}

impl Default for SymbolsProvider {
    fn default() -> Self {
        Self::new()
    }
}
