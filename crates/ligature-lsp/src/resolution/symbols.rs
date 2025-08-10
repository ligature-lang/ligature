//! Symbol resolution functionality for the LSP server.
//!
//! This module provides functionality for finding symbols, their definitions,
//! references, and extracting symbol information from modules.

use ligature_ast::Program;
use tower_lsp::lsp_types::{Location, Position, Range, SymbolInformation, SymbolKind, Url};

/// Symbol resolver for finding symbols across modules.
pub struct SymbolResolver;

impl SymbolResolver {
    /// Create a new symbol resolver.
    pub fn new() -> Self {
        Self
    }

    /// Find symbol definition within a module.
    pub fn find_symbol_definition_in_module(
        &self,
        module: &Program,
        symbol_name: &str,
        module_uri: &str,
    ) -> Option<Location> {
        for declaration in &module.declarations {
            let decl_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if decl_name == symbol_name {
                if let Ok(url) = Url::parse(module_uri) {
                    return Some(Location::new(
                        url,
                        Range::new(
                            Position::new(
                                declaration.span.line as u32 - 1,
                                declaration.span.column as u32 - 1,
                            ),
                            Position::new(
                                declaration.span.line as u32 - 1,
                                declaration.span.column as u32 - 1 + declaration.span.len() as u32,
                            ),
                        ),
                    ));
                }
            }
        }

        None
    }

    /// Extract symbols from a module that match a query.
    pub fn extract_symbols_from_module(
        &self,
        module: &Program,
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
                    let kind = self.get_symbol_kind(&declaration.kind);

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

    /// Find all references to a symbol within a module.
    pub fn find_symbol_in_module(
        &self,
        module: &Program,
        symbol_name: &str,
        module_uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

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

    /// Get all symbols from a module.
    pub fn get_all_symbols_from_module(
        &self,
        module: &Program,
        module_uri: &str,
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

            if let Ok(url) = Url::parse(module_uri) {
                let kind = self.get_symbol_kind(&declaration.kind);

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
                                declaration.span.column as u32 - 1 + declaration.span.len() as u32,
                            ),
                        ),
                    ),
                    container_name: None,
                });
            }
        }

        symbols
    }

    /// Find symbols by kind in a module.
    pub fn find_symbols_by_kind(
        &self,
        module: &Program,
        module_uri: &str,
        kind: SymbolKind,
    ) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();

        for declaration in &module.declarations {
            let declaration_kind = self.get_symbol_kind(&declaration.kind);
            if declaration_kind == kind {
                let symbol_name = match &declaration.kind {
                    ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                    ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                    ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                    ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                    _ => continue,
                };

                if let Ok(url) = Url::parse(module_uri) {
                    symbols.push(SymbolInformation {
                        name: symbol_name.clone(),
                        kind: declaration_kind,
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

    /// Get the LSP symbol kind for a declaration kind.
    fn get_symbol_kind(&self, declaration_kind: &ligature_ast::DeclarationKind) -> SymbolKind {
        match declaration_kind {
            ligature_ast::DeclarationKind::Value(_) => SymbolKind::VARIABLE,
            ligature_ast::DeclarationKind::TypeAlias(_) => SymbolKind::TYPE_PARAMETER,
            ligature_ast::DeclarationKind::TypeConstructor(_) => SymbolKind::CLASS,
            ligature_ast::DeclarationKind::TypeClass(_) => SymbolKind::INTERFACE,
            ligature_ast::DeclarationKind::Import(_) => SymbolKind::NAMESPACE,
            ligature_ast::DeclarationKind::Export(_) => SymbolKind::NAMESPACE,
            _ => SymbolKind::VARIABLE,
        }
    }

    /// Check if a symbol exists in a module.
    pub fn symbol_exists_in_module(&self, module: &Program, symbol_name: &str) -> bool {
        for declaration in &module.declarations {
            let decl_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if decl_name == symbol_name {
                return true;
            }
        }

        false
    }

    /// Get the number of symbols in a module.
    pub fn get_symbol_count(&self, module: &Program) -> usize {
        module
            .declarations
            .iter()
            .filter(|decl| {
                matches!(
                    decl.kind,
                    ligature_ast::DeclarationKind::Value(_)
                        | ligature_ast::DeclarationKind::TypeAlias(_)
                        | ligature_ast::DeclarationKind::TypeConstructor(_)
                        | ligature_ast::DeclarationKind::TypeClass(_)
                )
            })
            .count()
    }
}

impl Default for SymbolResolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::{
        Declaration, DeclarationKind, Expr, ExprKind, Literal, Program, Span, ValueDeclaration,
    };

    use super::*;

    fn create_test_program() -> Program {
        let value_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::simple(1, 1),
        };

        let value_decl = ValueDeclaration {
            name: "test_value".to_string(),
            value: value_expr,
            is_recursive: false,
            span: Span::simple(1, 1),
            type_annotation: None,
        };

        let declaration = Declaration {
            kind: DeclarationKind::Value(value_decl),
            span: Span::simple(1, 1),
        };

        Program {
            declarations: vec![declaration],
        }
    }

    #[test]
    fn test_symbol_resolver_creation() {
        let _resolver = SymbolResolver::new();
        // Just test that it can be created
    }

    #[test]
    fn test_find_symbol_definition_in_module() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();
        let module_uri = "file:///test/module.lig";

        let result = resolver.find_symbol_definition_in_module(&program, "test_value", module_uri);
        assert!(result.is_some());

        let location = result.unwrap();
        assert_eq!(location.range.start.line, 0); // 1-indexed to 0-indexed
        assert_eq!(location.range.start.character, 0);
    }

    #[test]
    fn test_find_nonexistent_symbol() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();
        let module_uri = "file:///test/module.lig";

        let result = resolver.find_symbol_definition_in_module(&program, "nonexistent", module_uri);
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_symbols_from_module() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();
        let module_uri = "file:///test/module.lig";

        let symbols = resolver.extract_symbols_from_module(&program, module_uri, "test");
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "test_value");
    }

    #[test]
    fn test_extract_symbols_no_match() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();
        let module_uri = "file:///test/module.lig";

        let symbols = resolver.extract_symbols_from_module(&program, module_uri, "nonexistent");
        assert_eq!(symbols.len(), 0);
    }

    #[test]
    fn test_get_all_symbols_from_module() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();
        let module_uri = "file:///test/module.lig";

        let symbols = resolver.get_all_symbols_from_module(&program, module_uri);
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "test_value");
    }

    #[test]
    fn test_symbol_exists_in_module() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();

        assert!(resolver.symbol_exists_in_module(&program, "test_value"));
        assert!(!resolver.symbol_exists_in_module(&program, "nonexistent"));
    }

    #[test]
    fn test_get_symbol_count() {
        let resolver = SymbolResolver::new();
        let program = create_test_program();

        assert_eq!(resolver.get_symbol_count(&program), 1);
    }

    #[test]
    fn test_get_symbol_kind() {
        let resolver = SymbolResolver::new();

        let value_expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::simple(1, 1),
        };

        let value_decl = ValueDeclaration {
            name: "test".to_string(),
            value: value_expr,
            is_recursive: false,
            span: Span::simple(1, 1),
            type_annotation: None,
        };

        let kind = resolver.get_symbol_kind(&DeclarationKind::Value(value_decl));
        assert_eq!(kind, SymbolKind::VARIABLE);
    }
}
