//! Definition provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Program, Span};
use lsp_types::{Location, Position, Range, Url};

/// Type alias for the definitions cache to reduce complexity
type DefinitionsCache = HashMap<String, HashMap<String, Location>>;

/// Provider for finding symbol definitions.
#[derive(Clone)]
pub struct DefinitionProvider {
    /// Cache of symbol definitions by document URI.
    definitions_cache: DefinitionsCache,
}

impl DefinitionProvider {
    /// Create a new definition provider.
    pub fn new() -> Self {
        Self {
            definitions_cache: HashMap::new(),
        }
    }

    /// Find the definition of a symbol at a given position.
    pub async fn find_definition(
        &self,
        uri: &str,
        content: &str,
        position: Position,
    ) -> Option<Location> {
        // Try to parse the program for context-aware definition finding
        let ast = ligature_parser::parse_program(content).ok();

        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() {
            return None;
        }

        // Check cache first
        if let Some(cache) = self.definitions_cache.get(uri) {
            if let Some(location) = cache.get(&symbol_name) {
                return Some(location.clone());
            }
        }

        // Find definition in the current document
        if let Some(program) = ast.as_ref() {
            if let Some(location) = self.find_definition_in_program(program, &symbol_name, uri) {
                // Note: Caching is disabled in async version to avoid mutable reference issues
                // let cache = self.definitions_cache.entry(uri.to_string()).or_insert_with(HashMap::new);
                // cache.insert(symbol_name.clone(), location.clone());
                return Some(location);
            }
        }

        None
    }

    /// Find the definition of a symbol at a given position (original method).
    pub fn find_definition_sync(
        &mut self,
        uri: &str,
        position: Position,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<Location> {
        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() {
            return None;
        }

        // Check cache first
        if let Some(cache) = self.definitions_cache.get(uri) {
            if let Some(location) = cache.get(&symbol_name) {
                return Some(location.clone());
            }
        }

        // Find definition in the current document
        if let Some(program) = ast {
            if let Some(location) = self.find_definition_in_program(program, &symbol_name, uri) {
                // Cache the definition
                let cache = self.definitions_cache.entry(uri.to_string()).or_default();
                cache.insert(symbol_name.clone(), location.clone());
                return Some(location);
            }
        }

        None
    }

    /// Find the definition of a symbol in a program.
    fn find_definition_in_program(
        &self,
        program: &Program,
        symbol_name: &str,
        uri: &str,
    ) -> Option<Location> {
        for decl in &program.declarations {
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(value_decl.span),
                        });
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_alias.span),
                        });
                    }
                }
                DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_constructor.span),
                        });
                    }
                }
                DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_class.span),
                        });
                    }
                }
                DeclarationKind::Instance(instance_decl) => {
                    if instance_decl.class_name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(instance_decl.span),
                        });
                    }
                }
                DeclarationKind::Import(_) => {
                    // Import statements don't define symbols in the current scope
                    continue;
                }
                DeclarationKind::Export(_) => {
                    // Export statements don't define symbols
                    continue;
                }
            }
        }

        None
    }

    /// Get the symbol name at a given position.
    fn get_symbol_at_position(&self, content: &str, position: Position) -> String {
        let lines: Vec<&str> = content.lines().collect();
        if position.line as usize >= lines.len() {
            return String::new();
        }

        let line = lines[position.line as usize];
        if position.character as usize >= line.len() {
            return String::new();
        }

        // Find the word boundaries around the position
        let mut start = position.character as usize;
        let mut end = position.character as usize;

        // Find start of word
        while start > 0 && self.is_identifier_char(line.chars().nth(start - 1)) {
            start -= 1;
        }

        // Find end of word
        while end < line.len() && self.is_identifier_char(line.chars().nth(end)) {
            end += 1;
        }

        if start < end {
            line[start..end].to_string()
        } else {
            String::new()
        }
    }

    /// Check if a character is part of an identifier.
    fn is_identifier_char(&self, c: Option<char>) -> bool {
        if let Some(c) = c {
            c.is_alphanumeric() || c == '_' || c == '\''
        } else {
            false
        }
    }

    /// Convert a span to a range.
    fn span_to_range(&self, span: Span) -> Range {
        Range {
            start: Position {
                line: span.line as u32,
                character: span.column as u32,
            },
            end: Position {
                line: span.line as u32,
                character: span.column as u32,
            },
        }
    }

    /// Clear the cache for a document.
    pub fn clear_cache(&mut self, uri: &str) {
        self.definitions_cache.remove(uri);
    }

    /// Get cached definition for a symbol.
    pub fn get_cached_definition(&self, uri: &str, symbol: &str) -> Option<&Location> {
        self.definitions_cache.get(uri)?.get(symbol)
    }
}

impl Default for DefinitionProvider {
    fn default() -> Self {
        Self::new()
    }
}
