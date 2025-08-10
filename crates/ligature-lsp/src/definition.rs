//! Definition provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Program, Span};
use lsp_types::{Location, Position, Range, Url};

use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};

/// Type alias for the definitions cache to reduce complexity
type DefinitionsCache = HashMap<String, HashMap<String, Location>>;

/// Provider for finding symbol definitions.
#[derive(Clone)]
pub struct DefinitionProvider {
    /// Cache of symbol definitions by document URI.
    definitions_cache: DefinitionsCache,
    /// Async evaluation service for evaluation-based definition finding.
    async_evaluation: Option<AsyncEvaluationService>,
}

impl DefinitionProvider {
    /// Create a new definition provider.
    pub fn new() -> Self {
        Self {
            definitions_cache: HashMap::new(),
            async_evaluation: None,
        }
    }

    /// Create a new definition provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let async_evaluation = AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        Self {
            definitions_cache: HashMap::new(),
            async_evaluation,
        }
    }

    /// Find the definition of a symbol at a given position with enhanced evaluation-based information.
    pub async fn find_definition_enhanced(
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
                // Enhance location with evaluation-based information
                let enhanced_location = self
                    .enhance_location_with_evaluation(location, program, &symbol_name)
                    .await;
                return Some(enhanced_location);
            }
        }

        None
    }

    /// Enhance location with evaluation-based information.
    async fn enhance_location_with_evaluation(
        &self,
        location: Location,
        _program: &Program,
        _symbol_name: &str,
    ) -> Location {
        // For now, return the original location
        // In the future, this could be enhanced to include evaluation-based metadata
        // such as runtime type information, value ranges, etc.
        location
    }

    /// Find evaluation-based definitions that might not be statically visible.
    pub async fn find_evaluation_based_definitions(
        &self,
        uri: &str,
        content: &str,
        position: Position,
    ) -> Vec<Location> {
        let mut definitions = Vec::new();

        if let Some(eval_service) = &self.async_evaluation {
            if let Ok(program) = ligature_parser::parse_program(content) {
                let symbol_name = self.get_symbol_at_position(content, position);

                if !symbol_name.is_empty() {
                    // Look for definitions that might be created through evaluation
                    for decl in &program.declarations {
                        if let DeclarationKind::Value(value_decl) = &decl.kind {
                            // Check if this value declaration might define the symbol through evaluation
                            if let Ok(eval_result) = eval_service
                                .evaluate_expression(
                                    &value_decl.value,
                                    Some(&format!("def_{symbol_name}")),
                                )
                                .await
                            {
                                if eval_result.success {
                                    // Check if the evaluation result contains the symbol
                                    for value in &eval_result.values {
                                        if self.value_contains_symbol(value, &symbol_name) {
                                            definitions.push(Location {
                                                uri: Url::parse(uri).unwrap(),
                                                range: self.span_to_range(decl.span.clone()),
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        definitions
    }

    /// Check if a value contains a specific symbol.
    #[allow(clippy::only_used_in_recursion)]
    fn value_contains_symbol(
        &self,
        value: &ligature_eval::value::Value,
        symbol_name: &str,
    ) -> bool {
        match &value.kind {
            ligature_eval::value::ValueKind::Record(fields) => {
                fields.iter().any(|(key, _)| key == symbol_name)
            }
            ligature_eval::value::ValueKind::List(elements) => elements
                .iter()
                .any(|element| self.value_contains_symbol(element, symbol_name)),
            ligature_eval::value::ValueKind::String(s) => s.contains(symbol_name),
            _ => false,
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
                            range: self.span_to_range(value_decl.span.clone()),
                        });
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_alias.span.clone()),
                        });
                    }
                }
                DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_constructor.span.clone()),
                        });
                    }
                }
                DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(type_class.span.clone()),
                        });
                    }
                }
                DeclarationKind::Instance(instance_decl) => {
                    if instance_decl.class_name == symbol_name {
                        return Some(Location {
                            uri: Url::parse(uri).ok()?,
                            range: self.span_to_range(instance_decl.span.clone()),
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
