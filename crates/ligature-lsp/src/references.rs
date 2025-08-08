//! References provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{Declaration, DeclarationKind, Expr, ExprKind, Program, Span};
use lsp_types::{Location, Position, Range, ReferenceContext, Url};

/// Provider for finding references to symbols.
#[derive(Clone)]
pub struct ReferencesProvider {
    /// Cache of symbol references by document URI.
    #[allow(clippy::type_complexity)]
    references_cache: HashMap<String, HashMap<String, Vec<Location>>>,
}

impl ReferencesProvider {
    /// Create a new references provider.
    pub fn new() -> Self {
        Self {
            references_cache: HashMap::new(),
        }
    }

    /// Find all references to a symbol at a given position.
    pub async fn find_references(
        &self,
        uri: &str,
        content: &str,
        position: Position,
    ) -> Vec<Location> {
        // Try to parse the program for context-aware references
        let ast = ligature_parser::parse_program(content).ok();
        let context = ReferenceContext {
            include_declaration: true,
        };

        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() {
            return vec![];
        }

        let mut references = Vec::new();

        // Find references in the current document
        if let Some(program) = ast.as_ref() {
            references.extend(self.find_references_in_program(program, &symbol_name, uri));
        }

        // If include_declaration is true, add the declaration location
        if context.include_declaration {
            if let Some(program) = ast.as_ref() {
                if let Some(declaration_location) =
                    self.find_declaration_location(program, &symbol_name, uri)
                {
                    references.push(declaration_location);
                }
            }
        }

        references
    }

    /// Find all references to a symbol at a given position (original method).
    pub fn find_references_sync(
        &mut self,
        uri: &str,
        position: Position,
        content: &str,
        ast: Option<&Program>,
        context: ReferenceContext,
    ) -> Vec<Location> {
        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() {
            return vec![];
        }

        let mut references = Vec::new();

        // Find references in the current document
        if let Some(program) = ast {
            references.extend(self.find_references_in_program(program, &symbol_name, uri));
        }

        // If include_declaration is true, add the declaration location
        if context.include_declaration {
            if let Some(program) = ast {
                if let Some(declaration_location) =
                    self.find_declaration_location(program, &symbol_name, uri)
                {
                    references.push(declaration_location);
                }
            }
        }

        // Cache the references
        let cache = self.references_cache.entry(uri.to_string()).or_default();
        cache.insert(symbol_name.clone(), references.clone());

        references
    }

    /// Find all references to a symbol across multiple documents.
    pub fn find_workspace_references(
        &mut self,
        symbol_name: &str,
        documents: &[(String, &Program)],
        context: ReferenceContext,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        for (uri, program) in documents {
            // Find references in this document
            references.extend(self.find_references_in_program(program, symbol_name, uri));

            // If include_declaration is true, add the declaration location
            if context.include_declaration {
                if let Some(declaration_location) =
                    self.find_declaration_location(program, symbol_name, uri)
                {
                    references.push(declaration_location);
                }
            }
        }

        references
    }

    /// Find all references to a symbol in a program.
    pub fn find_references_in_program(
        &self,
        program: &Program,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        // Find references in declarations
        for decl in &program.declarations {
            references.extend(self.find_references_in_declaration(decl, symbol_name, uri));
        }

        references
    }

    /// Find references to a symbol in a declaration.
    fn find_references_in_declaration(
        &self,
        decl: &Declaration,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        match &decl.kind {
            DeclarationKind::Value(value_decl) => {
                // Check if this is the declaration itself
                if value_decl.name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(value_decl.span),
                        });
                    }
                }

                // Find references in the value expression
                references.extend(self.find_references_in_expression(
                    &value_decl.value,
                    symbol_name,
                    uri,
                ));
            }
            DeclarationKind::TypeAlias(type_alias) => {
                // Check if this is the declaration itself
                if type_alias.name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(type_alias.span),
                        });
                    }
                }

                // Find references in the target type
                references.extend(self.find_references_in_type(
                    &type_alias.type_,
                    symbol_name,
                    uri,
                ));
            }
            DeclarationKind::TypeConstructor(type_ctor) => {
                // Check if this is the declaration itself
                if type_ctor.name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(type_ctor.span),
                        });
                    }
                }

                // Find references in the body type
                references.extend(self.find_references_in_type(&type_ctor.body, symbol_name, uri));
            }
            DeclarationKind::TypeClass(type_class) => {
                // Check if this is the declaration itself
                if type_class.name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(type_class.span),
                        });
                    }
                }

                // Find references in superclasses
                for constraint in &type_class.superclasses {
                    references.extend(self.find_references_in_type_class_constraint(
                        constraint,
                        symbol_name,
                        uri,
                    ));
                }

                // Find references in method signatures
                for method in &type_class.methods {
                    references.extend(self.find_references_in_type(
                        &method.type_,
                        symbol_name,
                        uri,
                    ));
                }
            }
            DeclarationKind::Instance(instance) => {
                // Find references in type arguments
                for type_arg in &instance.type_arguments {
                    references.extend(self.find_references_in_type(type_arg, symbol_name, uri));
                }

                // Find references in method implementations
                for method in &instance.methods {
                    references.extend(self.find_references_in_expression(
                        &method.implementation,
                        symbol_name,
                        uri,
                    ));
                }
            }
            _ => {}
        }

        references
    }

    /// Find references to a symbol in an expression.
    fn find_references_in_expression(
        &self,
        expr: &Expr,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        match &expr.kind {
            ExprKind::Variable(name) => {
                if name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(expr.span),
                        });
                    }
                }
            }
            ExprKind::Application { function, argument } => {
                references.extend(self.find_references_in_expression(function, symbol_name, uri));
                references.extend(self.find_references_in_expression(argument, symbol_name, uri));
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                // Don't include the parameter itself as a reference
                if parameter != symbol_name {
                    references.extend(self.find_references_in_expression(body, symbol_name, uri));
                }
                if let Some(ty) = parameter_type {
                    references.extend(self.find_references_in_type(ty, symbol_name, uri));
                }
            }
            ExprKind::Let { name, value, body } => {
                // Don't include the binding name itself as a reference
                if name != symbol_name {
                    references.extend(self.find_references_in_expression(value, symbol_name, uri));
                    references.extend(self.find_references_in_expression(body, symbol_name, uri));
                }
            }
            ExprKind::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_expression(
                        &field.value,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ExprKind::FieldAccess { record, field: _ } => {
                references.extend(self.find_references_in_expression(record, symbol_name, uri));
            }
            ExprKind::Union {
                variant: _,
                value: Some(val),
            } => {
                references.extend(self.find_references_in_expression(val, symbol_name, uri));
            }
            ExprKind::Union {
                variant: _,
                value: None,
            } => {}
            ExprKind::Match { scrutinee, cases } => {
                references.extend(self.find_references_in_expression(scrutinee, symbol_name, uri));
                for case in cases {
                    references.extend(self.find_references_in_pattern(
                        &case.pattern,
                        symbol_name,
                        uri,
                    ));
                    references.extend(self.find_references_in_expression(
                        &case.expression,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                references.extend(self.find_references_in_expression(condition, symbol_name, uri));
                references.extend(self.find_references_in_expression(
                    then_branch,
                    symbol_name,
                    uri,
                ));
                references.extend(self.find_references_in_expression(
                    else_branch,
                    symbol_name,
                    uri,
                ));
            }
            ExprKind::BinaryOp {
                operator: _,
                left,
                right,
            } => {
                references.extend(self.find_references_in_expression(left, symbol_name, uri));
                references.extend(self.find_references_in_expression(right, symbol_name, uri));
            }
            ExprKind::UnaryOp {
                operator: _,
                operand,
            } => {
                references.extend(self.find_references_in_expression(operand, symbol_name, uri));
            }
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => {
                references.extend(self.find_references_in_expression(expression, symbol_name, uri));
                references.extend(self.find_references_in_type(type_annotation, symbol_name, uri));
            }
            _ => {}
        }

        references
    }

    /// Find references to a symbol in a pattern.
    #[allow(clippy::only_used_in_recursion)]
    fn find_references_in_pattern(
        &self,
        pattern: &ligature_ast::Pattern,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        match pattern {
            ligature_ast::Pattern::Variable(name) => {
                if name == symbol_name {
                    // This is a pattern variable binding, not a reference
                    // We don't include it in references
                }
            }
            ligature_ast::Pattern::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_pattern(
                        &field.pattern,
                        symbol_name,
                        uri,
                    ));
                }
            }
            ligature_ast::Pattern::Union {
                variant: _,
                value: Some(val),
            } => {
                references.extend(self.find_references_in_pattern(val, symbol_name, uri));
            }
            ligature_ast::Pattern::Union {
                variant: _,
                value: None,
            } => {}
            ligature_ast::Pattern::List { elements } => {
                for element in elements {
                    references.extend(self.find_references_in_pattern(element, symbol_name, uri));
                }
            }
            _ => {}
        }

        references
    }

    /// Find references to a symbol in a type.
    fn find_references_in_type(
        &self,
        ty: &ligature_ast::Type,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        match &ty.kind {
            ligature_ast::TypeKind::Variable(name) => {
                if name == symbol_name {
                    if let Ok(url) = Url::parse(uri) {
                        references.push(Location {
                            uri: url,
                            range: self.span_to_range(ty.span),
                        });
                    }
                }
            }
            ligature_ast::TypeKind::Function {
                parameter,
                return_type,
            } => {
                references.extend(self.find_references_in_type(parameter, symbol_name, uri));
                references.extend(self.find_references_in_type(return_type, symbol_name, uri));
            }
            ligature_ast::TypeKind::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_type(&field.type_, symbol_name, uri));
                }
            }
            ligature_ast::TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(ref value_type) = variant.type_ {
                        references.extend(self.find_references_in_type(
                            value_type,
                            symbol_name,
                            uri,
                        ));
                    }
                }
            }
            ligature_ast::TypeKind::List(element_type) => {
                references.extend(self.find_references_in_type(element_type, symbol_name, uri));
            }
            ligature_ast::TypeKind::Application { function, argument } => {
                references.extend(self.find_references_in_type(function, symbol_name, uri));
                references.extend(self.find_references_in_type(argument, symbol_name, uri));
            }
            ligature_ast::TypeKind::ForAll { body, .. } => {
                references.extend(self.find_references_in_type(body, symbol_name, uri));
            }
            ligature_ast::TypeKind::Exists { body, .. } => {
                references.extend(self.find_references_in_type(body, symbol_name, uri));
            }
            ligature_ast::TypeKind::Pi {
                parameter_type,
                return_type,
                ..
            } => {
                references.extend(self.find_references_in_type(parameter_type, symbol_name, uri));
                references.extend(self.find_references_in_type(return_type, symbol_name, uri));
            }
            ligature_ast::TypeKind::Sigma {
                parameter_type,
                return_type,
                ..
            } => {
                references.extend(self.find_references_in_type(parameter_type, symbol_name, uri));
                references.extend(self.find_references_in_type(return_type, symbol_name, uri));
            }
            _ => {}
        }

        references
    }

    /// Find references to a symbol in a type class constraint.
    fn find_references_in_type_class_constraint(
        &self,
        constraint: &ligature_ast::TypeClassConstraint,
        symbol_name: &str,
        uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        if constraint.class_name == symbol_name {
            if let Ok(url) = Url::parse(uri) {
                references.push(Location {
                    uri: url,
                    range: self.span_to_range(constraint.span),
                });
            }
        }

        for type_arg in &constraint.type_arguments {
            references.extend(self.find_references_in_type(type_arg, symbol_name, uri));
        }

        references
    }

    /// Find the declaration location of a symbol.
    fn find_declaration_location(
        &self,
        program: &Program,
        symbol_name: &str,
        uri: &str,
    ) -> Option<Location> {
        for decl in &program.declarations {
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        if let Ok(url) = Url::parse(uri) {
                            return Some(Location {
                                uri: url,
                                range: self.span_to_range(value_decl.span),
                            });
                        }
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        if let Ok(url) = Url::parse(uri) {
                            return Some(Location {
                                uri: url,
                                range: self.span_to_range(type_alias.span),
                            });
                        }
                    }
                }
                DeclarationKind::TypeConstructor(type_ctor) => {
                    if type_ctor.name == symbol_name {
                        if let Ok(url) = Url::parse(uri) {
                            return Some(Location {
                                uri: url,
                                range: self.span_to_range(type_ctor.span),
                            });
                        }
                    }
                }
                DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        if let Ok(url) = Url::parse(uri) {
                            return Some(Location {
                                uri: url,
                                range: self.span_to_range(type_class.span),
                            });
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Get the symbol name at a specific position.
    pub fn get_symbol_at_position(&self, content: &str, position: Position) -> String {
        let lines: Vec<&str> = content.lines().collect();
        if position.line as usize >= lines.len() {
            return String::new();
        }

        let line = lines[position.line as usize];
        let char_pos = position.character as usize;

        if char_pos >= line.len() {
            return String::new();
        }

        // Find the start of the word
        let mut start = char_pos;
        while start > 0
            && line
                .chars()
                .nth(start - 1)
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            start -= 1;
        }

        // Find the end of the word
        let mut end = char_pos;
        while end < line.len()
            && line
                .chars()
                .nth(end)
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            end += 1;
        }

        line[start..end].to_string()
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

    /// Get cached references for a document.
    pub fn get_cached_references(&self, uri: &str, symbol_name: &str) -> Option<&Vec<Location>> {
        self.references_cache.get(uri)?.get(symbol_name)
    }

    /// Clear references for a document.
    pub fn clear_references(&mut self, uri: &str) {
        self.references_cache.remove(uri);
    }
}

impl Default for ReferencesProvider {
    fn default() -> Self {
        Self::new()
    }
}
