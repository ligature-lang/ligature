//! Rename provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Expr, ExprKind, Program, Span};
use lsp_types::{Position, Range, TextEdit, Url, WorkspaceEdit};

/// Provider for symbol renaming.
#[derive(Clone)]
pub struct RenameProvider {
    /// Cache of symbol locations by document URI.
    #[allow(clippy::type_complexity)]
    symbol_cache: HashMap<String, HashMap<String, Vec<Range>>>,
}

impl RenameProvider {
    /// Create a new rename provider.
    pub fn new() -> Self {
        Self {
            symbol_cache: HashMap::new(),
        }
    }

    /// Prepare rename by checking if the symbol at the given position can be renamed.
    pub fn prepare_rename(
        &self,
        _uri: &str,
        position: Position,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<lsp_types::PrepareRenameResponse> {
        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() {
            return None;
        }

        // Check if this is a valid symbol that can be renamed
        if let Some(program) = ast {
            if self.is_renameable_symbol(program, &symbol_name) {
                let range = self.get_symbol_range_at_position(content, position);
                return Some(lsp_types::PrepareRenameResponse::Range(range));
            }
        }

        None
    }

    /// Rename a symbol and return all the changes needed.
    pub async fn rename_symbol(
        &self,
        uri: &str,
        content: &str,
        position: Position,
        new_name: &str,
    ) -> Option<WorkspaceEdit> {
        // Try to parse the program for context-aware renaming
        let ast = ligature_parser::parse_program(content).ok();

        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() || new_name.is_empty() {
            return None;
        }

        // Validate the new name
        if !self.is_valid_identifier(new_name) {
            return None;
        }

        if let Some(program) = ast.as_ref() {
            let changes = self.find_all_references(program, &symbol_name, new_name, uri, content);
            if !changes.is_empty() {
                return Some(WorkspaceEdit {
                    changes: Some(changes),
                    document_changes: None,
                    change_annotations: None,
                });
            }
        }

        None
    }

    /// Rename a symbol and return all the changes needed (original method).
    pub fn rename_symbol_sync(
        &mut self,
        uri: &str,
        position: Position,
        new_name: &str,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<WorkspaceEdit> {
        let symbol_name = self.get_symbol_at_position(content, position);
        if symbol_name.is_empty() || new_name.is_empty() {
            return None;
        }

        // Validate the new name
        if !self.is_valid_identifier(new_name) {
            return None;
        }

        if let Some(program) = ast {
            let changes = self.find_all_references(program, &symbol_name, new_name, uri, content);
            if !changes.is_empty() {
                return Some(WorkspaceEdit {
                    changes: Some(changes),
                    document_changes: None,
                    change_annotations: None,
                });
            }
        }

        None
    }

    /// Check if a symbol can be renamed.
    fn is_renameable_symbol(&self, program: &Program, symbol_name: &str) -> bool {
        // Check if it's a declared symbol (not a builtin)
        for decl in &program.declarations {
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        return true;
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        return true;
                    }
                }
                DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        return true;
                    }
                }
                DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        return true;
                    }
                }
                DeclarationKind::Instance(instance_decl) => {
                    if instance_decl.class_name == symbol_name {
                        return true;
                    }
                }
                DeclarationKind::Import(_) => {
                    // Import statements can be renamed
                    continue;
                }
                DeclarationKind::Export(_) => {
                    // Export statements can be renamed
                    continue;
                }
            }
        }

        false
    }

    /// Find all references to a symbol and create text edits.
    fn find_all_references(
        &self,
        _program: &Program,
        symbol_name: &str,
        new_name: &str,
        uri: &str,
        content: &str,
    ) -> HashMap<Url, Vec<TextEdit>> {
        let mut changes = HashMap::new();
        let mut edits = Vec::new();

        // Find all occurrences in the current document
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            let mut start = 0;
            while let Some(pos) = line[start..].find(symbol_name) {
                let actual_pos = start + pos;

                // Check if this is a complete word match
                if self.is_complete_word_match(line, actual_pos, symbol_name) {
                    let range = Range {
                        start: Position {
                            line: line_num as u32,
                            character: actual_pos as u32,
                        },
                        end: Position {
                            line: line_num as u32,
                            character: (actual_pos + symbol_name.len()) as u32,
                        },
                    };

                    edits.push(TextEdit {
                        range,
                        new_text: new_name.to_string(),
                    });
                }

                start = actual_pos + 1;
            }
        }

        if !edits.is_empty() {
            if let Ok(url) = Url::parse(uri) {
                changes.insert(url, edits);
            }
        }

        changes
    }

    /// Check if a match is a complete word.
    fn is_complete_word_match(&self, line: &str, pos: usize, symbol_name: &str) -> bool {
        let before_char = if pos > 0 {
            line.chars().nth(pos - 1)
        } else {
            None
        };

        let after_char = line.chars().nth(pos + symbol_name.len());

        // Check that the character before is not part of an identifier
        let before_ok = before_char.map_or(true, |c| !self.is_identifier_char(c));

        // Check that the character after is not part of an identifier
        let after_ok = after_char.map_or(true, |c| !self.is_identifier_char(c));

        before_ok && after_ok
    }

    /// Check if a character is part of an identifier.
    fn is_identifier_char(&self, c: char) -> bool {
        c.is_alphanumeric() || c == '_' || c == '\''
    }

    /// Check if a string is a valid identifier.
    fn is_valid_identifier(&self, name: &str) -> bool {
        if name.is_empty() {
            return false;
        }

        let mut chars = name.chars();
        let first_char = chars.next().unwrap();

        // First character must be a letter or underscore
        if !first_char.is_alphabetic() && first_char != '_' {
            return false;
        }

        // All other characters must be alphanumeric, underscore, or prime
        chars.all(|c| self.is_identifier_char(c))
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
        while start > 0 && self.is_identifier_char(line.chars().nth(start - 1).unwrap_or(' ')) {
            start -= 1;
        }

        // Find end of word
        while end < line.len() && self.is_identifier_char(line.chars().nth(end).unwrap_or(' ')) {
            end += 1;
        }

        if start < end {
            line[start..end].to_string()
        } else {
            String::new()
        }
    }

    /// Get the range of a symbol at a given position.
    fn get_symbol_range_at_position(&self, content: &str, position: Position) -> Range {
        let lines: Vec<&str> = content.lines().collect();
        if position.line as usize >= lines.len() {
            return Range {
                start: position,
                end: position,
            };
        }

        let line = lines[position.line as usize];
        if position.character as usize >= line.len() {
            return Range {
                start: position,
                end: position,
            };
        }

        // Find the word boundaries around the position
        let mut start = position.character as usize;
        let mut end = position.character as usize;

        // Find start of word
        while start > 0 && self.is_identifier_char(line.chars().nth(start - 1).unwrap_or(' ')) {
            start -= 1;
        }

        // Find end of word
        while end < line.len() && self.is_identifier_char(line.chars().nth(end).unwrap_or(' ')) {
            end += 1;
        }

        Range {
            start: Position {
                line: position.line,
                character: start as u32,
            },
            end: Position {
                line: position.line,
                character: end as u32,
            },
        }
    }

    /// Find all references to a symbol in the AST.
    #[allow(dead_code)]
    fn find_references_in_ast(&self, program: &Program, symbol_name: &str) -> Vec<Range> {
        let mut references = Vec::new();

        for decl in &program.declarations {
            // Check declaration names
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        references.push(self.span_to_range(value_decl.span.clone()));
                    }
                    // Check for references in the value expression
                    references.extend(self.find_references_in_expr(&value_decl.value, symbol_name));
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        references.push(self.span_to_range(type_alias.span.clone()));
                    }
                    // Check for references in the type
                    references.extend(self.find_references_in_type(&type_alias.type_, symbol_name));
                }
                DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        references.push(self.span_to_range(type_constructor.span.clone()));
                    }
                    // Check for references in the body type
                    references
                        .extend(self.find_references_in_type(&type_constructor.body, symbol_name));
                }
                DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == symbol_name {
                        references.push(self.span_to_range(type_class.span.clone()));
                    }
                    // Check for references in methods
                    for method in &type_class.methods {
                        references.extend(self.find_references_in_type(&method.type_, symbol_name));
                    }
                }
                DeclarationKind::Instance(instance_decl) => {
                    if instance_decl.class_name == symbol_name {
                        references.push(self.span_to_range(instance_decl.span.clone()));
                    }
                    // Check for references in method implementations
                    for method in &instance_decl.methods {
                        references.extend(
                            self.find_references_in_expr(&method.implementation, symbol_name),
                        );
                    }
                }
                DeclarationKind::Import(import) => {
                    // Check for references in import path or items
                    if import.path == symbol_name {
                        references.push(self.span_to_range(import.span.clone()));
                    }
                    if let Some(items) = &import.items {
                        for item in items {
                            if item.name == symbol_name {
                                references.push(self.span_to_range(item.span.clone()));
                            }
                        }
                    }
                }
                DeclarationKind::Export(export) => {
                    // Check for references in export items
                    for item in &export.items {
                        if item.name == symbol_name {
                            references.push(self.span_to_range(item.span.clone()));
                        }
                    }
                }
            }
        }

        references
    }

    /// Find references to a symbol in an expression.
    #[allow(dead_code)]
    fn find_references_in_expr(&self, expr: &Expr, symbol_name: &str) -> Vec<Range> {
        let mut references = Vec::new();

        match &expr.kind {
            ExprKind::Variable(name) => {
                if name == symbol_name {
                    references.push(self.span_to_range(expr.span.clone()));
                }
            }
            ExprKind::Application { function, argument } => {
                references.extend(self.find_references_in_expr(function, symbol_name));
                references.extend(self.find_references_in_expr(argument, symbol_name));
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                if parameter == symbol_name {
                    references.push(self.span_to_range(expr.span.clone()));
                }
                if let Some(param_type) = parameter_type {
                    references.extend(self.find_references_in_type(param_type, symbol_name));
                }
                references.extend(self.find_references_in_expr(body, symbol_name));
            }
            ExprKind::Let { name, value, body } => {
                if name == symbol_name {
                    references.push(self.span_to_range(expr.span.clone()));
                }
                references.extend(self.find_references_in_expr(value, symbol_name));
                references.extend(self.find_references_in_expr(body, symbol_name));
            }
            ExprKind::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_expr(&field.value, symbol_name));
                }
            }
            ExprKind::FieldAccess { record, field: _ } => {
                references.extend(self.find_references_in_expr(record, symbol_name));
            }
            ExprKind::Union { variant: _, value } => {
                if let Some(val) = value {
                    references.extend(self.find_references_in_expr(val, symbol_name));
                }
            }
            ExprKind::Match { scrutinee, cases } => {
                references.extend(self.find_references_in_expr(scrutinee, symbol_name));
                for case in cases {
                    references.extend(self.find_references_in_pattern(&case.pattern, symbol_name));
                    if let Some(guard) = &case.guard {
                        references.extend(self.find_references_in_expr(guard, symbol_name));
                    }
                    references.extend(self.find_references_in_expr(&case.expression, symbol_name));
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                references.extend(self.find_references_in_expr(condition, symbol_name));
                references.extend(self.find_references_in_expr(then_branch, symbol_name));
                references.extend(self.find_references_in_expr(else_branch, symbol_name));
            }
            ExprKind::BinaryOp {
                operator: _,
                left,
                right,
            } => {
                references.extend(self.find_references_in_expr(left, symbol_name));
                references.extend(self.find_references_in_expr(right, symbol_name));
            }
            ExprKind::UnaryOp {
                operator: _,
                operand,
            } => {
                references.extend(self.find_references_in_expr(operand, symbol_name));
            }
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => {
                references.extend(self.find_references_in_expr(expression, symbol_name));
                references.extend(self.find_references_in_type(type_annotation, symbol_name));
            }
            ExprKind::Literal(_) => {
                // Literals don't contain variable references
            }
        }

        references
    }

    /// Find references to a symbol in a type.
    #[allow(dead_code)]
    fn find_references_in_type(&self, type_: &ligature_ast::Type, symbol_name: &str) -> Vec<Range> {
        let mut references = Vec::new();

        match &type_.kind {
            ligature_ast::TypeKind::Variable(name) => {
                if name == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
            }
            ligature_ast::TypeKind::Function {
                parameter,
                return_type,
            } => {
                references.extend(self.find_references_in_type(parameter, symbol_name));
                references.extend(self.find_references_in_type(return_type, symbol_name));
            }
            ligature_ast::TypeKind::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_type(&field.type_, symbol_name));
                }
            }
            ligature_ast::TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(type_) = &variant.type_ {
                        references.extend(self.find_references_in_type(type_, symbol_name));
                    }
                }
            }
            ligature_ast::TypeKind::List(element_type) => {
                references.extend(self.find_references_in_type(element_type, symbol_name));
            }
            ligature_ast::TypeKind::ForAll { parameter, body } => {
                if parameter == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
                references.extend(self.find_references_in_type(body, symbol_name));
            }
            ligature_ast::TypeKind::Exists { parameter, body } => {
                if parameter == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
                references.extend(self.find_references_in_type(body, symbol_name));
            }
            ligature_ast::TypeKind::Pi {
                parameter,
                parameter_type,
                return_type,
            } => {
                if parameter == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
                references.extend(self.find_references_in_type(parameter_type, symbol_name));
                references.extend(self.find_references_in_type(return_type, symbol_name));
            }
            ligature_ast::TypeKind::Sigma {
                parameter,
                parameter_type,
                return_type,
            } => {
                if parameter == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
                references.extend(self.find_references_in_type(parameter_type, symbol_name));
                references.extend(self.find_references_in_type(return_type, symbol_name));
            }
            ligature_ast::TypeKind::Application { function, argument } => {
                references.extend(self.find_references_in_type(function, symbol_name));
                references.extend(self.find_references_in_type(argument, symbol_name));
            }
            ligature_ast::TypeKind::Module { name } => {
                if name == symbol_name {
                    references.push(self.span_to_range(type_.span.clone()));
                }
            }
            ligature_ast::TypeKind::Constrained { constraint, type_ } => {
                references
                    .extend(self.find_references_in_type_class_constraint(constraint, symbol_name));
                references.extend(self.find_references_in_type(type_, symbol_name));
            }
            _ => {
                // Other type kinds don't contain variable references
            }
        }

        references
    }

    /// Find references to a symbol in a type class constraint.
    #[allow(dead_code)]
    fn find_references_in_type_class_constraint(
        &self,
        constraint: &ligature_ast::TypeClassConstraint,
        symbol_name: &str,
    ) -> Vec<Range> {
        let mut references = Vec::new();

        if constraint.class_name == symbol_name {
            references.push(self.span_to_range(constraint.span.clone()));
        }

        for type_arg in &constraint.type_arguments {
            references.extend(self.find_references_in_type(type_arg, symbol_name));
        }

        references
    }

    /// Find references to a symbol in a pattern.
    #[allow(clippy::only_used_in_recursion)]
    fn find_references_in_pattern(
        &self,
        pattern: &ligature_ast::Pattern,
        symbol_name: &str,
    ) -> Vec<Range> {
        let mut references = Vec::new();

        match pattern {
            ligature_ast::Pattern::Variable(name) => {
                if name == symbol_name {
                    // Note: Pattern doesn't have a span method, so we'll skip this for now
                    // references.push(self.span_to_range(pattern.span()));
                }
            }
            ligature_ast::Pattern::Union { variant: _, value } => {
                if let Some(val) = value {
                    references.extend(self.find_references_in_pattern(val, symbol_name));
                }
            }
            ligature_ast::Pattern::Record { fields } => {
                for field in fields {
                    references.extend(self.find_references_in_pattern(&field.pattern, symbol_name));
                }
            }
            ligature_ast::Pattern::List { .. } => {
                // List patterns don't contain variable references in this implementation
            }
            ligature_ast::Pattern::Literal(_) => {
                // Literals don't contain variable references
            }
            ligature_ast::Pattern::Wildcard => {
                // Wildcards don't contain variable references
            }
        }

        references
    }

    /// Convert a span to a range.
    #[allow(dead_code)]
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
        self.symbol_cache.remove(uri);
    }

    /// Get cached symbol locations for a document.
    #[allow(clippy::type_complexity)]
    pub fn get_cached_symbols(&self, uri: &str) -> Option<&HashMap<String, Vec<Range>>> {
        self.symbol_cache.get(uri)
    }
}

impl Default for RenameProvider {
    fn default() -> Self {
        Self::new()
    }
}
