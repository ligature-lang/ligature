//! Type-aware fixes and suggestions based on type checking.

use std::collections::HashMap;

use ligature_ast::{Program, Span};
use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, Position, Range, TextEdit, Url, WorkspaceEdit,
};

/// Handler for type-aware fixes and suggestions.
pub struct TypeAwareFixes;

impl TypeAwareFixes {
    /// Create a new type-aware fixes handler.
    pub fn new() -> Self {
        Self
    }

    /// Create type-aware fixes based on type checking results.
    pub fn create_type_aware_fixes(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Type check the program to find type errors
        // if let Err(type_error) = ligature_types::type_check_program(program) {
        //     actions.extend(self.create_type_error_fixes(uri, &type_error, content));
        // }

        // Suggest type annotations
        actions.extend(self.suggest_type_annotations(uri, range, content, program));

        // Suggest type conversions
        actions.extend(self.suggest_type_conversions(uri, range, content, program));

        actions
    }

    /// Create enhanced type-aware fixes.
    pub fn create_enhanced_type_aware_fixes(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Suggest type annotations for expressions
        actions.extend(self.suggest_enhanced_type_annotations(uri, range, content, program));

        // Suggest type conversions
        actions.extend(self.suggest_enhanced_type_conversions(uri, range, content, program));

        // Suggest type guards
        actions.extend(self.suggest_type_guards(uri, range, content, program));

        actions
    }

    #[allow(dead_code)]
    fn create_type_error_fixes(
        &self,
        error: &ligature_ast::AstError,
        uri: &str,
        range: lsp_types::Range,
    ) -> Vec<lsp_types::CodeAction> {
        let mut actions = Vec::new();

        match error {
            ligature_ast::AstError::MethodTypeMismatch {
                expected, found, ..
            } => {
                // Add fix suggestions for type mismatches
                let expected_str = format!("{expected:?}");
                let found_str = format!("{found:?}");
                if let Some(fix) = self.fix_type_mismatch(&expected_str, &found_str) {
                    actions.push(lsp_types::CodeAction {
                        title: format!("Fix type mismatch: {found_str} -> {expected_str}"),
                        kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                        diagnostics: None,
                        edit: Some(lsp_types::WorkspaceEdit {
                            changes: Some(std::collections::HashMap::from([(
                                lsp_types::Url::parse(uri)
                                    .unwrap_or_else(|_| lsp_types::Url::parse("file:///").unwrap()),
                                vec![lsp_types::TextEdit {
                                    range,
                                    new_text: fix,
                                }],
                            )])),
                            document_changes: None,
                            change_annotations: None,
                        }),
                        command: None,
                        is_preferred: Some(true),
                        disabled: None,
                        data: None,
                    });
                }
            }
            ligature_ast::AstError::UndefinedIdentifier { name, .. } => {
                // Add suggestions for undefined variables
                if let Some(suggestion) = self.suggest_import_or_definition(name) {
                    actions.push(lsp_types::CodeAction {
                        title: format!("Add import or definition for '{name}'"),
                        kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                        diagnostics: None,
                        edit: Some(lsp_types::WorkspaceEdit {
                            changes: Some(std::collections::HashMap::from([(
                                lsp_types::Url::parse(uri)
                                    .unwrap_or_else(|_| lsp_types::Url::parse("file:///").unwrap()),
                                vec![lsp_types::TextEdit {
                                    range,
                                    new_text: suggestion,
                                }],
                            )])),
                            document_changes: None,
                            change_annotations: None,
                        }),
                        command: None,
                        is_preferred: Some(false),
                        disabled: None,
                        data: None,
                    });
                }
            }
            _ => {}
        }

        actions
    }

    #[allow(dead_code)]
    fn fix_type_mismatch(&self, expected: &str, found: &str) -> Option<String> {
        // Simple type conversion suggestions
        match (expected, found) {
            ("Int", "String") => Some("parseInt".to_string()),
            ("String", "Int") => Some("toString".to_string()),
            ("Bool", "Int") => Some("x != 0".to_string()),
            ("Int", "Bool") => Some("if x then 1 else 0".to_string()),
            _ => None,
        }
    }

    #[allow(dead_code)]
    fn suggest_import_or_definition(&self, name: &str) -> Option<String> {
        // Suggest common imports or definitions
        match name {
            "add" | "sub" | "mul" | "div" => Some(format!("import {name} from \"stdlib/core\"")),
            "map" | "filter" | "fold" => Some(format!("import {name} from \"stdlib/collections\"")),
            "readFile" | "writeFile" => Some(format!("import {name} from \"stdlib/io\"")),
            _ => Some(format!("let {name} = undefined")),
        }
    }

    /// Suggest type annotations for expressions.
    fn suggest_type_annotations(
        &self,
        uri: &str,
        _range: Range,
        _content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find let bindings without type annotations
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if value_decl.type_annotation.is_none() {
                    // Try to infer the type
                    if let Some(inferred_type) = self.infer_expression_type(&value_decl.value) {
                        let action = CodeAction {
                            title: format!("Add type annotation: {inferred_type}"),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::from([(
                                    Url::parse(uri)
                                        .unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                                    vec![TextEdit {
                                        range: self.span_to_range(value_decl.value.span.clone()),
                                        new_text: format!(
                                            "let {name}: {inferred_type} = ",
                                            name = value_decl.name,
                                            inferred_type = inferred_type
                                        ),
                                    }],
                                )])),
                                document_changes: None,
                                change_annotations: None,
                            }),
                            command: None,
                            is_preferred: Some(false),
                            disabled: None,
                            data: None,
                        };
                        actions.push(CodeActionOrCommand::CodeAction(action));
                    }
                }
            }
        }

        actions
    }

    /// Suggest enhanced type annotations.
    fn suggest_enhanced_type_annotations(
        &self,
        uri: &str,
        _range: Range,
        _content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find let bindings without type annotations
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if value_decl.type_annotation.is_none() {
                    // Try to infer the type
                    if let Some(inferred_type) = self.infer_expression_type(&value_decl.value) {
                        let action = CodeAction {
                            title: format!("Add type annotation: {inferred_type}"),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::from([(
                                    Url::parse(uri)
                                        .unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                                    vec![TextEdit {
                                        range: self.span_to_range(value_decl.value.span.clone()),
                                        new_text: format!(
                                            "let {name}: {inferred_type} = ",
                                            name = value_decl.name,
                                            inferred_type = inferred_type
                                        ),
                                    }],
                                )])),
                                document_changes: None,
                                change_annotations: None,
                            }),
                            command: None,
                            is_preferred: Some(false),
                            disabled: None,
                            data: None,
                        };
                        actions.push(CodeActionOrCommand::CodeAction(action));
                    }
                }
            }
        }

        actions
    }

    /// Suggest type conversions for expressions.
    fn suggest_type_conversions(
        &self,
        uri: &str,
        _range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find expressions that might need type conversions
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if let Some(type_annotation) = &value_decl.type_annotation {
                    let expected_type = format!("{type_annotation:?}");
                    let actual_type = self.infer_expression_type(&value_decl.value);

                    if let Some(actual) = actual_type {
                        if actual != expected_type {
                            // Suggest type conversion
                            let conversion = self.suggest_type_conversion(&actual, &expected_type);
                            if let Some(conv) = conversion {
                                let action = CodeAction {
                                    title: format!("Convert {actual} to {expected_type}"),
                                    kind: Some(CodeActionKind::REFACTOR),
                                    diagnostics: None,
                                    edit: Some(WorkspaceEdit {
                                        changes: Some(HashMap::from([(
                                            Url::parse(uri).unwrap_or_else(|_| {
                                                Url::parse("file:///").unwrap()
                                            }),
                                            vec![TextEdit {
                                                range: self
                                                    .span_to_range(value_decl.value.span.clone()),
                                                new_text: format!("{conv}({content})"),
                                            }],
                                        )])),
                                        document_changes: None,
                                        change_annotations: None,
                                    }),
                                    command: None,
                                    is_preferred: Some(false),
                                    disabled: None,
                                    data: None,
                                };
                                actions.push(CodeActionOrCommand::CodeAction(action));
                            }
                        }
                    }
                }
            }
        }

        actions
    }

    /// Suggest enhanced type conversions.
    fn suggest_enhanced_type_conversions(
        &self,
        uri: &str,
        _range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find expressions that might need type conversions
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if let Some(type_annotation) = &value_decl.type_annotation {
                    let expected_type = format!("{type_annotation:?}");
                    let actual_type = self.infer_expression_type(&value_decl.value);

                    if let Some(actual) = actual_type {
                        if actual != expected_type {
                            // Suggest type conversion
                            let conversion = self.suggest_type_conversion(&actual, &expected_type);
                            if let Some(conv) = conversion {
                                let action = CodeAction {
                                    title: format!("Convert {actual} to {expected_type}"),
                                    kind: Some(CodeActionKind::REFACTOR),
                                    diagnostics: None,
                                    edit: Some(WorkspaceEdit {
                                        changes: Some(HashMap::from([(
                                            Url::parse(uri).unwrap_or_else(|_| {
                                                Url::parse("file:///").unwrap()
                                            }),
                                            vec![TextEdit {
                                                range: self
                                                    .span_to_range(value_decl.value.span.clone()),
                                                new_text: format!("{conv}({content})"),
                                            }],
                                        )])),
                                        document_changes: None,
                                        change_annotations: None,
                                    }),
                                    command: None,
                                    is_preferred: Some(false),
                                    disabled: None,
                                    data: None,
                                };
                                actions.push(CodeActionOrCommand::CodeAction(action));
                            }
                        }
                    }
                }
            }
        }

        actions
    }

    /// Suggest type guards.
    fn suggest_type_guards(
        &self,
        _uri: &str,
        _range: Range,
        _content: &str,
        _program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        // This is a placeholder implementation
        // In a full implementation, you would analyze the program for potential type guard opportunities

        Vec::new()
    }

    // Helper methods

    /// Convert a span to a range.
    fn span_to_range(&self, span: Span) -> Range {
        Range {
            start: Position {
                line: span.line as u32,
                character: span.column as u32,
            },
            end: Position {
                line: span.line as u32,
                character: (span.column + span.len()) as u32,
            },
        }
    }

    /// Infer the type of an expression.
    #[allow(clippy::only_used_in_recursion)]
    fn infer_expression_type(&self, expr: &ligature_ast::Expr) -> Option<String> {
        match &expr.kind {
            ligature_ast::ExprKind::Literal(literal) => match literal {
                ligature_ast::Literal::Integer(_) => Some("Int".to_string()),
                ligature_ast::Literal::Float(_) => Some("Float".to_string()),
                ligature_ast::Literal::String(_) => Some("String".to_string()),
                ligature_ast::Literal::Boolean(_) => Some("Bool".to_string()),
                ligature_ast::Literal::Unit => Some("Unit".to_string()),
                ligature_ast::Literal::List(_) => Some("List".to_string()),
            },
            ligature_ast::ExprKind::Variable(_) => Some("Unknown".to_string()),
            ligature_ast::ExprKind::Application {
                function,
                argument: _,
            } => {
                // Try to infer function return type
                self.infer_expression_type(function)
            }
            ligature_ast::ExprKind::Let { body, .. } => {
                // Return the type of the body
                self.infer_expression_type(body)
            }
            ligature_ast::ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                // Both branches should have the same type
                let then_type = self.infer_expression_type(then_branch);
                let else_type = self.infer_expression_type(else_branch);
                if then_type == else_type {
                    then_type
                } else {
                    Some("Unknown".to_string())
                }
            }
            ligature_ast::ExprKind::Match { cases, .. } => {
                // Return the type of the first case
                if let Some(first_case) = cases.first() {
                    self.infer_expression_type(&first_case.expression)
                } else {
                    Some("Unknown".to_string())
                }
            }
            _ => Some("Unknown".to_string()),
        }
    }

    /// Suggest a type conversion function.
    fn suggest_type_conversion(&self, from_type: &str, to_type: &str) -> Option<String> {
        match (from_type, to_type) {
            ("String", "Int") => Some("parseInt".to_string()),
            ("Int", "String") => Some("toString".to_string()),
            ("Float", "Int") => Some("floor".to_string()),
            ("Int", "Float") => Some("toFloat".to_string()),
            ("Bool", "Int") => Some("if $1 then 1 else 0".to_string()),
            ("Int", "Bool") => Some("$1 != 0".to_string()),
            _ => None,
        }
    }
}

impl Default for TypeAwareFixes {
    fn default() -> Self {
        Self::new()
    }
}
