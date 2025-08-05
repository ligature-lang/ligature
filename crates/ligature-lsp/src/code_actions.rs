//! Enhanced code actions provider for the Ligature LSP server.

use ligature_ast::{Program, Span};
use ligature_types::checker::TypeChecker;
use lsp_types::{
    CodeAction, CodeActionContext, CodeActionKind, CodeActionOrCommand, Command, Diagnostic,
    Position, Range, TextEdit, Url, WorkspaceEdit,
};
use std::collections::HashMap;

/// Enhanced provider for code actions and quick fixes.
pub struct CodeActionsProvider {
    /// Cache of code actions by document URI.
    actions_cache: HashMap<String, Vec<CodeAction>>,
    /// Type checker for type-aware code actions.
    type_checker: TypeChecker,
    /// Configuration for code actions.
    config: CodeActionsConfig,
}

/// Configuration for code actions.
#[derive(Debug, Clone)]
pub struct CodeActionsConfig {
    /// Whether to enable advanced refactoring actions.
    pub enable_advanced_refactoring: bool,
    /// Whether to enable code generation actions.
    pub enable_code_generation: bool,
    /// Whether to enable type-aware fixes.
    pub enable_type_aware_fixes: bool,
    /// Whether to enable performance suggestions.
    pub enable_performance_suggestions: bool,
    /// Whether to enable style suggestions.
    pub enable_style_suggestions: bool,
}

impl Default for CodeActionsConfig {
    fn default() -> Self {
        Self {
            enable_advanced_refactoring: true,
            enable_code_generation: true,
            enable_type_aware_fixes: true,
            enable_performance_suggestions: true,
            enable_style_suggestions: true,
        }
    }
}

impl CodeActionsProvider {
    /// Create a new enhanced code actions provider.
    pub fn new() -> Self {
        Self {
            actions_cache: HashMap::new(),
            type_checker: TypeChecker::new(),
            config: CodeActionsConfig::default(),
        }
    }

    /// Create a new code actions provider with custom configuration.
    pub fn with_config(config: CodeActionsConfig) -> Self {
        Self {
            actions_cache: HashMap::new(),
            type_checker: TypeChecker::new(),
            config,
        }
    }

    /// Provide enhanced code actions for a given range and context.
    pub async fn provide_code_actions(
        &self,
        uri: &str,
        content: &str,
        range: Range,
        context: &CodeActionContext,
    ) -> Vec<CodeActionOrCommand> {
        // Try to parse the program for context-aware code actions
        let ast = ligature_parser::parse_program(content).ok();

        let mut actions = Vec::new();

        // Add quick fixes for diagnostics
        for diagnostic in &context.diagnostics {
            if let Some(quick_fix) =
                self.create_enhanced_quick_fix(uri, diagnostic, content, ast.as_ref())
            {
                actions.push(CodeActionOrCommand::CodeAction(quick_fix));
            }
        }

        // Add type-aware fixes
        if self.config.enable_type_aware_fixes {
            if let Some(program) = ast.as_ref() {
                actions.extend(self.create_enhanced_type_aware_fixes(uri, range, content, program));
            }
        }

        // Add advanced refactoring actions
        if self.config.enable_advanced_refactoring {
            actions.extend(self.create_advanced_refactoring_actions(
                uri,
                range,
                content,
                ast.as_ref(),
            ));
        }

        // Add code generation actions
        if self.config.enable_code_generation {
            actions.extend(self.create_enhanced_code_generation_actions(
                uri,
                range,
                content,
                ast.as_ref(),
            ));
        }

        // Add performance suggestions
        if self.config.enable_performance_suggestions {
            if let Some(program) = ast.as_ref() {
                actions.extend(self.create_performance_suggestions(uri, range, content, program));
            }
        }

        // Add style suggestions
        if self.config.enable_style_suggestions {
            actions.extend(self.create_style_suggestions(uri, range, content, ast.as_ref()));
        }

        // Add source actions
        actions.extend(self.create_enhanced_source_actions(uri, range, content, ast.as_ref()));

        actions
    }

    /// Get code actions for a given range and context (original method).
    pub fn get_code_actions(
        &mut self,
        uri: &str,
        range: Range,
        diagnostics: &[Diagnostic],
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Add quick fixes for diagnostics
        for diagnostic in diagnostics {
            if let Some(quick_fix) = self.create_quick_fix(uri, diagnostic, content, ast) {
                actions.push(CodeActionOrCommand::CodeAction(quick_fix));
            }
        }

        // Add type-aware fixes
        if let Some(program) = ast {
            actions.extend(self.create_type_aware_fixes(uri, range, content, program));
        }

        // Add refactoring actions
        actions.extend(self.create_refactoring_actions(uri, range, content, ast));

        // Add source actions
        actions.extend(self.create_source_actions(uri, range, content, ast));

        // Add code generation actions
        actions.extend(self.create_code_generation_actions(uri, range, content, ast));

        // Cache the actions
        self.actions_cache.insert(
            uri.to_string(),
            actions
                .iter()
                .filter_map(|action| {
                    if let CodeActionOrCommand::CodeAction(action) = action {
                        Some(action.clone())
                    } else {
                        None
                    }
                })
                .collect(),
        );

        actions
    }

    /// Create quick fixes for diagnostics.
    fn create_quick_fix(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<CodeAction> {
        // Check if this is a parse error that we can fix
        if let Some(code) = &diagnostic.code {
            match code {
                lsp_types::NumberOrString::String(code) => match code.as_str() {
                    "E001" => self.fix_parse_error(uri, diagnostic, content),
                    "E002" => self.fix_invalid_identifier(uri, diagnostic, content),
                    "E003" => self.fix_duplicate_identifier(uri, diagnostic, content),
                    "E004" => self.fix_undefined_identifier(uri, diagnostic, content),
                    _ => None,
                },
                _ => None,
            }
        } else {
            None
        }
    }

    /// Fix parse errors by suggesting common corrections.
    fn fix_parse_error(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        let message = &diagnostic.message;

        // Common parse error fixes
        if message.contains("expected") && message.contains(";") {
            Some(CodeAction {
                title: "Add missing semicolon".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: format!("{};", content),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(true),
                disabled: None,
                data: None,
            })
        } else if message.contains("unexpected") && message.contains("token") {
            Some(CodeAction {
                title: "Remove unexpected token".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: "".to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            })
        } else {
            None
        }
    }

    /// Fix invalid identifier errors.
    fn fix_invalid_identifier(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        // Extract the invalid identifier from the error message
        if let Some(invalid_name) = diagnostic.message.strip_prefix("Invalid identifier: ") {
            // Suggest a valid identifier name
            let valid_name = self.suggest_valid_identifier(invalid_name);

            Some(CodeAction {
                title: format!("Rename to '{}'", valid_name),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: valid_name,
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(true),
                disabled: None,
                data: None,
            })
        } else {
            None
        }
    }

    /// Fix duplicate identifier errors.
    fn fix_duplicate_identifier(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        if let Some(duplicate_name) = diagnostic.message.strip_prefix("Duplicate identifier: ") {
            // Suggest renaming the duplicate
            let new_name = format!("{}_new", duplicate_name);

            Some(CodeAction {
                title: format!("Rename to '{}'", new_name),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: new_name,
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(true),
                disabled: None,
                data: None,
            })
        } else {
            None
        }
    }

    /// Fix undefined identifier errors.
    fn fix_undefined_identifier(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        if let Some(undefined_name) = diagnostic.message.strip_prefix("Undefined identifier: ") {
            // Suggest adding an import or declaration
            Some(CodeAction {
                title: format!("Add declaration for '{}'", undefined_name),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: Range {
                                start: Position {
                                    line: 0,
                                    character: 0,
                                },
                                end: Position {
                                    line: 0,
                                    character: 0,
                                },
                            },
                            new_text: format!("let {} = undefined;\n", undefined_name),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            })
        } else {
            None
        }
    }

    /// Create type-aware fixes based on type checking results.
    fn create_type_aware_fixes(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Type check the program to find type errors
        if let Err(type_error) = ligature_types::type_check_program(program) {
            actions.extend(self.create_type_error_fixes(uri, &type_error, content));
        }

        // Suggest type annotations
        actions.extend(self.suggest_type_annotations(uri, range, content, program));

        // Suggest type conversions
        actions.extend(self.suggest_type_conversions(uri, range, content, program));

        actions
    }

    /// Create fixes for type errors.
    fn create_type_error_fixes(
        &self,
        _uri: &str,
        type_error: &ligature_ast::AstError,
        _content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        match type_error {
            ligature_ast::AstError::MethodTypeMismatch {
                method: _,
                expected,
                found,
                span,
            } => {
                if let Some(fix) = self.fix_type_mismatch(
                    _uri,
                    &format!("{:?}", expected),
                    &format!("{:?}", found),
                    *span,
                    _content,
                ) {
                    actions.push(CodeActionOrCommand::CodeAction(fix));
                }
            }
            ligature_ast::AstError::UndefinedIdentifier { name, span } => {
                if let Some(fix) = self.suggest_import_or_definition(_uri, name, *span, _content) {
                    actions.push(CodeActionOrCommand::CodeAction(fix));
                }
            }
            _ => {}
        }

        actions
    }

    /// Fix type mismatches by suggesting appropriate conversions or corrections.
    fn fix_type_mismatch(
        &self,
        uri: &str,
        expected: &str,
        actual: &str,
        span: Span,
        content: &str,
    ) -> Option<CodeAction> {
        let range = self.span_to_range(span);

        // Common type mismatch fixes
        let fix = match (expected, actual) {
            ("Int", "String") => {
                // Suggest converting string to int
                Some(("Convert string to integer", "parseInt(${1:value})"))
            }
            ("String", "Int") => {
                // Suggest converting int to string
                Some(("Convert integer to string", "toString(${1:value})"))
            }
            ("Bool", "Int") => {
                // Suggest converting int to bool
                Some(("Convert integer to boolean", "(${1:value} != 0)"))
            }
            ("Int", "Bool") => {
                // Suggest converting bool to int
                Some(("Convert boolean to integer", "if ${1:value} then 1 else 0"))
            }
            _ => None,
        };

        fix.map(|(title, replacement)| CodeAction {
            title: title.to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                    vec![TextEdit {
                        range,
                        new_text: replacement.to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        })
    }

    /// Suggest imports or definitions for undefined identifiers.
    fn suggest_import_or_definition(
        &self,
        uri: &str,
        name: &str,
        span: Span,
        _content: &str,
    ) -> Option<CodeAction> {
        let _range = self.span_to_range(span);

        // Check if this might be a built-in function
        let builtins = [
            "add", "sub", "mul", "div", "eq", "lt", "gt", "concat", "length", "head", "tail",
        ];

        if builtins.contains(&name) {
            // Suggest adding an import for built-in functions
            Some(CodeAction {
                title: format!("Import built-in function '{}'", name),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: Range {
                                start: Position {
                                    line: 0,
                                    character: 0,
                                },
                                end: Position {
                                    line: 0,
                                    character: 0,
                                },
                            },
                            new_text: format!("import {} from \"stdlib/core\";\n", name),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(true),
                disabled: None,
                data: None,
            })
        } else {
            // Suggest creating a definition
            Some(CodeAction {
                title: format!("Create definition for '{}'", name),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: Range {
                                start: Position {
                                    line: 0,
                                    character: 0,
                                },
                                end: Position {
                                    line: 0,
                                    character: 0,
                                },
                            },
                            new_text: format!("let {} = $1;\n", name),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            })
        }
    }

    /// Suggest type annotations for expressions.
    fn suggest_type_annotations(
        &self,
        uri: &str,
        range: Range,
        content: &str,
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
                            title: format!("Add type annotation: {}", inferred_type),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::from([(
                                    Url::parse(uri)
                                        .unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                                    vec![TextEdit {
                                        range: self.span_to_range(value_decl.value.span),
                                        new_text: format!(
                                            "let {}: {} = ",
                                            value_decl.name, inferred_type
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
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find expressions that might need type conversions
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if let Some(type_annotation) = &value_decl.type_annotation {
                    let expected_type = format!("{:?}", type_annotation);
                    let actual_type = self.infer_expression_type(&value_decl.value);

                    if let Some(actual) = actual_type {
                        if actual != expected_type {
                            // Suggest type conversion
                            let conversion = self.suggest_type_conversion(&actual, &expected_type);
                            if let Some(conv) = conversion {
                                let action = CodeAction {
                                    title: format!("Convert {} to {}", actual, expected_type),
                                    kind: Some(CodeActionKind::REFACTOR),
                                    diagnostics: None,
                                    edit: Some(WorkspaceEdit {
                                        changes: Some(HashMap::from([(
                                            Url::parse(uri).unwrap_or_else(|_| {
                                                Url::parse("file:///").unwrap()
                                            }),
                                            vec![TextEdit {
                                                range: self.span_to_range(value_decl.value.span),
                                                new_text: format!("{}({})", conv, content),
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

    /// Create code generation actions.
    fn create_code_generation_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate boilerplate code
        actions.extend(self.create_boilerplate_actions(uri, range, content));

        // Generate constructors
        actions.extend(self.create_constructor_actions(uri, range, content, ast));

        // Generate pattern matching
        actions.extend(self.create_pattern_matching_actions(uri, range, content, ast));

        actions
    }

    /// Create boilerplate code generation actions.
    fn create_boilerplate_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate function template
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate function template".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "fun ${1:name}(${2:params}) : ${3:return_type} = ${4:body}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate type definition
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate type definition".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "type ${1:TypeName} = ${2:definition}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create constructor generation actions.
    fn create_constructor_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate data type with constructors
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate data type with constructors".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "data ${1:TypeName} = ${2:Constructor1} | ${3:Constructor2}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create pattern matching generation actions.
    fn create_pattern_matching_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate match expression
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate match expression".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "match ${1:expression} of\n  ${2:pattern1} => ${3:result1}\n  ${4:pattern2} => ${5:result2}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create refactoring actions.
    fn create_refactoring_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Extract function action
        if let Some(extract_action) = self.create_extract_function_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(extract_action));
        }

        // Inline variable action
        if let Some(inline_action) = self.create_inline_variable_action(uri, range, content, ast) {
            actions.push(CodeActionOrCommand::CodeAction(inline_action));
        }

        // Rename symbol action
        if let Some(rename_action) = self.create_rename_symbol_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(rename_action));
        }

        actions
    }

    /// Create extract function action.
    fn create_extract_function_action(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        // This is a placeholder - in a real implementation, you'd analyze the selected code
        // and determine if it can be extracted into a function
        Some(CodeAction {
            title: "Extract function".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Extract function".to_string(),
                command: "ligature.extractFunction".to_string(),
                arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        })
    }

    /// Create inline variable action.
    fn create_inline_variable_action(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Option<CodeAction> {
        // This is a placeholder - in a real implementation, you'd analyze the AST
        // to find variable declarations that can be inlined
        Some(CodeAction {
            title: "Inline variable".to_string(),
            kind: Some(CodeActionKind::REFACTOR_INLINE),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Inline variable".to_string(),
                command: "ligature.inlineVariable".to_string(),
                arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        })
    }



    /// Create source actions.
    fn create_source_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Organize imports action
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Organize imports".to_string(),
            kind: Some(CodeActionKind::SOURCE_ORGANIZE_IMPORTS),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Organize imports".to_string(),
                command: "ligature.organizeImports".to_string(),
                arguments: Some(vec![serde_json::json!(uri)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        }));

        // Fix all auto-fixable problems
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Fix all auto-fixable problems".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Fix all auto-fixable problems".to_string(),
                command: "ligature.fixAll".to_string(),
                arguments: Some(vec![serde_json::json!(uri)]),
            }),
            is_preferred: Some(true),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Suggest a valid identifier name.
    fn suggest_valid_identifier(&self, invalid_name: &str) -> String {
        // Remove invalid characters and convert to valid identifier
        let mut valid_name = String::new();
        let mut capitalize_next = false;

        for ch in invalid_name.chars() {
            if ch.is_alphanumeric() || ch == '_' {
                if capitalize_next {
                    valid_name.push(ch.to_ascii_uppercase());
                    capitalize_next = false;
                } else {
                    valid_name.push(ch);
                }
            } else if ch.is_whitespace() || ch == '-' {
                capitalize_next = true;
            }
        }

        // Ensure it starts with a letter or underscore
        if valid_name.is_empty()
            || (!valid_name.chars().next().unwrap().is_alphabetic() && !valid_name.starts_with('_'))
        {
            valid_name = format!("_{}", valid_name);
        }

        valid_name
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
                character: (span.column + span.len()) as u32,
            },
        }
    }

    /// Clear the cache for a document.
    pub fn clear_cache(&mut self, uri: &str) {
        self.actions_cache.remove(uri);
    }

    /// Get cached actions for a document.
    pub fn get_cached_actions(&self, uri: &str) -> Option<&Vec<CodeAction>> {
        self.actions_cache.get(uri)
    }

    /// Infer the type of an expression.
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
            ligature_ast::ExprKind::Let { value, body, .. } => {
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

    /// Create enhanced quick fixes for diagnostics.
    fn create_enhanced_quick_fix(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<CodeAction> {
        // Check if this is a parse error that we can fix
        if let Some(code) = &diagnostic.code {
            match code {
                lsp_types::NumberOrString::String(code) => match code.as_str() {
                    "E001" => self.fix_enhanced_parse_error(uri, diagnostic, content),
                    "E002" => self.fix_invalid_identifier(uri, diagnostic, content),
                    "E003" => self.fix_duplicate_identifier(uri, diagnostic, content),
                    "E004" => self.fix_undefined_identifier(uri, diagnostic, content),
                    "T001" => {
                        // Extract type information from diagnostic message
                        if let Some((expected, actual)) = self.extract_type_info(&diagnostic.message) {
                            // Create a default span from the diagnostic range
                            let span = ligature_ast::Span {
                                line: diagnostic.range.start.line as usize,
                                column: diagnostic.range.start.character as usize,
                                start: diagnostic.range.start.line as usize,
                                end: diagnostic.range.end.line as usize,
                            };
                            self.fix_type_mismatch(uri, &expected, &actual, span, content)
                        } else {
                            None
                        }
                    }
                    "T002" => self.fix_undefined_type(uri, diagnostic, content, ast),
                    "W001" => self.fix_unused_import(uri, diagnostic, content),
                    "I001" => self.fix_long_line(uri, diagnostic, content),
                    "I002" => self.fix_trailing_whitespace(uri, diagnostic, content),
                    _ => None,
                },
                _ => None,
            }
        } else {
            None
        }
    }

    /// Fix enhanced parse errors with more intelligent suggestions.
    fn fix_enhanced_parse_error(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        let message = &diagnostic.message;

        // Enhanced parse error fixes with more context
        if message.contains("expected") && message.contains(";") {
            Some(CodeAction {
                title: "Add missing semicolon".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: format!("{};", content),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(true),
                disabled: None,
                data: None,
            })
        } else if message.contains("unexpected") && message.contains("token") {
            Some(CodeAction {
                title: "Remove unexpected token".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: "".to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            })
        } else if message.contains("missing") && message.contains("closing") {
            // Suggest adding missing closing brace/bracket/parenthesis
            let closing_char = if message.contains("brace") {
                "}"
            } else if message.contains("bracket") {
                "]"
            } else if message.contains("parenthesis") {
                ")"
            } else {
                ""
            };

            if !closing_char.is_empty() {
                Some(CodeAction {
                    title: format!("Add missing closing {}", closing_char),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diagnostic.clone()]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(HashMap::from([(
                            Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                            vec![TextEdit {
                                range: diagnostic.range,
                                new_text: format!("{}{}", content, closing_char),
                            }],
                        )])),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(true),
                    disabled: None,
                    data: None,
                })
            } else {
                None
            }
        } else {
            None
        }
    }



    /// Fix undefined types with import suggestions.
    fn fix_undefined_type(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<CodeAction> {
        let message = &diagnostic.message;

        if let Some(type_name) = message.strip_prefix("Undefined type: ") {
            // Check if this is a built-in type
            let builtin_types = ["Int", "Float", "String", "Bool", "List", "Unit"];
            if builtin_types.contains(&type_name) {
                Some(CodeAction {
                    title: format!("Import built-in type '{}'", type_name),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diagnostic.clone()]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(HashMap::from([(
                            Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                            vec![TextEdit {
                                range: Range {
                                    start: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                    end: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                },
                                new_text: format!("import {} from \"stdlib/core\";\n", type_name),
                            }],
                        )])),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(true),
                    disabled: None,
                    data: None,
                })
            } else {
                // Suggest creating a type definition
                Some(CodeAction {
                    title: format!("Create type definition for '{}'", type_name),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diagnostic.clone()]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(HashMap::from([(
                            Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                            vec![TextEdit {
                                range: Range {
                                    start: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                    end: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                },
                                new_text: format!("type {} = $1;\n", type_name),
                            }],
                        )])),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(false),
                    disabled: None,
                    data: None,
                })
            }
        } else {
            None
        }
    }

    /// Fix unused imports by removing them.
    fn fix_unused_import(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        _content: &str,
    ) -> Option<CodeAction> {
        Some(CodeAction {
            title: "Remove unused import".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![diagnostic.clone()]),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: "".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        })
    }

    /// Fix long lines by wrapping them.
    fn fix_long_line(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        // Simple line wrapping at 80 characters
        let line = content;
        if line.len() > 80 {
            let wrapped = self.wrap_line(line, 80);
            Some(CodeAction {
                title: "Wrap long line".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: wrapped,
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            })
        } else {
            None
        }
    }

    /// Fix trailing whitespace.
    fn fix_trailing_whitespace(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        let trimmed = content.trim_end();
        Some(CodeAction {
            title: "Remove trailing whitespace".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![diagnostic.clone()]),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: trimmed.to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        })
    }

    /// Create enhanced type-aware fixes.
    fn create_enhanced_type_aware_fixes(
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

    /// Suggest enhanced type annotations.
    fn suggest_enhanced_type_annotations(
        &self,
        uri: &str,
        range: Range,
        content: &str,
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
                            title: format!("Add type annotation: {}", inferred_type),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::from([(
                                    Url::parse(uri)
                                        .unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                                    vec![TextEdit {
                                        range: self.span_to_range(value_decl.value.span),
                                        new_text: format!(
                                            "let {}: {} = ",
                                            value_decl.name, inferred_type
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

    /// Create advanced refactoring actions.
    fn create_advanced_refactoring_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Extract function action
        if let Some(extract_action) = self.create_extract_function_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(extract_action));
        }

        // Inline variable action
        if let Some(inline_action) = self.create_inline_variable_action(uri, range, content, ast) {
            actions.push(CodeActionOrCommand::CodeAction(inline_action));
        }

        // Rename symbol action
        if let Some(rename_action) = self.create_rename_symbol_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(rename_action));
        }

        // Extract constant action
        if let Some(constant_action) = self.create_extract_constant_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(constant_action));
        }

        // Convert to function action
        if let Some(convert_action) = self.create_convert_to_function_action(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(convert_action));
        }

        actions
    }

    /// Create enhanced code generation actions.
    fn create_enhanced_code_generation_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate boilerplate code
        actions.extend(self.create_enhanced_boilerplate_actions(uri, range, content));

        // Generate constructors
        actions.extend(self.create_enhanced_constructor_actions(uri, range, content, ast));

        // Generate pattern matching
        actions.extend(self.create_enhanced_pattern_matching_actions(uri, range, content, ast));

        // Generate tests
        actions.extend(self.create_test_generation_actions(uri, range, content, ast));

        // Generate documentation
        actions.extend(self.create_documentation_generation_actions(uri, range, content, ast));

        actions
    }

    /// Create performance suggestions.
    fn create_performance_suggestions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Check for inefficient patterns
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                // Check for repeated calculations
                if self.has_repeated_calculations(&value_decl.value) {
                    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                        title: "Extract repeated calculation to variable".to_string(),
                        kind: Some(CodeActionKind::REFACTOR),
                        diagnostics: None,
                        edit: None,
                        command: Some(Command {
                            title: "Extract repeated calculation".to_string(),
                            command: "ligature.extractRepeatedCalculation".to_string(),
                            arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
                        }),
                        is_preferred: Some(false),
                        disabled: None,
                        data: None,
                    }));
                }

                // Check for inefficient list operations
                if self.has_inefficient_list_operations(&value_decl.value) {
                    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                        title: "Optimize list operations".to_string(),
                        kind: Some(CodeActionKind::REFACTOR),
                        diagnostics: None,
                        edit: None,
                        command: Some(Command {
                            title: "Optimize list operations".to_string(),
                            command: "ligature.optimizeListOperations".to_string(),
                            arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
                        }),
                        is_preferred: Some(false),
                        disabled: None,
                        data: None,
                    }));
                }
            }
        }

        actions
    }

    /// Create style suggestions.
    fn create_style_suggestions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Suggest consistent naming
        if let Some(naming_action) = self.create_naming_suggestion(uri, range, content) {
            actions.push(CodeActionOrCommand::CodeAction(naming_action));
        }

        // Suggest function extraction for long expressions
        if let Some(extract_action) =
            self.create_function_extraction_suggestion(uri, range, content)
        {
            actions.push(CodeActionOrCommand::CodeAction(extract_action));
        }

        // Suggest constant extraction for magic numbers
        if let Some(constant_action) =
            self.create_constant_extraction_suggestion(uri, range, content)
        {
            actions.push(CodeActionOrCommand::CodeAction(constant_action));
        }

        actions
    }

    /// Create enhanced source actions.
    fn create_enhanced_source_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Organize imports action
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Organize imports".to_string(),
            kind: Some(CodeActionKind::SOURCE_ORGANIZE_IMPORTS),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Organize imports".to_string(),
                command: "ligature.organizeImports".to_string(),
                arguments: Some(vec![serde_json::json!(uri)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        }));

        // Fix all auto-fixable problems
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Fix all auto-fixable problems".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Fix all auto-fixable problems".to_string(),
                command: "ligature.fixAll".to_string(),
                arguments: Some(vec![serde_json::json!(uri)]),
            }),
            is_preferred: Some(true),
            disabled: None,
            data: None,
        }));

        // Add missing exports
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Add missing exports".to_string(),
            kind: Some(CodeActionKind::SOURCE),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Add missing exports".to_string(),
                command: "ligature.addMissingExports".to_string(),
                arguments: Some(vec![serde_json::json!(uri)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        }));

        actions
    }

    // Helper methods

    /// Extract type information from error message.
    fn extract_type_info(&self, message: &str) -> Option<(String, String)> {
        // Look for patterns like "expected X, got Y"
        if let Some(parts) = message.split("expected ").nth(1) {
            if let Some(expected_part) = parts.split(", got ").next() {
                if let Some(found_part) = parts.split(", got ").nth(1) {
                    let expected = expected_part.trim().to_string();
                    let found = found_part.trim().to_string();
                    return Some((expected, found));
                }
            }
        }
        None
    }

    /// Wrap a long line at the specified width.
    fn wrap_line(&self, line: &str, width: usize) -> String {
        if line.len() <= width {
            return line.to_string();
        }

        // Simple word-based wrapping
        let words: Vec<&str> = line.split_whitespace().collect();
        let mut result = String::new();
        let mut current_line = String::new();

        for word in words {
            if current_line.len() + word.len() + 1 <= width {
                if !current_line.is_empty() {
                    current_line.push(' ');
                }
                current_line.push_str(word);
            } else {
                if !result.is_empty() {
                    result.push('\n');
                }
                result.push_str(&current_line);
                current_line = word.to_string();
            }
        }

        if !current_line.is_empty() {
            if !result.is_empty() {
                result.push('\n');
            }
            result.push_str(&current_line);
        }

        result
    }

    /// Check if an expression has repeated calculations.
    fn has_repeated_calculations(&self, expr: &ligature_ast::Expr) -> bool {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST for repeated sub-expressions
        false
    }

    /// Check if an expression has inefficient list operations.
    fn has_inefficient_list_operations(&self, expr: &ligature_ast::Expr) -> bool {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST for inefficient list patterns
        false
    }

    /// Create naming suggestion action.
    fn create_naming_suggestion(
        &self,
        _uri: &str,
        _range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        // This is a placeholder implementation
        None
    }

    /// Create function extraction suggestion.
    fn create_function_extraction_suggestion(
        &self,
        _uri: &str,
        _range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        // This is a placeholder implementation
        None
    }

    /// Create constant extraction suggestion.
    fn create_constant_extraction_suggestion(
        &self,
        _uri: &str,
        _range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        // This is a placeholder implementation
        None
    }

    /// Create extract function action.


    /// Create inline variable action.


    /// Create rename symbol action.
    fn create_rename_symbol_action(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        Some(CodeAction {
            title: "Rename symbol".to_string(),
            kind: Some(CodeActionKind::REFACTOR),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Rename symbol".to_string(),
                command: "ligature.renameSymbol".to_string(),
                arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        })
    }

    /// Create extract constant action.
    fn create_extract_constant_action(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        Some(CodeAction {
            title: "Extract constant".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Extract constant".to_string(),
                command: "ligature.extractConstant".to_string(),
                arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        })
    }

    /// Create convert to function action.
    fn create_convert_to_function_action(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Option<CodeAction> {
        Some(CodeAction {
            title: "Convert to function".to_string(),
            kind: Some(CodeActionKind::REFACTOR),
            diagnostics: None,
            edit: None,
            command: Some(Command {
                title: "Convert to function".to_string(),
                command: "ligature.convertToFunction".to_string(),
                arguments: Some(vec![serde_json::json!(uri), serde_json::json!(range)]),
            }),
            is_preferred: None,
            disabled: None,
            data: None,
        })
    }

    /// Create enhanced boilerplate actions.
    fn create_enhanced_boilerplate_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate function template
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate function template".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "fun ${1:name}(${2:params}) : ${3:return_type} = ${4:body}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate type definition
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate type definition".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "type ${1:TypeName} = ${2:definition}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate module template
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate module template".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "module ${1:ModuleName} {\n  ${2:// module content}\n}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create enhanced constructor actions.
    fn create_enhanced_constructor_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate data type with constructors
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate data type with constructors".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "data ${1:TypeName} = ${2:Constructor1} | ${3:Constructor2}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate type class
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate type class".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "class ${1:ClassName} a where\n  ${2:method1} :: a -> ${3:ResultType}\n  ${4:method2} :: a -> ${5:ResultType}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create enhanced pattern matching actions.
    fn create_enhanced_pattern_matching_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate match expression
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate match expression".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "match ${1:expression} of\n  ${2:pattern1} => ${3:result1}\n  ${4:pattern2} => ${5:result2}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate if-else expression
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate if-else expression".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text:
                            "if ${1:condition} then\n  ${2:then_branch}\nelse\n  ${3:else_branch}"
                                .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create test generation actions.
    fn create_test_generation_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate unit test
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate unit test".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "test \"${1:test_name}\" = ${2:test_expression}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate property test
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate property test".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text:
                            "property \"${1:property_name}\" = forAll ${2:generator} ${3:property}"
                                .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Create documentation generation actions.
    fn create_documentation_generation_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate function documentation
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate function documentation".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "/// ${1:Function description}\n/// @param ${2:param_name} ${3:param_description}\n/// @return ${4:return_description}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        // Generate module documentation
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate module documentation".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "/// ${1:Module description}\n/// @author ${2:author_name}\n/// @version ${3:version}".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Suggest enhanced type conversions.
    fn suggest_enhanced_type_conversions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Find expressions that might need type conversions
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                if let Some(type_annotation) = &value_decl.type_annotation {
                    let expected_type = format!("{:?}", type_annotation);
                    let actual_type = self.infer_expression_type(&value_decl.value);

                    if let Some(actual) = actual_type {
                        if actual != expected_type {
                            // Suggest type conversion
                            let conversion = self.suggest_type_conversion(&actual, &expected_type);
                            if let Some(conv) = conversion {
                                let action = CodeAction {
                                    title: format!("Convert {} to {}", actual, expected_type),
                                    kind: Some(CodeActionKind::REFACTOR),
                                    diagnostics: None,
                                    edit: Some(WorkspaceEdit {
                                        changes: Some(HashMap::from([(
                                            Url::parse(uri).unwrap_or_else(|_| {
                                                Url::parse("file:///").unwrap()
                                            }),
                                            vec![TextEdit {
                                                range: self.span_to_range(value_decl.value.span),
                                                new_text: format!("{}({})", conv, content),
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
        uri: &str,
        range: Range,
        content: &str,
        program: &Program,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // This is a placeholder implementation
        // In a full implementation, you would analyze the program for potential type guard opportunities

        actions
    }
}

impl Default for CodeActionsProvider {
    fn default() -> Self {
        Self::new()
    }
}
