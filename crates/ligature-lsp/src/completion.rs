//! Completion provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Program, Type, TypeKind};
// use ligature_types::checker::TypeChecker;
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionResponse, InsertTextFormat, MarkupContent,
    MarkupKind, Position,
};

/// Provider for code completion suggestions.
pub struct CompletionProvider {
    /// Built-in keywords and their documentation.
    keywords: HashMap<&'static str, &'static str>,
    /// Built-in functions and their signatures.
    builtins: HashMap<&'static str, BuiltinFunction>,
    /// Type checker for type-aware completions.
    #[allow(dead_code)]
    // type_checker: TypeChecker,
    /// Configuration for completions.
    config: CompletionConfig,
}

/// Configuration for completion provider.
#[derive(Debug, Clone)]
pub struct CompletionConfig {
    /// Whether to enable type-aware completions.
    pub enable_type_aware_completions: bool,
    /// Whether to enable snippet completions.
    pub enable_snippet_completions: bool,
    /// Whether to enable import completions.
    pub enable_import_completions: bool,
}

impl Default for CompletionConfig {
    fn default() -> Self {
        Self {
            enable_type_aware_completions: true,
            enable_snippet_completions: true,
            enable_import_completions: true,
        }
    }
}

/// Information about a built-in function.
#[derive(Debug, Clone)]
struct BuiltinFunction {
    signature: String,
    documentation: String,
    parameters: Vec<String>,
    return_type: String,
}

impl CompletionProvider {
    /// Create a new completion provider.
    pub fn new() -> Self {
        let mut keywords = HashMap::new();
        keywords.insert("let", "Declare a value binding");
        keywords.insert("in", "Start the body of a let expression");
        keywords.insert("fun", "Define a function");
        keywords.insert("type", "Define a type alias");
        keywords.insert("data", "Define a data type");
        keywords.insert("match", "Pattern matching expression");
        keywords.insert("case", "Pattern matching");
        keywords.insert("of", "Pattern matching cases");
        keywords.insert("when", "Pattern guard condition");
        keywords.insert("if", "Conditional expression");
        keywords.insert("then", "Then branch of conditional");
        keywords.insert("else", "Else branch of conditional");
        keywords.insert("import", "Import a module");
        keywords.insert("export", "Export items from module");
        keywords.insert("module", "Define a module");
        keywords.insert("class", "Define a type class");
        keywords.insert("instance", "Define a type class instance");
        keywords.insert("where", "Where clause for definitions");

        let mut builtins = HashMap::new();
        builtins.insert(
            "add",
            BuiltinFunction {
                signature: "add : Int -> Int -> Int".to_string(),
                documentation: "Add two integers".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Int".to_string(),
            },
        );
        builtins.insert(
            "sub",
            BuiltinFunction {
                signature: "sub : Int -> Int -> Int".to_string(),
                documentation: "Subtract two integers".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Int".to_string(),
            },
        );
        builtins.insert(
            "mul",
            BuiltinFunction {
                signature: "mul : Int -> Int -> Int".to_string(),
                documentation: "Multiply two integers".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Int".to_string(),
            },
        );
        builtins.insert(
            "div",
            BuiltinFunction {
                signature: "div : Int -> Int -> Int".to_string(),
                documentation: "Divide two integers".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Int".to_string(),
            },
        );
        builtins.insert(
            "eq",
            BuiltinFunction {
                signature: "eq : a -> a -> Bool".to_string(),
                documentation: "Check if two values are equal".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Bool".to_string(),
            },
        );
        builtins.insert(
            "lt",
            BuiltinFunction {
                signature: "lt : Int -> Int -> Bool".to_string(),
                documentation: "Check if first integer is less than second".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Bool".to_string(),
            },
        );
        builtins.insert(
            "gt",
            BuiltinFunction {
                signature: "gt : Int -> Int -> Bool".to_string(),
                documentation: "Check if first integer is greater than second".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Bool".to_string(),
            },
        );
        builtins.insert(
            "concat",
            BuiltinFunction {
                signature: "concat : String -> String -> String".to_string(),
                documentation: "Concatenate two strings".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "String".to_string(),
            },
        );
        builtins.insert(
            "length",
            BuiltinFunction {
                signature: "length : List a -> Int".to_string(),
                documentation: "Get the length of a list".to_string(),
                parameters: vec!["list".to_string()],
                return_type: "Int".to_string(),
            },
        );
        builtins.insert(
            "head",
            BuiltinFunction {
                signature: "head : List a -> Maybe a".to_string(),
                documentation: "Get the first element of a list".to_string(),
                parameters: vec!["list".to_string()],
                return_type: "Maybe a".to_string(),
            },
        );
        builtins.insert(
            "tail",
            BuiltinFunction {
                signature: "tail : List a -> Maybe (List a)".to_string(),
                documentation: "Get all but the first element of a list".to_string(),
                parameters: vec!["list".to_string()],
                return_type: "Maybe (List a)".to_string(),
            },
        );
        builtins.insert(
            "cons",
            BuiltinFunction {
                signature: "cons : a -> List a -> List a".to_string(),
                documentation: "Add an element to the front of a list".to_string(),
                parameters: vec!["element".to_string(), "list".to_string()],
                return_type: "List a".to_string(),
            },
        );
        builtins.insert(
            "isEmpty",
            BuiltinFunction {
                signature: "isEmpty : List a -> Bool".to_string(),
                documentation: "Check if a list is empty".to_string(),
                parameters: vec!["list".to_string()],
                return_type: "Bool".to_string(),
            },
        );

        Self {
            keywords,
            builtins,
            // type_checker: TypeChecker::new(),
            config: CompletionConfig::default(),
        }
    }

    /// Get completions for a given position in a document.
    pub async fn provide_completion(
        &self,
        _uri: &str,
        content: &str,
        position: Position,
    ) -> CompletionResponse {
        let mut completions = Vec::new();
        let word = self.get_word_at_position(content, position);

        // Try to parse the program for context-aware completions
        let ast = ligature_parser::parse_program(content).ok();

        // Get context-aware completions
        if let Some(program) = ast.as_ref() {
            // Type-aware completions
            completions.extend(self.get_type_aware_completions(program, &word, position));

            // Symbol completions
            completions.extend(self.get_symbol_completions(program, &word));
        }

        // Always include keywords and builtins
        completions.extend(self.get_keyword_completions(&word));
        completions.extend(self.get_builtin_completions(&word));
        completions.extend(self.get_snippet_completions(&word));

        CompletionResponse::Array(completions)
    }

    /// Provide completion with import resolution support.
    pub async fn provide_completion_with_imports(
        &self,
        uri: &str,
        content: &str,
        position: Position,
        import_resolution: &crate::import_resolution::ImportResolutionService,
    ) -> CompletionResponse {
        let mut completions = self.provide_completion(uri, content, position).await;

        // Get completions from imported modules
        let imported_completions = self
            .get_imported_completions(uri, position, import_resolution)
            .await;

        // Add imported completions to the list
        if let CompletionResponse::Array(ref mut items) = completions {
            items.extend(imported_completions);
        }

        completions
    }

    /// Get completions from imported modules.
    async fn get_imported_completions(
        &self,
        uri: &str,
        _position: Position,
        import_resolution: &crate::import_resolution::ImportResolutionService,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Get imported modules
        let imported_modules = import_resolution.get_imported_modules(uri).await;

        for module_uri in imported_modules {
            if let Some(module) = import_resolution.get_cached_module(&module_uri).await {
                let module_completions = self.extract_completions_from_module(&module, &module_uri);
                completions.extend(module_completions);
            }
        }

        completions
    }

    /// Extract completion items from a module.
    fn extract_completions_from_module(
        &self,
        module: &ligature_ast::Program,
        module_uri: &str,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        for declaration in &module.declarations {
            let (name, kind, detail) = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    let detail = if let Some(ref type_ann) = value_decl.type_annotation {
                        format!(": {type_ann:?}")
                    } else {
                        ": <inferred>".to_string()
                    };
                    (
                        value_decl.name.clone(),
                        CompletionItemKind::VARIABLE,
                        detail,
                    )
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    let detail = format!("type alias = {:?}", type_alias.type_);
                    (
                        type_alias.name.clone(),
                        CompletionItemKind::TYPE_PARAMETER,
                        detail,
                    )
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => (
                    type_ctor.name.clone(),
                    CompletionItemKind::CLASS,
                    "data type".to_string(),
                ),
                ligature_ast::DeclarationKind::TypeClass(type_class) => (
                    type_class.name.clone(),
                    CompletionItemKind::INTERFACE,
                    "type class".to_string(),
                ),
                _ => continue,
            };

            completions.push(CompletionItem {
                label: name.clone(),
                kind: Some(kind),
                detail: Some(detail),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("Imported from module: {module_uri}"),
                })),
                deprecated: None,
                preselect: None,
                sort_text: Some(format!("1{name}")), // Prioritize imported symbols
                filter_text: Some(name.clone()),
                insert_text: Some(name),
                insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        completions
    }

    /// Get type-aware completions based on the expected type at the current position.
    fn get_type_aware_completions(
        &self,
        program: &Program,
        prefix: &str,
        position: Position,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Try to infer the expected type at the current position
        if let Some(expected_type) = self.infer_expected_type(program, position) {
            // Filter builtins that match the expected type
            for (name, builtin) in &self.builtins {
                if name.starts_with(prefix)
                    && self.type_matches(&builtin.return_type, &expected_type)
                {
                    completions.push(CompletionItem {
                        label: name.to_string(),
                        kind: Some(CompletionItemKind::FUNCTION),
                        detail: Some(builtin.signature.clone()),
                        documentation: Some(lsp_types::Documentation::MarkupContent(
                            MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: builtin.documentation.clone(),
                            },
                        )),
                        insert_text: Some(name.to_string()),
                        insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                        sort_text: Some(format!("1{name}")),
                        ..Default::default()
                    });
                }
            }

            // Add type-specific suggestions
            completions.extend(self.get_type_specific_suggestions(&expected_type, prefix));
        }

        completions
    }

    /// Infer the expected type at a given position.
    fn infer_expected_type(&self, _program: &Program, _position: Position) -> Option<Type> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Find the expression at the current position
        // 2. Determine the context (function argument, let binding, etc.)
        // 3. Infer the expected type from the context

        // For now, we'll return None to fall back to general completions
        None
    }

    /// Check if a type matches an expected type.
    fn type_matches(&self, actual: &str, expected: &Type) -> bool {
        // Simplified type matching
        // In a full implementation, you would do proper type unification
        match &expected.kind {
            TypeKind::Integer => actual.contains("Int"),
            TypeKind::Bool => actual.contains("Bool"),
            TypeKind::String => actual.contains("String"),
            TypeKind::List(_) => actual.contains("List"),
            _ => true, // Accept all for complex types
        }
    }

    /// Get type-specific suggestions based on the expected type.
    fn get_type_specific_suggestions(
        &self,
        expected_type: &Type,
        prefix: &str,
    ) -> Vec<CompletionItem> {
        let mut suggestions = Vec::new();

        match &expected_type.kind {
            TypeKind::Integer => {
                if prefix.is_empty() || "0".starts_with(prefix) {
                    suggestions.push(CompletionItem {
                        label: "0".to_string(),
                        kind: Some(CompletionItemKind::CONSTANT),
                        detail: Some("Int".to_string()),
                        insert_text: Some("0".to_string()),
                        insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                        sort_text: Some("0".to_string()),
                        ..Default::default()
                    });
                }
            }
            TypeKind::Bool => {
                for value in &["true", "false"] {
                    if value.starts_with(prefix) {
                        suggestions.push(CompletionItem {
                            label: value.to_string(),
                            kind: Some(CompletionItemKind::CONSTANT),
                            detail: Some("Bool".to_string()),
                            insert_text: Some(value.to_string()),
                            insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                            sort_text: Some(value.to_string()),
                            ..Default::default()
                        });
                    }
                }
            }
            TypeKind::String => {
                if prefix.is_empty() || "\"\"".starts_with(prefix) {
                    suggestions.push(CompletionItem {
                        label: "\"\"".to_string(),
                        kind: Some(CompletionItemKind::CONSTANT),
                        detail: Some("String".to_string()),
                        insert_text: Some("\"\"".to_string()),
                        insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                        sort_text: Some("\"\"".to_string()),
                        ..Default::default()
                    });
                }
            }
            TypeKind::List(_) => {
                if prefix.is_empty() || "[]".starts_with(prefix) {
                    suggestions.push(CompletionItem {
                        label: "[]".to_string(),
                        kind: Some(CompletionItemKind::CONSTANT),
                        detail: Some("List".to_string()),
                        insert_text: Some("[]".to_string()),
                        insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                        sort_text: Some("[]".to_string()),
                        ..Default::default()
                    });
                }
            }
            _ => {}
        }

        suggestions
    }

    /// Get completion items for symbols defined in the AST.
    fn get_symbol_completions(&self, program: &Program, prefix: &str) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        for decl in &program.declarations {
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name.to_lowercase().starts_with(prefix) {
                        let detail = if let Some(ref type_ann) = value_decl.type_annotation {
                            format!("{} : {:?}", value_decl.name, type_ann)
                        } else {
                            format!("{} : <inferred>", value_decl.name)
                        };

                        items.push(CompletionItem {
                            label: value_decl.name.clone(),
                            kind: Some(CompletionItemKind::VARIABLE),
                            detail: Some(detail),
                            documentation: None,
                            deprecated: None,
                            sort_text: Some(format!("2_{}", value_decl.name)),
                            filter_text: Some(value_decl.name.clone()),
                            insert_text: Some(value_decl.name.clone()),
                            insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                            text_edit: None,
                            additional_text_edits: None,
                            commit_characters: Some(vec![
                                "(".to_string(),
                                " ".to_string(),
                                ".".to_string(),
                            ]),
                            command: None,
                            data: None,
                            tags: None,

                            preselect: None,
                            insert_text_mode: None,
                            label_details: None,
                        });
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name.to_lowercase().starts_with(prefix) {
                        items.push(CompletionItem {
                            label: type_alias.name.clone(),
                            kind: Some(CompletionItemKind::TYPE_PARAMETER),
                            detail: Some(format!("type alias {}", type_alias.name)),
                            documentation: None,
                            deprecated: None,
                            sort_text: Some(format!("3_{}", type_alias.name)),
                            filter_text: Some(type_alias.name.clone()),
                            insert_text: Some(type_alias.name.clone()),
                            insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                            text_edit: None,
                            additional_text_edits: None,
                            commit_characters: Some(vec![
                                "<".to_string(),
                                " ".to_string(),
                                ".".to_string(),
                            ]),
                            command: None,
                            data: None,
                            tags: None,

                            preselect: None,
                            insert_text_mode: None,
                            label_details: None,
                        });
                    }
                }
                DeclarationKind::TypeConstructor(type_ctor) => {
                    if type_ctor.name.to_lowercase().starts_with(prefix) {
                        items.push(CompletionItem {
                            label: type_ctor.name.clone(),
                            kind: Some(CompletionItemKind::CLASS),
                            detail: Some(format!("data type {}", type_ctor.name)),
                            documentation: None,
                            deprecated: None,
                            sort_text: Some(format!("4_{}", type_ctor.name)),
                            filter_text: Some(type_ctor.name.clone()),
                            insert_text: Some(type_ctor.name.clone()),
                            insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                            text_edit: None,
                            additional_text_edits: None,
                            commit_characters: Some(vec![
                                "(".to_string(),
                                " ".to_string(),
                                ".".to_string(),
                            ]),
                            command: None,
                            data: None,
                            tags: None,

                            preselect: None,
                            insert_text_mode: None,
                            label_details: None,
                        });
                    }
                }
                _ => {}
            }
        }

        items
    }

    /// Get completion items for keywords.
    fn get_keyword_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut items = Vec::new();
        for (keyword, documentation) in &self.keywords {
            if keyword.to_lowercase().starts_with(prefix) {
                items.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some(format!("keyword: {keyword}")),
                    documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: documentation.to_string(),
                    })),
                    deprecated: None,
                    sort_text: Some(format!("0_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,

                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }
        items
    }

    /// Get completion items for built-in functions.
    fn get_builtin_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut items = Vec::new();
        for (name, builtin) in &self.builtins {
            if name.to_lowercase().starts_with(prefix) {
                items.push(CompletionItem {
                    label: name.to_string(),
                    kind: Some(CompletionItemKind::FUNCTION),
                    detail: Some(builtin.signature.clone()),
                    documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: format!("**{}**\n\n{}", builtin.signature, builtin.documentation),
                    })),
                    deprecated: None,
                    sort_text: Some(format!("1_{name}")),
                    filter_text: Some(name.to_string()),
                    insert_text: Some(format!("{}({})", name, builtin.parameters.join(", "))),
                    insert_text_format: Some(InsertTextFormat::SNIPPET),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: Some(vec!["(".to_string(), " ".to_string()]),
                    command: None,
                    data: None,
                    tags: None,

                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }
        items
    }

    /// Get snippet completions for common patterns.
    fn get_snippet_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut items = Vec::new();

        // Function definition snippet
        if "fun".starts_with(prefix) || "function".starts_with(prefix) {
            items.push(CompletionItem {
                label: "function".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Function definition".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a function definition".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_function".to_string()),
                filter_text: Some("function".to_string()),
                insert_text: Some("fun ${1:name} (${2:param}) : ${3:Type} = ${4:body}".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Let binding snippet
        if "let".starts_with(prefix) {
            items.push(CompletionItem {
                label: "let".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Let binding".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a let binding".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_let".to_string()),
                filter_text: Some("let".to_string()),
                insert_text: Some("let ${1:name} = ${2:value} in ${3:body}".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Match expression snippet
        if "match".starts_with(prefix) {
            items.push(CompletionItem {
                label: "match".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Match expression".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a match expression for pattern matching".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_match".to_string()),
                filter_text: Some("match".to_string()),
                insert_text: Some(
                    "match ${1:expression} of\n  ${2:pattern} => ${3:result}\n  ${4:_} => \
                     ${5:default}"
                        .to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Case expression snippet
        if "case".starts_with(prefix) {
            items.push(CompletionItem {
                label: "case".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Case expression".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a case expression for pattern matching".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_case".to_string()),
                filter_text: Some("case".to_string()),
                insert_text: Some(
                    "case ${1:expression} of\n  ${2:pattern} => ${3:result}\n  ${4:_} => \
                     ${5:default}"
                        .to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Type definition snippet
        if "type".starts_with(prefix) {
            items.push(CompletionItem {
                label: "type".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Type alias".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a type alias".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_type".to_string()),
                filter_text: Some("type".to_string()),
                insert_text: Some("type ${1:Name} = ${2:Type}".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Module definition snippet
        if "module".starts_with(prefix) {
            items.push(CompletionItem {
                label: "module".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Module definition".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a module definition".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_module".to_string()),
                filter_text: Some("module".to_string()),
                insert_text: Some(
                    "module ${1:ModuleName} {\n  ${2:// declarations}\n}".to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Pattern guard snippet
        if "when".starts_with(prefix) {
            items.push(CompletionItem {
                label: "when".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Pattern guard".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Add a pattern guard condition".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_when".to_string()),
                filter_text: Some("when".to_string()),
                insert_text: Some("when ${1:condition}".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Import snippet
        if "import".starts_with(prefix) {
            items.push(CompletionItem {
                label: "import".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Import statement".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Import from a module".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_import".to_string()),
                filter_text: Some("import".to_string()),
                insert_text: Some("import ${1:ModuleName};".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        // Export snippet
        if "export".starts_with(prefix) {
            items.push(CompletionItem {
                label: "export".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Export statement".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Export items from module".to_string(),
                })),
                deprecated: None,
                sort_text: Some("5_export".to_string()),
                filter_text: Some("export".to_string()),
                insert_text: Some("export { ${1:item1}, ${2:item2} };".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,

                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        items
    }

    /// Get the word at a specific position in the content.
    fn get_word_at_position(&self, content: &str, position: Position) -> String {
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
}

impl Default for CompletionProvider {
    fn default() -> Self {
        Self::new()
    }
}
