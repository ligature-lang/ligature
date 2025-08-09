//! Enhanced completion provider for the Ligature LSP server with improved IDE integration.

use std::collections::HashMap;

use ligature_ast::{Program, Type};
// use ligature_types::checker::TypeChecker;
use lsp_types::{
    CompletionContext, CompletionItem, CompletionItemKind, CompletionResponse, InsertTextFormat,
    MarkupContent, MarkupKind, Position,
};

/// Enhanced provider for code completion suggestions with improved IDE integration.
pub struct EnhancedCompletionProvider {
    /// Built-in keywords and their documentation.
    keywords: HashMap<&'static str, &'static str>,
    /// Built-in functions and their signatures.
    builtins: HashMap<&'static str, EnhancedBuiltinFunction>,
    /// Type checker for type-aware completions.
    #[allow(dead_code)]
    // type_checker: TypeChecker,
    /// Configuration for enhanced completions.
    config: EnhancedCompletionConfig,
    /// Context-aware snippets.
    #[allow(dead_code)]
    context_snippets: HashMap<String, Vec<CompletionItem>>,
}

/// Enhanced information about a built-in function.
#[derive(Debug, Clone)]
struct EnhancedBuiltinFunction {
    signature: String,
    documentation: String,
    #[allow(dead_code)]
    parameters: Vec<String>,
    #[allow(dead_code)]
    return_type: String,
    examples: Vec<String>,
    #[allow(dead_code)]
    category: String,
}

/// Configuration for enhanced completions.
#[derive(Debug, Clone)]
pub struct EnhancedCompletionConfig {
    /// Whether to enable context-aware completions.
    pub enable_context_aware: bool,
    /// Whether to enable type-aware completions.
    pub enable_type_aware: bool,
    /// Whether to enable snippet completions.
    pub enable_snippets: bool,
    /// Whether to enable documentation in completions.
    pub enable_documentation: bool,
    /// Whether to enable examples in completions.
    pub enable_examples: bool,
    /// Whether to enable fuzzy matching.
    pub enable_fuzzy_matching: bool,
    /// Whether to enable auto-import suggestions.
    pub enable_auto_import: bool,
}

impl Default for EnhancedCompletionConfig {
    fn default() -> Self {
        Self {
            enable_context_aware: true,
            enable_type_aware: true,
            enable_snippets: true,
            enable_documentation: true,
            enable_examples: true,
            enable_fuzzy_matching: true,
            enable_auto_import: true,
        }
    }
}

impl EnhancedCompletionProvider {
    /// Create a new enhanced completion provider.
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
            EnhancedBuiltinFunction {
                signature: "add : Int -> Int -> Int".to_string(),
                documentation: "Add two integers together".to_string(),
                parameters: vec!["a".to_string(), "b".to_string()],
                return_type: "Int".to_string(),
                examples: vec!["add 5 3".to_string(), "let result = add x y".to_string()],
                category: "arithmetic".to_string(),
            },
        );

        let mut context_snippets = HashMap::new();
        context_snippets.insert("function".to_string(), Self::create_function_snippets());
        context_snippets.insert("type".to_string(), Self::create_type_snippets());
        context_snippets.insert("pattern".to_string(), Self::create_pattern_snippets());

        Self {
            keywords,
            builtins,
            // type_checker: TypeChecker::new(),
            config: EnhancedCompletionConfig::default(),
            context_snippets,
        }
    }

    /// Create a new enhanced completion provider with custom configuration.
    pub fn with_config(config: EnhancedCompletionConfig) -> Self {
        let mut provider = Self::new();
        provider.config = config;
        provider
    }

    /// Provide enhanced completions with context awareness.
    pub async fn provide_enhanced_completion(
        &self,
        _uri: &str,
        content: &str,
        position: Position,
        _context: Option<CompletionContext>,
    ) -> CompletionResponse {
        let prefix = self.get_word_at_position(content, position);
        let mut completions = Vec::new();

        // Get context-aware completions
        if self.config.enable_context_aware {
            completions.extend(self.get_context_aware_completions(content, position, &prefix));
        }

        // Get type-aware completions
        if self.config.enable_type_aware {
            if let Ok(program) = ligature_parser::parse_program(content) {
                completions
                    .extend(self.get_enhanced_type_aware_completions(&program, &prefix, position));
            }
        }

        // Get symbol completions
        completions.extend(self.get_enhanced_symbol_completions(content, &prefix));

        // Get keyword completions
        completions.extend(self.get_enhanced_keyword_completions(&prefix));

        // Get builtin completions
        completions.extend(self.get_enhanced_builtin_completions(&prefix));

        // Get snippet completions
        if self.config.enable_snippets {
            completions.extend(self.get_enhanced_snippet_completions(&prefix, content, position));
        }

        // Get auto-import suggestions
        if self.config.enable_auto_import {
            completions.extend(self.get_auto_import_suggestions(&prefix, content));
        }

        // Sort and deduplicate completions
        completions.sort_by(|a, b| {
            // Prioritize exact matches
            let a_exact = a.label.starts_with(&prefix);
            let b_exact = b.label.starts_with(&prefix);
            if a_exact != b_exact {
                return b_exact.cmp(&a_exact);
            }
            // Then by label
            a.label.cmp(&b.label)
        });

        // Remove duplicates
        completions.dedup_by(|a, b| a.label == b.label);

        CompletionResponse::Array(completions)
    }

    /// Get context-aware completions based on the current position and surrounding code.
    fn get_context_aware_completions(
        &self,
        content: &str,
        position: Position,
        prefix: &str,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let current_line = lines.get(position.line as usize).unwrap_or(&"");

        // Check if we're in a function definition
        if current_line.trim().starts_with("fun ") || current_line.contains("->") {
            completions.extend(self.get_function_context_completions(prefix));
        }

        // Check if we're in a type definition
        if current_line.trim().starts_with("type ") || current_line.contains("=") {
            completions.extend(self.get_type_context_completions(prefix));
        }

        // Check if we're in a pattern match
        if current_line.trim().starts_with("match ") || current_line.contains("=>") {
            completions.extend(self.get_pattern_context_completions(prefix));
        }

        // Check if we're in an import statement
        if current_line.trim().starts_with("import ") {
            completions.extend(self.get_import_context_completions(prefix));
        }

        completions
    }

    /// Get enhanced type-aware completions.
    fn get_enhanced_type_aware_completions(
        &self,
        program: &Program,
        prefix: &str,
        position: Position,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Try to infer the expected type at the current position
        if let Some(expected_type) = self.infer_expected_type(program, position) {
            completions.extend(self.get_type_specific_suggestions(&expected_type, prefix));
        }

        // Get completions for declared symbols
        completions.extend(self.get_symbol_completions(program, prefix));

        completions
    }

    /// Get enhanced symbol completions.
    fn get_enhanced_symbol_completions(
        &self,
        _content: &str,
        _prefix: &str,
    ) -> Vec<CompletionItem> {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to find all symbols

        Vec::new()
    }

    /// Get enhanced keyword completions.
    fn get_enhanced_keyword_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        for (keyword, documentation) in &self.keywords {
            if keyword.starts_with(prefix) || self.fuzzy_match(keyword, prefix) {
                let item = CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some(format!("Keyword: {keyword}")),
                    documentation: if self.config.enable_documentation {
                        Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: documentation.to_string(),
                        }))
                    } else {
                        None
                    },
                    sort_text: Some(format!("1_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                };

                completions.push(item);
            }
        }

        completions
    }

    /// Get enhanced builtin completions.
    fn get_enhanced_builtin_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        for (name, builtin) in &self.builtins {
            if name.starts_with(prefix) || self.fuzzy_match(name, prefix) {
                let item = CompletionItem {
                    label: name.to_string(),
                    kind: Some(CompletionItemKind::FUNCTION),
                    detail: Some(builtin.signature.clone()),
                    documentation: if self.config.enable_documentation {
                        let mut doc = builtin.documentation.clone();
                        if self.config.enable_examples && !builtin.examples.is_empty() {
                            doc.push_str("\n\n**Examples:**\n");
                            for example in &builtin.examples {
                                doc.push_str(&format!("```\n{example}\n```\n"));
                            }
                        }
                        Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: doc,
                        }))
                    } else {
                        None
                    },
                    sort_text: Some(format!("2_{name}")),
                    filter_text: Some(name.to_string()),
                    insert_text: Some(name.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                };

                completions.push(item);
            }
        }

        completions
    }

    /// Get enhanced snippet completions.
    fn get_enhanced_snippet_completions(
        &self,
        prefix: &str,
        _content: &str,
        _position: Position,
    ) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Add function snippets
        completions.extend(self.get_function_snippets(prefix));

        // Add type snippets
        completions.extend(self.get_type_snippets(prefix));

        // Add pattern matching snippets
        completions.extend(self.get_pattern_snippets(prefix));

        // Add conditional snippets
        completions.extend(self.get_conditional_snippets(prefix));

        completions
    }

    /// Get auto-import suggestions.
    fn get_auto_import_suggestions(&self, prefix: &str, content: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Check if this might be a built-in function that needs importing
        let builtins = [
            "add", "sub", "mul", "div", "eq", "lt", "gt", "concat", "length", "head", "tail",
        ];

        for builtin in &builtins {
            if builtin.starts_with(prefix) && !content.contains(&format!("import {builtin}")) {
                completions.push(CompletionItem {
                    label: format!("import {builtin}"),
                    kind: Some(CompletionItemKind::TEXT),
                    detail: Some(format!("Import {builtin} from stdlib")),
                    documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: format!(
                            "Add import statement for `{builtin}` from the standard library"
                        ),
                    })),
                    sort_text: Some(format!("3_import_{builtin}")),
                    filter_text: Some(builtin.to_string()),
                    insert_text: Some(format!("import {builtin} from \"stdlib/core\";")),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }

        completions
    }

    // Helper methods for context-specific completions

    fn get_function_context_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Add function-specific keywords
        let function_keywords = ["->", "=", "where", "let", "in"];
        for keyword in &function_keywords {
            if keyword.starts_with(prefix) {
                completions.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some("Function syntax".to_string()),
                    documentation: None,
                    sort_text: Some(format!("1_func_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }

        completions
    }

    fn get_type_context_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Add type-specific keywords
        let type_keywords = ["=", "|", "->", "where"];
        for keyword in &type_keywords {
            if keyword.starts_with(prefix) {
                completions.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some("Type syntax".to_string()),
                    documentation: None,
                    sort_text: Some(format!("1_type_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }

        completions
    }

    fn get_pattern_context_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Add pattern-specific keywords
        let pattern_keywords = ["=>", "|", "when", "where"];
        for keyword in &pattern_keywords {
            if keyword.starts_with(prefix) {
                completions.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some("Pattern matching syntax".to_string()),
                    documentation: None,
                    sort_text: Some(format!("1_pattern_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }

        completions
    }

    fn get_import_context_completions(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // Add import-specific keywords
        let import_keywords = ["from", "as", "where"];
        for keyword in &import_keywords {
            if keyword.starts_with(prefix) {
                completions.push(CompletionItem {
                    label: keyword.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    detail: Some("Import syntax".to_string()),
                    documentation: None,
                    sort_text: Some(format!("1_import_{keyword}")),
                    filter_text: Some(keyword.to_string()),
                    insert_text: Some(keyword.to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    text_edit: None,
                    additional_text_edits: None,
                    commit_characters: None,
                    command: None,
                    data: None,
                    tags: None,
                    deprecated: None,
                    preselect: None,
                    insert_text_mode: None,
                    label_details: None,
                });
            }
        }

        completions
    }

    // Snippet generation methods

    fn get_function_snippets(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        if "fun".starts_with(prefix) || "function".starts_with(prefix) {
            completions.push(CompletionItem {
                label: "fun".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Function definition".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a new function definition".to_string(),
                })),
                sort_text: Some("1_snippet_fun".to_string()),
                filter_text: Some("fun".to_string()),
                insert_text: Some(
                    "fun ${1:name}(${2:params}) : ${3:return_type} = ${4:body}".to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                deprecated: None,
                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        completions
    }

    fn get_type_snippets(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        if "type".starts_with(prefix) {
            completions.push(CompletionItem {
                label: "type".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Type definition".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a new type definition".to_string(),
                })),
                sort_text: Some("1_snippet_type".to_string()),
                filter_text: Some("type".to_string()),
                insert_text: Some("type ${1:TypeName} = ${2:definition}".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                deprecated: None,
                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        if "data".starts_with(prefix) {
            completions.push(CompletionItem {
                label: "data".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Data type definition".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a new data type with constructors".to_string(),
                })),
                sort_text: Some("1_snippet_data".to_string()),
                filter_text: Some("data".to_string()),
                insert_text: Some(
                    "data ${1:TypeName} = ${2:Constructor1} | ${3:Constructor2}".to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                deprecated: None,
                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        completions
    }

    fn get_pattern_snippets(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        if "match".starts_with(prefix) {
            completions.push(CompletionItem {
                label: "match".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Pattern matching".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a pattern matching expression".to_string(),
                })),
                sort_text: Some("1_snippet_match".to_string()),
                filter_text: Some("match".to_string()),
                insert_text: Some(
                    "match ${1:expression} of\n  ${2:pattern1} => ${3:result1}\n  ${4:pattern2} \
                     => ${5:result2}"
                        .to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                deprecated: None,
                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        completions
    }

    fn get_conditional_snippets(&self, prefix: &str) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        if "if".starts_with(prefix) {
            completions.push(CompletionItem {
                label: "if".to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                detail: Some("Conditional expression".to_string()),
                documentation: Some(lsp_types::Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "Create a conditional expression".to_string(),
                })),
                sort_text: Some("1_snippet_if".to_string()),
                filter_text: Some("if".to_string()),
                insert_text: Some(
                    "if ${1:condition} then\n  ${2:then_branch}\nelse\n  ${3:else_branch}"
                        .to_string(),
                ),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                text_edit: None,
                additional_text_edits: None,
                commit_characters: None,
                command: None,
                data: None,
                tags: None,
                deprecated: None,
                preselect: None,
                insert_text_mode: None,
                label_details: None,
            });
        }

        completions
    }

    // Static methods for creating snippet collections

    fn create_function_snippets() -> Vec<CompletionItem> {
        vec![]
    }

    fn create_type_snippets() -> Vec<CompletionItem> {
        vec![]
    }

    fn create_pattern_snippets() -> Vec<CompletionItem> {
        vec![]
    }

    // Helper methods

    fn infer_expected_type(&self, _program: &Program, _position: Position) -> Option<Type> {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to infer the expected type
        None
    }

    fn get_type_specific_suggestions(
        &self,
        _expected_type: &Type,
        _prefix: &str,
    ) -> Vec<CompletionItem> {
        // This is a simplified implementation
        // In a full implementation, you would provide type-specific suggestions
        vec![]
    }

    fn get_symbol_completions(&self, _program: &Program, _prefix: &str) -> Vec<CompletionItem> {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to find symbols
        vec![]
    }

    fn fuzzy_match(&self, text: &str, pattern: &str) -> bool {
        if !self.config.enable_fuzzy_matching {
            return false;
        }

        // Simple fuzzy matching implementation
        let text_lower = text.to_lowercase();
        let pattern_lower = pattern.to_lowercase();

        if pattern_lower.is_empty() {
            return true;
        }

        let mut pattern_chars = pattern_lower.chars().peekable();
        for ch in text_lower.chars() {
            if let Some(&pattern_ch) = pattern_chars.peek() {
                if ch == pattern_ch {
                    pattern_chars.next();
                    if pattern_chars.peek().is_none() {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn get_word_at_position(&self, content: &str, position: Position) -> String {
        let lines: Vec<&str> = content.lines().collect();
        if let Some(line) = lines.get(position.line as usize) {
            let char_pos = position.character as usize;
            if char_pos <= line.len() {
                let before_cursor = &line[..char_pos];
                let after_cursor = &line[char_pos..];

                let word_start = before_cursor
                    .rfind(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(|i| i + 1)
                    .unwrap_or(0);

                let word_end = after_cursor
                    .find(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(|i| char_pos + i)
                    .unwrap_or(line.len());

                return line[word_start..word_end].to_string();
            }
        }
        String::new()
    }

    /// Update configuration.
    pub fn update_config(&mut self, config: EnhancedCompletionConfig) {
        self.config = config;
    }
}

impl Default for EnhancedCompletionProvider {
    fn default() -> Self {
        Self::new()
    }
}
