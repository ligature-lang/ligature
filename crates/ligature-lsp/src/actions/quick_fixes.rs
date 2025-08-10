//! Quick fixes for diagnostics and parse errors.

use std::collections::HashMap;

use ligature_ast::{Program, Span};
use lsp_types::{
    CodeAction, CodeActionKind, Diagnostic, Position, Range, TextEdit, Url, WorkspaceEdit,
};

/// Handler for quick fixes based on diagnostics.
pub struct QuickFixes;

impl QuickFixes {
    /// Create a new quick fixes handler.
    pub fn new() -> Self {
        Self
    }

    /// Create quick fixes for diagnostics.
    pub fn create_quick_fix(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
        _ast: Option<&Program>,
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

    /// Create enhanced quick fixes for diagnostics.
    pub fn create_enhanced_quick_fix(
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
                        if let Some((expected, actual)) =
                            self.extract_type_info(&diagnostic.message)
                        {
                            // Create a default span from the diagnostic range
                            let span = ligature_ast::Span {
                                file: None,
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
                            new_text: format!("{content};"),
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
                            new_text: format!("{content};"),
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
                    title: format!("Add missing closing {closing_char}"),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diagnostic.clone()]),
                    edit: Some(WorkspaceEdit {
                        changes: Some(HashMap::from([(
                            Url::parse(uri).unwrap_or_else(|_| Url::parse("file:///").unwrap()),
                            vec![TextEdit {
                                range: diagnostic.range,
                                new_text: format!("{content}{closing_char}"),
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

    /// Fix invalid identifier errors.
    fn fix_invalid_identifier(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        content: &str,
    ) -> Option<CodeAction> {
        let _content = content; // Suppress unused variable warning
        // Extract the invalid identifier from the error message
        if let Some(invalid_name) = diagnostic.message.strip_prefix("Invalid identifier: ") {
            // Suggest a valid identifier name
            let valid_name = self.suggest_valid_identifier(invalid_name);

            Some(CodeAction {
                title: format!("Rename to '{valid_name}'"),
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
        let _content = content; // Suppress unused variable warning
        if let Some(duplicate_name) = diagnostic.message.strip_prefix("Duplicate identifier: ") {
            // Suggest renaming the duplicate
            let new_name = format!("{duplicate_name}_new");

            Some(CodeAction {
                title: format!("Rename to '{new_name}'"),
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
        let _content = content; // Suppress unused variable warning
        diagnostic
            .message
            .strip_prefix("Undefined identifier: ")
            .map(|undefined_name| {
                // Suggest adding an import or declaration
                CodeAction {
                    title: format!("Add declaration for '{undefined_name}'"),
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
                                new_text: format!("let {undefined_name} = undefined;\n"),
                            }],
                        )])),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(false),
                    disabled: None,
                    data: None,
                }
            })
    }

    /// Fix undefined types with import suggestions.
    fn fix_undefined_type(
        &self,
        uri: &str,
        diagnostic: &Diagnostic,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Option<CodeAction> {
        let message = &diagnostic.message;

        if let Some(type_name) = message.strip_prefix("Undefined type: ") {
            // Check if this is a built-in type
            let builtin_types = ["Int", "Float", "String", "Bool", "List", "Unit"];
            if builtin_types.contains(&type_name) {
                Some(CodeAction {
                    title: format!("Import built-in type '{type_name}'"),
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
                                new_text: format!("import {type_name} from \"stdlib/core\";\n"),
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
                    title: format!("Create type definition for '{type_name}'"),
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
                                new_text: format!("type {type_name} = $1;\n"),
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

    /// Fix type mismatches by suggesting appropriate conversions or corrections.
    fn fix_type_mismatch(
        &self,
        uri: &str,
        expected: &str,
        actual: &str,
        span: Span,
        _content: &str,
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

    // Helper methods

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
            valid_name = format!("_{valid_name}");
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
            if current_line.len() + word.len() < width {
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
}

impl Default for QuickFixes {
    fn default() -> Self {
        Self::new()
    }
}
