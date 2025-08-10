//! Source-level actions like import organization.

use ligature_ast::Program;
use lsp_types::{CodeAction, CodeActionKind, CodeActionOrCommand, Command, Range};

/// Handler for source-level actions.
pub struct SourceActions;

impl SourceActions {
    /// Create a new source actions handler.
    pub fn new() -> Self {
        Self
    }

    /// Create source actions.
    pub fn create_source_actions(
        &self,
        uri: &str,
        _range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let actions = vec![
            CodeActionOrCommand::CodeAction(CodeAction {
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
            }),
            CodeActionOrCommand::CodeAction(CodeAction {
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
            }),
        ];

        actions
    }

    /// Create enhanced source actions.
    pub fn create_enhanced_source_actions(
        &self,
        uri: &str,
        _range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let actions = vec![
            CodeActionOrCommand::CodeAction(CodeAction {
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
            }),
            CodeActionOrCommand::CodeAction(CodeAction {
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
            }),
            CodeActionOrCommand::CodeAction(CodeAction {
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
            }),
        ];

        actions
    }
}

impl Default for SourceActions {
    fn default() -> Self {
        Self::new()
    }
}
