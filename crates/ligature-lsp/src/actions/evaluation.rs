//! Evaluation-based code actions.

use std::collections::HashMap;

use ligature_ast::Program;
use lsp_types::{CodeAction, CodeActionKind, CodeActionOrCommand, Range, WorkspaceEdit};

use crate::async_evaluation::AsyncEvaluationService;

/// Handler for evaluation-based actions.
pub struct EvaluationActions;

impl EvaluationActions {
    /// Create a new evaluation actions handler.
    pub fn new() -> Self {
        Self
    }

    /// Create evaluation-based code actions.
    pub async fn create_evaluation_based_actions(
        &self,
        _uri: &str,
        _range: Range,
        _content: &str,
        program: &Program,
        eval_service: &AsyncEvaluationService,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Try to evaluate the program to get runtime information
        match eval_service.evaluate_program(program, None).await {
            Ok(result) => {
                if result.success {
                    // Add performance optimization actions
                    if result.evaluation_time.as_millis() > 100 {
                        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                            title: "Optimize for performance".to_string(),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            is_preferred: Some(true),
                            disabled: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::new()),
                                document_changes: None,
                                change_annotations: None,
                            }),
                            command: None,
                            data: None,
                        }));
                    }

                    // Add caching suggestions
                    if result.metrics.cache_hit_rate() < 0.5 {
                        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                            title: "Add caching".to_string(),
                            kind: Some(CodeActionKind::REFACTOR),
                            diagnostics: None,
                            is_preferred: Some(false),
                            disabled: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::new()),
                                document_changes: None,
                                change_annotations: None,
                            }),
                            command: None,
                            data: None,
                        }));
                    }
                } else {
                    // Add error fix actions
                    if let Some(error) = result.error {
                        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                            title: format!("Fix evaluation error: {error}"),
                            kind: Some(CodeActionKind::QUICKFIX),
                            diagnostics: None,
                            is_preferred: Some(true),
                            disabled: None,
                            edit: Some(WorkspaceEdit {
                                changes: Some(HashMap::new()),
                                document_changes: None,
                                change_annotations: None,
                            }),
                            command: None,
                            data: None,
                        }));
                    }
                }
            }
            Err(e) => {
                // Add service error actions
                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!("Fix evaluation service error: {e}"),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    is_preferred: Some(false),
                    disabled: None,
                    edit: Some(WorkspaceEdit {
                        changes: Some(HashMap::new()),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    data: None,
                }));
            }
        }

        actions
    }
}

impl Default for EvaluationActions {
    fn default() -> Self {
        Self::new()
    }
}
