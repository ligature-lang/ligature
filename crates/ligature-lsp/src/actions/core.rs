//! Core code actions provider implementation.

use std::collections::HashMap;

use ligature_ast::Program;
use lsp_types::{CodeAction, CodeActionContext, CodeActionOrCommand, Range};

use super::code_generation::CodeGenerationActions;
use super::config::CodeActionsConfig;
use super::evaluation::EvaluationActions;
use super::performance_style::PerformanceStyleActions;
use super::quick_fixes::QuickFixes;
use super::refactoring::RefactoringActions;
use super::source_actions::SourceActions;
use super::type_aware::TypeAwareFixes;
use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};

/// Enhanced provider for code actions and quick fixes.
pub struct CodeActionsProvider {
    /// Cache of code actions by document URI.
    actions_cache: HashMap<String, Vec<CodeAction>>,
    /// Configuration for code actions.
    config: CodeActionsConfig,
    /// Async evaluation service for evaluation-based code actions.
    async_evaluation: Option<AsyncEvaluationService>,
    /// Quick fixes handler.
    quick_fixes: QuickFixes,
    /// Type-aware fixes handler.
    type_aware_fixes: TypeAwareFixes,
    /// Refactoring actions handler.
    refactoring_actions: RefactoringActions,
    /// Code generation actions handler.
    code_generation_actions: CodeGenerationActions,
    /// Performance and style actions handler.
    performance_style_actions: PerformanceStyleActions,
    /// Evaluation actions handler.
    evaluation_actions: EvaluationActions,
    /// Source actions handler.
    source_actions: SourceActions,
}

impl CodeActionsProvider {
    /// Create a new enhanced code actions provider.
    pub fn new() -> Self {
        Self {
            actions_cache: HashMap::new(),
            config: CodeActionsConfig::default(),
            async_evaluation: None,
            quick_fixes: QuickFixes::new(),
            type_aware_fixes: TypeAwareFixes::new(),
            refactoring_actions: RefactoringActions::new(),
            code_generation_actions: CodeGenerationActions::new(),
            performance_style_actions: PerformanceStyleActions::new(),
            evaluation_actions: EvaluationActions::new(),
            source_actions: SourceActions::new(),
        }
    }

    /// Create a new code actions provider with custom configuration.
    pub fn with_config(config: CodeActionsConfig) -> Self {
        Self {
            actions_cache: HashMap::new(),
            config,
            async_evaluation: None,
            quick_fixes: QuickFixes::new(),
            type_aware_fixes: TypeAwareFixes::new(),
            refactoring_actions: RefactoringActions::new(),
            code_generation_actions: CodeGenerationActions::new(),
            performance_style_actions: PerformanceStyleActions::new(),
            evaluation_actions: EvaluationActions::new(),
            source_actions: SourceActions::new(),
        }
    }

    /// Create a new code actions provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let mut provider = Self::new();
        provider.async_evaluation =
            AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        provider
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
                self.quick_fixes
                    .create_enhanced_quick_fix(uri, diagnostic, content, ast.as_ref())
            {
                actions.push(CodeActionOrCommand::CodeAction(quick_fix));
            }
        }

        // Add type-aware fixes
        if self.config.enable_type_aware_fixes {
            if let Some(program) = ast.as_ref() {
                actions.extend(
                    self.type_aware_fixes
                        .create_enhanced_type_aware_fixes(uri, range, content, program),
                );
            }
        }

        // Add evaluation-based code actions
        if let Some(eval_service) = &self.async_evaluation {
            if let Some(program) = ast.as_ref() {
                actions.extend(
                    self.evaluation_actions
                        .create_evaluation_based_actions(uri, range, content, program, eval_service)
                        .await,
                );
            }
        }

        // Add advanced refactoring actions
        if self.config.enable_advanced_refactoring {
            actions.extend(
                self.refactoring_actions
                    .create_advanced_refactoring_actions(uri, range, content, ast.as_ref()),
            );
        }

        // Add code generation actions
        if self.config.enable_code_generation {
            actions.extend(
                self.code_generation_actions
                    .create_enhanced_code_generation_actions(uri, range, content, ast.as_ref()),
            );
        }

        // Add performance suggestions
        if self.config.enable_performance_suggestions {
            if let Some(program) = ast.as_ref() {
                actions.extend(
                    self.performance_style_actions
                        .create_performance_suggestions(uri, range, content, program),
                );
            }
        }

        // Add style suggestions
        if self.config.enable_style_suggestions {
            actions.extend(self.performance_style_actions.create_style_suggestions(
                uri,
                range,
                content,
                ast.as_ref(),
            ));
        }

        // Add source actions
        actions.extend(self.source_actions.create_enhanced_source_actions(
            uri,
            range,
            content,
            ast.as_ref(),
        ));

        actions
    }

    /// Get code actions for a given range and context (original method).
    pub fn get_code_actions(
        &mut self,
        uri: &str,
        range: Range,
        diagnostics: &[lsp_types::Diagnostic],
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Add quick fixes for diagnostics
        for diagnostic in diagnostics {
            if let Some(quick_fix) = self
                .quick_fixes
                .create_quick_fix(uri, diagnostic, content, ast)
            {
                actions.push(CodeActionOrCommand::CodeAction(quick_fix));
            }
        }

        // Add type-aware fixes
        if let Some(program) = ast {
            actions.extend(
                self.type_aware_fixes
                    .create_type_aware_fixes(uri, range, content, program),
            );
        }

        // Add refactoring actions
        actions.extend(
            self.refactoring_actions
                .create_refactoring_actions(uri, range, content, ast),
        );

        // Add source actions
        actions.extend(
            self.source_actions
                .create_source_actions(uri, range, content, ast),
        );

        // Add code generation actions
        actions.extend(
            self.code_generation_actions
                .create_code_generation_actions(uri, range, content, ast),
        );

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

    /// Clear the cache for a document.
    pub fn clear_cache(&mut self, uri: &str) {
        self.actions_cache.remove(uri);
    }

    /// Get cached actions for a document.
    pub fn get_cached_actions(&self, uri: &str) -> Option<&Vec<CodeAction>> {
        self.actions_cache.get(uri)
    }
}

impl Default for CodeActionsProvider {
    fn default() -> Self {
        Self::new()
    }
}
