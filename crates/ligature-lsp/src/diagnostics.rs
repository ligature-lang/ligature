//! Diagnostics provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{Program, Span};
use ligature_parser::parse_program;
// use ligature_types::checker::TypeChecker;
// use ligature_types::type_check_program;
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};

/// Configuration for diagnostics provider.
#[derive(Debug, Clone)]
pub struct DiagnosticsConfig {
    /// Whether to enable type-aware diagnostics.
    pub enable_type_aware_diagnostics: bool,
    /// Whether to enable semantic diagnostics.
    pub enable_semantic_diagnostics: bool,
    /// Whether to enable style diagnostics.
    pub enable_style_diagnostics: bool,
    /// Whether to enable detailed error explanations.
    pub enable_detailed_explanations: bool,
    /// Whether to suggest fixes in error messages.
    pub enable_fix_suggestions: bool,
    /// Whether to provide related information for errors.
    pub enable_related_information: bool,
    /// Whether to categorize errors by severity.
    pub enable_error_categorization: bool,
    /// Whether to provide performance warnings.
    pub enable_performance_warnings: bool,
    /// Whether to provide style suggestions.
    pub enable_style_suggestions: bool,
    /// Whether to provide security warnings.
    pub enable_security_warnings: bool,
}

impl Default for DiagnosticsConfig {
    fn default() -> Self {
        Self {
            enable_type_aware_diagnostics: true,
            enable_semantic_diagnostics: true,
            enable_style_diagnostics: true,
            enable_detailed_explanations: true,
            enable_fix_suggestions: true,
            enable_related_information: true,
            enable_error_categorization: true,
            enable_performance_warnings: true,
            enable_style_suggestions: true,
            enable_security_warnings: true,
        }
    }
}

/// Provider for diagnostics (errors and warnings).
pub struct DiagnosticsProvider {
    /// Cache of diagnostics by document URI.
    diagnostics_cache: HashMap<String, Vec<Diagnostic>>,
    /// Type checker for type-aware diagnostics.
    #[allow(dead_code)]
    // type_checker: TypeChecker,
    /// Configuration for diagnostics.
    config: DiagnosticsConfig,
    /// Async evaluation service for evaluation-based diagnostics.
    async_evaluation: Option<AsyncEvaluationService>,
}

impl DiagnosticsProvider {
    /// Create a new diagnostics provider.
    pub fn new() -> Self {
        Self {
            diagnostics_cache: HashMap::new(),
            // type_checker: TypeChecker::new(),
            config: DiagnosticsConfig::default(),
            async_evaluation: None,
        }
    }

    /// Create a new diagnostics provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let async_evaluation = AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        Self {
            diagnostics_cache: HashMap::new(),
            // type_checker: TypeChecker::new(),
            config: DiagnosticsConfig::default(),
            async_evaluation,
        }
    }

    /// Compute diagnostics for a document.
    pub async fn compute_diagnostics(
        &mut self,
        uri: &str,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<Vec<Diagnostic>> {
        let mut diagnostics = Vec::new();

        // Parse diagnostics with enhanced error reporting
        if let Err(parse_error) = parse_program(content) {
            match parse_error {
                ligature_error::StandardError::Ligature(ligature_error) => {
                    if self.config.enable_detailed_explanations {
                        diagnostics
                            .extend(self.convert_enhanced_parse_errors(&ligature_error, uri));
                    } else {
                        diagnostics.extend(self.convert_parse_errors(&ligature_error));
                    }
                }
                _ => {
                    // Handle other standard errors as generic parse errors
                    diagnostics.push(Diagnostic {
                        range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                        severity: Some(DiagnosticSeverity::ERROR),
                        code: Some(lsp_types::NumberOrString::String("P000".to_string())),
                        code_description: None,
                        source: Some("ligature-parser".to_string()),
                        message: format!("Parse error: {parse_error}"),
                        related_information: None,
                        tags: None,
                        data: None,
                    });
                }
            }
        }

        // Type checking diagnostics
        if let Some(program) = ast {
            diagnostics.extend(self.compute_type_diagnostics(program));

            // Evaluation-based diagnostics
            if let Some(eval_service) = &self.async_evaluation {
                diagnostics.extend(
                    self.compute_evaluation_diagnostics(program, eval_service)
                        .await,
                );
            }
        }

        // Additional semantic checks
        diagnostics.extend(self.check_semantic_issues(content));

        // Cache the diagnostics
        self.diagnostics_cache
            .insert(uri.to_string(), diagnostics.clone());

        Some(diagnostics)
    }

    /// Compute type checking diagnostics.
    fn compute_type_diagnostics(&mut self, program: &Program) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Type check the program
        // if let Err(type_error) = type_check_program(program) {
        //     diagnostics.extend(self.convert_type_errors(&type_error));
        // }

        // Additional type-aware checks
        diagnostics.extend(self.check_type_specific_issues(program));

        diagnostics
    }

    /// Compute evaluation-based diagnostics.
    async fn compute_evaluation_diagnostics(
        &self,
        program: &Program,
        eval_service: &AsyncEvaluationService,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Try to evaluate the program to catch runtime errors
        match eval_service.evaluate_program(program, None).await {
            Ok(result) => {
                if !result.success {
                    if let Some(error) = result.error {
                        diagnostics.push(Diagnostic {
                            range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                            severity: Some(DiagnosticSeverity::ERROR),
                            code: Some(lsp_types::NumberOrString::String("E000".to_string())),
                            code_description: None,
                            source: Some("ligature-eval".to_string()),
                            message: format!("Evaluation error: {error}"),
                            related_information: None,
                            tags: None,
                            data: None,
                        });
                    }
                } else {
                    // Add performance warnings for slow evaluations
                    if result.evaluation_time.as_millis() > 100 {
                        diagnostics.push(Diagnostic {
                            range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                            severity: Some(DiagnosticSeverity::WARNING),
                            code: Some(lsp_types::NumberOrString::String("P000".to_string())),
                            code_description: None,
                            source: Some("ligature-eval".to_string()),
                            message: format!(
                                "Slow evaluation: {}ms (consider optimizing)",
                                result.evaluation_time.as_millis()
                            ),
                            related_information: None,
                            tags: None,
                            data: None,
                        });
                    }

                    // Add cache performance information
                    if result.metrics.cache_hit_rate() < 0.8 {
                        diagnostics.push(Diagnostic {
                            range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                            severity: Some(DiagnosticSeverity::INFORMATION),
                            code: Some(lsp_types::NumberOrString::String("C000".to_string())),
                            code_description: None,
                            source: Some("ligature-eval".to_string()),
                            message: format!(
                                "Low cache hit rate: {:.1}% (consider caching strategies)",
                                result.metrics.cache_hit_rate() * 100.0
                            ),
                            related_information: None,
                            tags: None,
                            data: None,
                        });
                    }
                }
            }
            Err(e) => {
                diagnostics.push(Diagnostic {
                    range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E001".to_string())),
                    code_description: None,
                    source: Some("ligature-eval".to_string()),
                    message: format!("Evaluation service error: {e}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Convert type errors to LSP diagnostics.
    #[allow(dead_code)]
    fn convert_type_errors(&self, error: &ligature_ast::AstError) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        match error {
            ligature_ast::AstError::MethodTypeMismatch {
                method,
                expected,
                found,
                span,
                ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T001".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!(
                        "Type mismatch in method {method}: expected {expected:?}, got {found:?}"
                    ),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UndefinedIdentifier { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T002".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Undefined identifier: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::DuplicateIdentifier { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T003".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Duplicate identifier: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidTypeAnnotation { span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T004".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: "Invalid type annotation".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            _ => {
                // Handle other type errors
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(Span::default()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T999".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Type error: {error:?}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check for type-specific issues.
    fn check_type_specific_issues(&self, program: &Program) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for unused variables
        diagnostics.extend(self.check_unused_variables(program));

        // Check for potential type issues
        diagnostics.extend(self.check_potential_type_issues(program));

        diagnostics
    }

    /// Check for unused variables.
    fn check_unused_variables(&self, _program: &Program) -> Vec<Diagnostic> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Track variable usage across the program
        // 2. Identify variables that are declared but never used
        // 3. Generate warnings for unused variables

        Vec::new()
    }

    /// Check for potential type issues.
    fn check_potential_type_issues(&self, _program: &Program) -> Vec<Diagnostic> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Analyze patterns for potential type mismatches
        // 2. Check for common type-related issues
        // 3. Generate warnings for potential problems

        Vec::new()
    }

    /// Convert parse errors to LSP diagnostics.
    fn convert_parse_errors(&self, error: &ligature_ast::AstError) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        match error {
            ligature_ast::AstError::Parse { message, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E001".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: message.clone(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidIdentifier { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E002".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Invalid identifier: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::DuplicateIdentifier { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E003".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Duplicate identifier: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UndefinedIdentifier { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E004".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Undefined identifier: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidImportPath { path, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E005".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Invalid import path: {path}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::ModuleNotFound { module, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E006".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Module not found: {module}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::ImportCycle { path, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E007".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Import cycle detected: {path}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            // Type class system errors
            ligature_ast::AstError::DuplicateTypeClass { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E008".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Duplicate type class: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UndefinedTypeClass { name, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E009".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Undefined type class: {name}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UnusedTypeParameter {
                parameter, span, ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::WARNING),
                    code: Some(lsp_types::NumberOrString::String("E010".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Unused type parameter: {parameter}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::TypeArgumentMismatch {
                expected,
                found,
                span,
                ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E011".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Type argument mismatch: expected {expected}, found {found}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::MissingMethod {
                method,
                class,
                span,
                ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E012".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Missing method: {method} in class {class}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UndefinedMethod {
                method,
                class,
                span,
                ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E013".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Undefined method: {method} in class {class}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::MethodTypeMismatch {
                method,
                expected,
                found,
                span,
                ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E014".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!(
                        "Method type mismatch: {method}, expected {expected:?}, found {found:?}"
                    ),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::NoInstanceFound {
                class, type_, span, ..
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E015".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("No instance found for type {type_:?} in class {class}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidTypeAnnotation { span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E005".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: "Invalid type annotation".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidExpression { span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E006".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: "Invalid expression".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::InvalidDeclaration { span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E007".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: "Invalid declaration".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::CircularDependency { span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E008".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: "Circular dependency detected".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }

            ligature_ast::AstError::InternalError { message, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("E011".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Internal error: {message}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            // Handle new error types
            ligature_ast::AstError::Type { message, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("T001".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: format!("Type error: {message}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::Evaluation { message, span, .. } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(span.clone()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("R001".to_string())),
                    code_description: None,
                    source: Some("ligature-eval".to_string()),
                    message: format!("Evaluation error: {message}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::Module { message, .. } => {
                diagnostics.push(Diagnostic {
                    range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("M001".to_string())),
                    code_description: None,
                    source: Some("ligature-module".to_string()),
                    message: format!("Module error: {message}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::Configuration { message, .. } => {
                diagnostics.push(Diagnostic {
                    range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(lsp_types::NumberOrString::String("C001".to_string())),
                    code_description: None,
                    source: Some("ligature-config".to_string()),
                    message: format!("Configuration error: {message}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check for semantic issues in the code.
    fn check_semantic_issues(&self, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Check for common issues
        for (line_num, line) in lines.iter().enumerate() {
            let line_num = line_num + 1; // Convert to 1-indexed

            // Check for unused imports (basic heuristic)
            if line.trim().starts_with("import") && !self.is_import_used(line, content) {
                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32 - 1,
                            character: 0,
                        },
                        end: Position {
                            line: line_num as u32 - 1,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::WARNING),
                    code: Some(lsp_types::NumberOrString::String("W001".to_string())),
                    code_description: None,
                    source: Some("ligature-lsp".to_string()),
                    message: "Unused import".to_string(),
                    related_information: None,
                    tags: Some(vec![lsp_types::DiagnosticTag::UNNECESSARY]),
                    data: None,
                });
            }

            // Check for long lines
            if line.len() > 100 {
                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32 - 1,
                            character: 100,
                        },
                        end: Position {
                            line: line_num as u32 - 1,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(lsp_types::NumberOrString::String("I001".to_string())),
                    code_description: None,
                    source: Some("ligature-lsp".to_string()),
                    message: "Line is longer than 100 characters".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }

            // Check for trailing whitespace
            if line.ends_with(' ') || line.ends_with('\t') {
                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32 - 1,
                            character: line.trim_end().len() as u32,
                        },
                        end: Position {
                            line: line_num as u32 - 1,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(lsp_types::NumberOrString::String("I002".to_string())),
                    code_description: None,
                    source: Some("ligature-lsp".to_string()),
                    message: "Trailing whitespace".to_string(),
                    related_information: None,
                    tags: Some(vec![lsp_types::DiagnosticTag::UNNECESSARY]),
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check if an import is used in the content.
    fn is_import_used(&self, import_line: &str, content: &str) -> bool {
        // Extract the module name from the import
        if let Some(module_name) = import_line.split_whitespace().nth(1) {
            // Simple heuristic: check if the module name appears elsewhere in the content
            let occurrences = content.matches(module_name).count();
            occurrences > 1 // More than just the import line itself
        } else {
            false
        }
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

    /// Get cached diagnostics for a document.
    pub fn get_cached_diagnostics(&self, uri: &str) -> Option<&Vec<Diagnostic>> {
        self.diagnostics_cache.get(uri)
    }

    /// Clear diagnostics for a document.
    pub fn clear_diagnostics(&mut self, uri: &str) {
        self.diagnostics_cache.remove(uri);
    }

    /// Convert enhanced parse errors with detailed explanations.
    fn convert_enhanced_parse_errors(
        &self,
        error: &ligature_ast::AstError,
        uri: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let range = if let Some(span) = error.span() {
            self.span_to_range(span.clone())
        } else {
            Range::new(Position::new(0, 0), Position::new(0, 0))
        };

        let mut message = error.to_string();
        let mut code = "P001".to_string();

        // Add detailed explanations and fix suggestions
        if self.config.enable_detailed_explanations {
            match error {
                ligature_ast::AstError::Parse {
                    code: error_code,
                    message: error_msg,
                    suggestions,
                    ..
                } => {
                    code = error_code.as_str().to_string();
                    message = error_msg.clone();
                    if self.config.enable_fix_suggestions && !suggestions.is_empty() {
                        message = format!("{} Suggestions: {}", message, suggestions.join(", "));
                    }
                }
                ligature_ast::AstError::Type {
                    code: error_code,
                    message: error_msg,
                    expected,
                    found,
                    suggestions,
                    ..
                } => {
                    code = error_code.as_str().to_string();
                    message = error_msg.clone();
                    if let (Some(expected_type), Some(found_type)) = (expected, found) {
                        message =
                            format!("{message} Expected: {expected_type}, Found: {found_type}");
                    }
                    if self.config.enable_fix_suggestions && !suggestions.is_empty() {
                        message = format!("{} Suggestions: {}", message, suggestions.join(", "));
                    }
                }
                ligature_ast::AstError::InvalidIdentifier {
                    code: error_code,
                    name,
                    ..
                } => {
                    code = error_code.as_str().to_string();
                    message = format!(
                        "Invalid identifier '{name}'. Identifiers must start with a letter or \
                         underscore and contain only letters, digits, and underscores."
                    );
                    if self.config.enable_fix_suggestions {
                        if let Some(suggestion) = self.suggest_identifier_fix(name) {
                            message = format!("{message} Suggestion: {suggestion}");
                        }
                    }
                }
                ligature_ast::AstError::DuplicateIdentifier {
                    code: error_code,
                    name,
                    ..
                } => {
                    code = error_code.as_str().to_string();
                    message = format!(
                        "Duplicate declaration of '{name}'. Each identifier must be declared only \
                         once in its scope."
                    );
                }
                ligature_ast::AstError::UndefinedIdentifier {
                    code: error_code,
                    name,
                    ..
                } => {
                    code = error_code.as_str().to_string();
                    message = format!(
                        "Undefined variable '{name}'. Make sure the variable is declared before \
                         use."
                    );
                }
                _ => {
                    code = "P008".to_string();
                    message = error.to_string();
                }
            }
        }

        // Add related information if enabled
        let related_information = if self.config.enable_related_information {
            self.get_related_information_for_parse_error(error, uri)
        } else {
            None
        };

        // Determine severity based on error categorization
        let severity = if self.config.enable_error_categorization {
            match error {
                ligature_ast::AstError::Parse { .. } => DiagnosticSeverity::ERROR,
                ligature_ast::AstError::Type { .. } => DiagnosticSeverity::ERROR,
                ligature_ast::AstError::InvalidIdentifier { .. } => DiagnosticSeverity::ERROR,
                ligature_ast::AstError::DuplicateIdentifier { .. } => DiagnosticSeverity::ERROR,
                ligature_ast::AstError::UndefinedIdentifier { .. } => DiagnosticSeverity::WARNING,
                _ => DiagnosticSeverity::ERROR,
            }
        } else {
            DiagnosticSeverity::ERROR
        };

        diagnostics.push(Diagnostic {
            range,
            severity: Some(severity),
            code: Some(lsp_types::NumberOrString::String(code)),
            code_description: None,
            source: Some("ligature-parser".to_string()),
            message,
            related_information,
            tags: None,
            data: None,
        });

        diagnostics
    }

    #[allow(dead_code)]
    fn check_security_issues(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for hardcoded passwords
        if content.contains("password") && content.contains("=") {
            diagnostics.push(Diagnostic {
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
                severity: Some(DiagnosticSeverity::WARNING),
                code: Some(lsp_types::NumberOrString::String("S001".to_string())),
                code_description: None,
                source: Some("ligature-security".to_string()),
                message: "Potential hardcoded password detected".to_string(),
                related_information: None,
                tags: None,
                data: None,
            });
        }

        // Check for potential SQL injection patterns
        if content.contains("SELECT") && content.contains("${") {
            diagnostics.push(Diagnostic {
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
                severity: Some(DiagnosticSeverity::WARNING),
                code: Some(lsp_types::NumberOrString::String("S002".to_string())),
                code_description: None,
                source: Some("ligature-security".to_string()),
                message: "Potential SQL injection pattern detected".to_string(),
                related_information: None,
                tags: None,
                data: None,
            });
        }

        diagnostics
    }

    #[allow(dead_code)]
    fn check_performance_issues(&self, _program: &Program, _uri: &str) -> Vec<Diagnostic> {
        // Placeholder for performance checks
        Vec::new()
    }

    #[allow(dead_code)]
    fn check_style_issues(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for long lines
        for (line_num, line) in content.lines().enumerate() {
            if line.len() > 100 {
                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32,
                            character: 0,
                        },
                        end: Position {
                            line: line_num as u32,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(lsp_types::NumberOrString::String("ST001".to_string())),
                    code_description: None,
                    source: Some("ligature-style".to_string()),
                    message: "Line is too long (consider breaking it)".to_string(),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    #[allow(dead_code)]
    fn suggest_token_fix(&self, token: &str) -> Option<String> {
        // Simple token suggestions
        match token {
            "fucntion" => Some("function".to_string()),
            "retrun" => Some("return".to_string()),
            "improt" => Some("import".to_string()),
            "exprot" => Some("export".to_string()),
            _ => None,
        }
    }

    #[allow(dead_code)]
    fn suggest_type_fix(&self, expected: &str, found: &str) -> Option<String> {
        // Type conversion suggestions
        match (expected, found) {
            ("Int", "String") => Some("parseInt".to_string()),
            ("String", "Int") => Some("toString".to_string()),
            _ => None,
        }
    }

    /// Suggest identifier fixes.
    fn suggest_identifier_fix(&self, name: &str) -> Option<String> {
        if name.chars().next().is_some_and(|c| c.is_numeric()) {
            Some(
                "Identifiers cannot start with a number. Add a letter or underscore prefix."
                    .to_string(),
            )
        } else if name.contains('-') {
            Some("Identifiers cannot contain hyphens. Use underscores instead.".to_string())
        } else {
            None
        }
    }

    /// Get related information for parse errors.
    fn get_related_information_for_parse_error(
        &self,
        error: &ligature_ast::AstError,
        uri: &str,
    ) -> Option<Vec<lsp_types::DiagnosticRelatedInformation>> {
        // This would provide links to related documentation or examples
        let mut related = Vec::new();

        // Add suggestions from the error if available
        for suggestion in error.get_suggestions() {
            related.push(lsp_types::DiagnosticRelatedInformation {
                location: lsp_types::Location {
                    uri: lsp_types::Url::parse(uri).ok()?,
                    range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                },
                message: suggestion,
            });
        }

        if related.is_empty() {
            None
        } else {
            Some(related)
        }
    }

    /// Update configuration.
    pub fn update_config(&mut self, config: DiagnosticsConfig) {
        self.config = config;
    }
}

impl Default for DiagnosticsProvider {
    fn default() -> Self {
        Self::new()
    }
}
