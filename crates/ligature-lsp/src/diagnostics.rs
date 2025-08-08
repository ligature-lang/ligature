//! Diagnostics provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{Program, Span};
use ligature_parser::parse_program;
use ligature_types::checker::TypeChecker;
use ligature_types::type_check_program;
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

/// Provider for diagnostics (errors and warnings).
pub struct DiagnosticsProvider {
    /// Cache of diagnostics by document URI.
    diagnostics_cache: HashMap<String, Vec<Diagnostic>>,
    /// Type checker for type-aware diagnostics.
    #[allow(dead_code)]
    type_checker: TypeChecker,
}

impl DiagnosticsProvider {
    /// Create a new diagnostics provider.
    pub fn new() -> Self {
        Self {
            diagnostics_cache: HashMap::new(),
            type_checker: TypeChecker::new(),
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

        // Parse diagnostics
        if let Err(parse_error) = parse_program(content) {
            diagnostics.extend(self.convert_parse_errors(&parse_error));
        }

        // Type checking diagnostics
        if let Some(program) = ast {
            diagnostics.extend(self.compute_type_diagnostics(program));
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
        if let Err(type_error) = type_check_program(program) {
            diagnostics.extend(self.convert_type_errors(&type_error));
        }

        // Additional type-aware checks
        diagnostics.extend(self.check_type_specific_issues(program));

        diagnostics
    }

    /// Convert type errors to LSP diagnostics.
    fn convert_type_errors(&self, error: &ligature_ast::AstError) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        match error {
            ligature_ast::AstError::MethodTypeMismatch {
                method,
                expected,
                found,
                span,
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::UndefinedIdentifier { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::DuplicateIdentifier { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidTypeAnnotation { span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::ParseError { message, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidIdentifier { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::DuplicateIdentifier { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::UndefinedIdentifier { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidImportPath { path, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::ModuleNotFound { module, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::ImportCycle { path, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::DuplicateTypeClass { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::UndefinedTypeClass { name, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::UnusedTypeParameter { parameter, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::NoInstanceFound { class, type_, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidTypeAnnotation { span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidExpression { span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::InvalidDeclaration { span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
            ligature_ast::AstError::CircularDependency { span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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

            ligature_ast::AstError::InternalError { message, span } => {
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
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
}

impl Default for DiagnosticsProvider {
    fn default() -> Self {
        Self::new()
    }
}
