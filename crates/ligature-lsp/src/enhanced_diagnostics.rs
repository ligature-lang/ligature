//! Enhanced diagnostics provider for the Ligature LSP server with improved error reporting.

use ligature_ast::{Program, Span};
use ligature_parser::parse_program;
use ligature_types::{checker::TypeChecker, type_check_program};
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, NumberOrString, Position, Range,
};
use std::collections::HashMap;

/// Enhanced provider for diagnostics with improved error reporting.
pub struct EnhancedDiagnosticsProvider {
    /// Cache of diagnostics by document URI.
    diagnostics_cache: HashMap<String, Vec<Diagnostic>>,
    /// Type checker for type-aware diagnostics.
    #[allow(dead_code)]
    type_checker: TypeChecker,
    /// Configuration for enhanced diagnostics.
    config: EnhancedDiagnosticsConfig,
}

/// Configuration for enhanced diagnostics.
#[derive(Debug, Clone)]
pub struct EnhancedDiagnosticsConfig {
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

impl Default for EnhancedDiagnosticsConfig {
    fn default() -> Self {
        Self {
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

impl EnhancedDiagnosticsProvider {
    /// Create a new enhanced diagnostics provider.
    pub fn new() -> Self {
        Self {
            diagnostics_cache: HashMap::new(),
            type_checker: TypeChecker::new(),
            config: EnhancedDiagnosticsConfig::default(),
        }
    }

    /// Create a new enhanced diagnostics provider with custom configuration.
    pub fn with_config(config: EnhancedDiagnosticsConfig) -> Self {
        Self {
            diagnostics_cache: HashMap::new(),
            type_checker: TypeChecker::new(),
            config,
        }
    }

    /// Compute enhanced diagnostics for a document.
    pub async fn compute_enhanced_diagnostics(
        &mut self,
        uri: &str,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<Vec<Diagnostic>> {
        let mut diagnostics = Vec::new();

        // Parse diagnostics with enhanced error reporting
        if let Err(parse_error) = parse_program(content) {
            diagnostics.extend(self.convert_enhanced_parse_errors(&parse_error, uri));
        }

        // Type checking diagnostics with detailed explanations
        if let Some(program) = ast {
            diagnostics.extend(self.compute_enhanced_type_diagnostics(program, uri));
        }

        // Semantic analysis with performance and style suggestions
        diagnostics.extend(self.check_enhanced_semantic_issues(content, uri));

        // Security analysis
        if self.config.enable_security_warnings {
            diagnostics.extend(self.check_security_issues(content, uri));
        }

        // Performance analysis
        if self.config.enable_performance_warnings {
            if let Some(program) = ast {
                diagnostics.extend(self.check_performance_issues(program, uri));
            }
        }

        // Style analysis
        if self.config.enable_style_suggestions {
            diagnostics.extend(self.check_style_issues(content, uri));
        }

        // Cache the diagnostics
        self.diagnostics_cache
            .insert(uri.to_string(), diagnostics.clone());

        Some(diagnostics)
    }

    /// Convert parse errors to enhanced LSP diagnostics.
    fn convert_enhanced_parse_errors(
        &self,
        error: &ligature_ast::AstError,
        uri: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        match error {
            ligature_ast::AstError::ParseError { message: _, span } => {
                let message = if self.config.enable_detailed_explanations {
                    "Unexpected token. This token doesn't fit the expected syntax at this position."
                        .to_string()
                } else {
                    "Unexpected token".to_string()
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    self.suggest_token_fix(&message)
                } else {
                    None
                };

                let full_message = if let Some(suggestion) = suggestion {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message
                };

                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("P001".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: full_message,
                    related_information: self.get_related_information_for_parse_error(error, uri),
                    tags: None,
                    data: None,
                });
            }
            _ => {
                // Handle other parse errors with basic conversion
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(error.span()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("P000".to_string())),
                    code_description: None,
                    source: Some("ligature-parser".to_string()),
                    message: format!("Parse error: {error:?}"),
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Compute enhanced type checking diagnostics.
    fn compute_enhanced_type_diagnostics(
        &mut self,
        program: &Program,
        uri: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Type check the program
        if let Err(type_error) = type_check_program(program) {
            diagnostics.extend(self.convert_enhanced_type_errors(&type_error, uri));
        }

        // Additional type-aware checks
        diagnostics.extend(self.check_enhanced_type_specific_issues(program, uri));

        diagnostics
    }

    /// Convert type errors to enhanced LSP diagnostics.
    fn convert_enhanced_type_errors(
        &self,
        error: &ligature_ast::AstError,
        uri: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        match error {
            ligature_ast::AstError::MethodTypeMismatch {
                method,
                expected,
                found,
                span,
            } => {
                let message = if self.config.enable_detailed_explanations {
                    format!(
                        "Type mismatch in method '{method}': expected type '{expected:?}', but found type '{found:?}'. This usually means the arguments don't match the function's expected parameter types."
                    )
                } else {
                    format!(
                        "Type mismatch in method {method}: expected {expected:?}, got {found:?}"
                    )
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    self.suggest_type_fix(&format!("{expected:?}"), &format!("{found:?}"))
                } else {
                    None
                };

                let full_message = if let Some(suggestion) = suggestion {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message
                };

                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("T001".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: full_message,
                    related_information: self.get_related_information_for_type_error(error, uri),
                    tags: None,
                    data: None,
                });
            }
            ligature_ast::AstError::UndefinedIdentifier { name, span } => {
                let message = if self.config.enable_detailed_explanations {
                    format!(
                        "Undefined identifier '{name}'. This variable or function hasn't been declared or imported. Check if you need to add an import statement or declare this identifier."
                    )
                } else {
                    format!("Undefined identifier: {name}")
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    self.suggest_identifier_fix(name)
                } else {
                    None
                };

                let full_message = if let Some(suggestion) = suggestion {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message
                };

                diagnostics.push(Diagnostic {
                    range: self.span_to_range(*span),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("T002".to_string())),
                    code_description: None,
                    source: Some("ligature-types".to_string()),
                    message: full_message,
                    related_information: self.get_related_information_for_type_error(error, uri),
                    tags: None,
                    data: None,
                });
            }
            _ => {
                // Handle other type errors with basic conversion
                diagnostics.push(Diagnostic {
                    range: self.span_to_range(error.span()),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("T000".to_string())),
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

    /// Check enhanced semantic issues.
    fn check_enhanced_semantic_issues(&self, content: &str, uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for unused imports
        diagnostics.extend(self.check_unused_imports_enhanced(content, uri));

        // Check for unused variables
        diagnostics.extend(self.check_unused_variables_enhanced(content, uri));

        // Check for potential issues
        diagnostics.extend(self.check_potential_issues_enhanced(content, uri));

        diagnostics
    }

    /// Check for unused imports with enhanced reporting.
    fn check_unused_imports_enhanced(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            if line.trim().starts_with("import ") {
                let import_name = line
                    .trim()
                    .strip_prefix("import ")
                    .and_then(|s| s.split_whitespace().next())
                    .unwrap_or("");

                if !import_name.is_empty() && !self.is_import_used(import_name, content) {
                    let message = if self.config.enable_detailed_explanations {
                        format!(
                            "Unused import '{import_name}'. This import statement brings in functionality that isn't being used in the current file. Consider removing it to keep your code clean."
                        )
                    } else {
                        format!("Unused import: {import_name}")
                    };

                    let suggestion = if self.config.enable_fix_suggestions {
                        "Remove this import statement if it's not needed"
                    } else {
                        ""
                    };

                    let full_message = if !suggestion.is_empty() {
                        format!("{message}\n\nSuggestion: {suggestion}")
                    } else {
                        message
                    };

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
                        severity: Some(DiagnosticSeverity::WARNING),
                        code: Some(NumberOrString::String("W001".to_string())),
                        code_description: None,
                        source: Some("ligature-semantic".to_string()),
                        message: full_message,
                        related_information: None,
                        tags: None,
                        data: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for unused variables with enhanced reporting.
    fn check_unused_variables_enhanced(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to find unused variables
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            if line.trim().starts_with("let ") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 2 {
                    let var_name = parts[1];
                    if !self.is_variable_used(var_name, content) {
                        let message = if self.config.enable_detailed_explanations {
                            format!(
                                "Unused variable '{var_name}'. This variable is declared but never used. Consider removing it or using it in your code."
                            )
                        } else {
                            format!("Unused variable: {var_name}")
                        };

                        let suggestion = if self.config.enable_fix_suggestions {
                            "Remove this variable declaration or use it in your code"
                        } else {
                            ""
                        };

                        let full_message = if !suggestion.is_empty() {
                            format!("{message}\n\nSuggestion: {suggestion}")
                        } else {
                            message
                        };

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
                            severity: Some(DiagnosticSeverity::WARNING),
                            code: Some(NumberOrString::String("W002".to_string())),
                            code_description: None,
                            source: Some("ligature-semantic".to_string()),
                            message: full_message,
                            related_information: None,
                            tags: None,
                            data: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for potential issues with enhanced reporting.
    fn check_potential_issues_enhanced(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for long lines
        let lines: Vec<&str> = content.lines().collect();
        for (line_num, line) in lines.iter().enumerate() {
            if line.len() > 100 {
                let message = if self.config.enable_detailed_explanations {
                    "This line is quite long (over 100 characters). Consider breaking it into multiple lines for better readability."
                } else {
                    "Line too long"
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    "Break this line into multiple lines or use line continuation"
                } else {
                    ""
                };

                let full_message = if !suggestion.is_empty() {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message.to_string()
                };

                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32,
                            character: 100,
                        },
                        end: Position {
                            line: line_num as u32,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(NumberOrString::String("I001".to_string())),
                    code_description: None,
                    source: Some("ligature-style".to_string()),
                    message: full_message,
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        // Check for trailing whitespace
        for (line_num, line) in lines.iter().enumerate() {
            if line.ends_with(' ') || line.ends_with('\t') {
                let message = if self.config.enable_detailed_explanations {
                    "This line has trailing whitespace. While this doesn't affect functionality, it's considered bad practice and can cause issues in version control."
                } else {
                    "Trailing whitespace"
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    "Remove the trailing whitespace"
                } else {
                    ""
                };

                let full_message = if !suggestion.is_empty() {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message.to_string()
                };

                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32,
                            character: line.trim_end().len() as u32,
                        },
                        end: Position {
                            line: line_num as u32,
                            character: line.len() as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(NumberOrString::String("I002".to_string())),
                    code_description: None,
                    source: Some("ligature-style".to_string()),
                    message: full_message,
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check for security issues.
    fn check_security_issues(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for potential security issues
        let lines: Vec<&str> = content.lines().collect();
        for (line_num, line) in lines.iter().enumerate() {
            // Check for hardcoded secrets (simplified)
            if line.contains("password") && line.contains("=") {
                let message = if self.config.enable_detailed_explanations {
                    "Potential security issue: This line appears to contain a hardcoded password. Consider using environment variables or a secure configuration system instead."
                } else {
                    "Potential hardcoded password"
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    "Use environment variables or a secure configuration system"
                } else {
                    ""
                };

                let full_message = if !suggestion.is_empty() {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message.to_string()
                };

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
                    severity: Some(DiagnosticSeverity::WARNING),
                    code: Some(NumberOrString::String("S001".to_string())),
                    code_description: None,
                    source: Some("ligature-security".to_string()),
                    message: full_message,
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check for performance issues.
    fn check_performance_issues(&self, _program: &Program, _uri: &str) -> Vec<Diagnostic> {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST for performance issues

        Vec::new()
    }

    /// Check for style issues.
    fn check_style_issues(&self, content: &str, _uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for inconsistent indentation
        let lines: Vec<&str> = content.lines().collect();
        let _expected_indent = 0;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }

            let indent = line.len() - line.trim_start().len();
            if indent % 2 != 0 && !trimmed.starts_with("//") {
                let message = if self.config.enable_detailed_explanations {
                    "Inconsistent indentation. This line uses an odd number of spaces for indentation, which may indicate inconsistent formatting."
                } else {
                    "Inconsistent indentation"
                };

                let suggestion = if self.config.enable_fix_suggestions {
                    "Use consistent indentation (typically 2 or 4 spaces)"
                } else {
                    ""
                };

                let full_message = if !suggestion.is_empty() {
                    format!("{message}\n\nSuggestion: {suggestion}")
                } else {
                    message.to_string()
                };

                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: line_num as u32,
                            character: 0,
                        },
                        end: Position {
                            line: line_num as u32,
                            character: indent as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::INFORMATION),
                    code: Some(NumberOrString::String("I003".to_string())),
                    code_description: None,
                    source: Some("ligature-style".to_string()),
                    message: full_message,
                    related_information: None,
                    tags: None,
                    data: None,
                });
            }
        }

        diagnostics
    }

    /// Check enhanced type-specific issues.
    fn check_enhanced_type_specific_issues(&self, program: &Program, uri: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Check for unused variables in the AST
        diagnostics.extend(self.check_unused_variables_in_ast(program, uri));

        // Check for potential type issues
        diagnostics.extend(self.check_potential_type_issues_in_ast(program, uri));

        diagnostics
    }

    /// Check for unused variables in the AST.
    fn check_unused_variables_in_ast(&self, _program: &Program, _uri: &str) -> Vec<Diagnostic> {
        // This is a simplified implementation
        // In a full implementation, you would traverse the AST to find unused variables

        Vec::new()
    }

    /// Check for potential type issues in the AST.
    fn check_potential_type_issues_in_ast(
        &self,
        _program: &Program,
        _uri: &str,
    ) -> Vec<Diagnostic> {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST for potential type issues

        Vec::new()
    }

    // Helper methods

    /// Suggest a fix for a token error.
    fn suggest_token_fix(&self, token: &str) -> Option<String> {
        match token {
            "(" => Some("Did you mean to close a parenthesis? Try adding ')'".to_string()),
            "[" => Some("Did you mean to close a bracket? Try adding ']'".to_string()),
            "{" => Some("Did you mean to close a brace? Try adding '}'".to_string()),
            _ => None,
        }
    }

    /// Suggest a fix for a type error.
    fn suggest_type_fix(&self, expected: &str, found: &str) -> Option<String> {
        match (expected, found) {
            ("Int", "String") => {
                Some("Convert the string to an integer using a conversion function".to_string())
            }
            ("String", "Int") => {
                Some("Convert the integer to a string using toString()".to_string())
            }
            ("Bool", "Int") => {
                Some("Convert the integer to a boolean using a comparison".to_string())
            }
            ("Int", "Bool") => {
                Some("Convert the boolean to an integer using if-then-else".to_string())
            }
            _ => None,
        }
    }

    /// Suggest a fix for an undefined identifier.
    fn suggest_identifier_fix(&self, name: &str) -> Option<String> {
        // Check if this might be a built-in function
        let builtins = [
            "add", "sub", "mul", "div", "eq", "lt", "gt", "concat", "length", "head", "tail",
        ];

        if builtins.contains(&name) {
            Some(format!(
                "Add 'import {name} from \"stdlib/core\";' at the top of your file"
            ))
        } else {
            Some(format!(
                "Declare '{name}' using 'let {name} = ...;' or add an appropriate import"
            ))
        }
    }

    /// Get related information for parse errors.
    fn get_related_information_for_parse_error(
        &self,
        _error: &ligature_ast::AstError,
        _uri: &str,
    ) -> Option<Vec<DiagnosticRelatedInformation>> {
        if self.config.enable_related_information {
            // In a full implementation, you would provide related information
            None
        } else {
            None
        }
    }

    /// Get related information for type errors.
    fn get_related_information_for_type_error(
        &self,
        _error: &ligature_ast::AstError,
        _uri: &str,
    ) -> Option<Vec<DiagnosticRelatedInformation>> {
        if self.config.enable_related_information {
            // In a full implementation, you would provide related information
            None
        } else {
            None
        }
    }

    /// Check if an import is used in the content.
    fn is_import_used(&self, import_name: &str, content: &str) -> bool {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to check import usage
        content.contains(import_name)
    }

    /// Check if a variable is used in the content.
    fn is_variable_used(&self, var_name: &str, content: &str) -> bool {
        // This is a simplified implementation
        // In a full implementation, you would analyze the AST to check variable usage
        let lines: Vec<&str> = content.lines().collect();
        for line in lines {
            if line.contains(var_name) && !line.trim().starts_with("let ") {
                return true;
            }
        }
        false
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

    /// Get cached diagnostics for a document.
    pub fn get_cached_diagnostics(&self, uri: &str) -> Option<&Vec<Diagnostic>> {
        self.diagnostics_cache.get(uri)
    }

    /// Clear diagnostics for a document.
    pub fn clear_diagnostics(&mut self, uri: &str) {
        self.diagnostics_cache.remove(uri);
    }

    /// Update configuration.
    pub fn update_config(&mut self, config: EnhancedDiagnosticsConfig) {
        self.config = config;
    }
}

impl Default for EnhancedDiagnosticsProvider {
    fn default() -> Self {
        Self::new()
    }
}
