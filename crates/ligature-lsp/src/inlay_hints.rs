//! Inlay hints provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Expr, ExprKind, Program, Span, Type, TypeKind};
use ligature_types::checker::TypeChecker;
use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, Position, Range};

/// Provider for inlay hints (type annotations and parameter names).
pub struct InlayHintsProvider {
    /// Type checker for type inference.
    type_checker: TypeChecker,
    /// Cache of inlay hints by document URI.
    hints_cache: HashMap<String, Vec<InlayHint>>,
}

impl InlayHintsProvider {
    /// Create a new inlay hints provider.
    pub fn new() -> Self {
        Self {
            type_checker: TypeChecker::new(),
            hints_cache: HashMap::new(),
        }
    }

    /// Provide inlay hints for a given range.
    pub async fn provide_inlay_hints(
        &self,
        _uri: &str,
        content: &str,
        range: Range,
    ) -> Vec<InlayHint> {
        // Try to parse the program for context-aware inlay hints
        let ast = ligature_parser::parse_program(content).ok();

        let mut hints = Vec::new();

        if let Some(program) = ast.as_ref() {
            // Type hints for expressions
            hints.extend(self.get_type_hints(program, range));

            // Parameter name hints for function calls
            hints.extend(self.get_parameter_hints(program, range));

            // Variable type hints
            hints.extend(self.get_variable_type_hints(program, range));
        }

        hints
    }

    /// Get inlay hints for a given range (original method).
    pub fn get_inlay_hints(
        &mut self,
        range: Range,
        _content: &str,
        ast: Option<&Program>,
    ) -> Vec<InlayHint> {
        let mut hints = Vec::new();

        if let Some(program) = ast {
            // Type hints for expressions
            hints.extend(self.get_type_hints(program, range));

            // Parameter name hints for function calls
            hints.extend(self.get_parameter_hints(program, range));

            // Variable type hints
            hints.extend(self.get_variable_type_hints(program, range));
        }

        hints
    }

    /// Get type hints for expressions.
    fn get_type_hints(&self, program: &Program, range: Range) -> Vec<InlayHint> {
        let mut hints = Vec::new();

        // Walk through the AST and find expressions that could benefit from type hints
        self.walk_program_for_type_hints(program, &mut hints, range);

        hints
    }

    /// Walk through the program to find expressions that need type hints.
    fn walk_program_for_type_hints(
        &self,
        program: &Program,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        for declaration in &program.declarations {
            match &declaration.kind {
                DeclarationKind::Value(value_decl) => {
                    self.walk_expression_for_type_hints(&value_decl.value, hints, range);
                }
                DeclarationKind::TypeAlias(_) => {
                    // Type aliases don't need type hints
                }
                DeclarationKind::TypeConstructor(_) => {
                    // Type constructors don't need type hints
                }
                DeclarationKind::Import(_) => {
                    // Imports don't need type hints
                }
                DeclarationKind::Export(_) => {
                    // Exports don't need type hints
                }
                DeclarationKind::TypeClass(_) => {
                    // Type classes don't need type hints
                }
                DeclarationKind::Instance(_) => {
                    // Instances don't need type hints
                }
            }
        }
    }

    /// Walk through an expression to find type hints.
    fn walk_expression_for_type_hints(
        &self,
        expr: &Expr,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        // Check if this expression is in the requested range
        if !self.expression_in_range(expr, range) {
            return;
        }

        match &expr.kind {
            ExprKind::Literal(_) => {
                // Literals don't need type hints as they're obvious
            }
            ExprKind::Variable(name) => {
                // Variables might need type hints if their type is not obvious
                if let Ok(var_type) = self.type_checker.infer_variable(name) {
                    if self.should_show_type_hint(&var_type) {
                        hints.push(InlayHint {
                            position: Position {
                                line: expr.span.line as u32,
                                character: expr.span.column as u32,
                            },
                            label: InlayHintLabel::String(format!(
                                ": {}",
                                self.type_to_string(&var_type)
                            )),
                            kind: Some(InlayHintKind::TYPE),
                            text_edits: None,
                            tooltip: None,
                            padding_left: Some(false),
                            padding_right: Some(true),
                            data: None,
                        });
                    }
                }
            }
            ExprKind::Application { function, argument } => {
                // Function applications might need type hints for the result
                self.walk_expression_for_type_hints(function, hints, range);
                self.walk_expression_for_type_hints(argument, hints, range);

                // Add type hint for the application result
                // Note: Type checker calls disabled in async version to avoid mutable reference issues
                // if let Ok(app_type) = self.type_checker.infer_application(function, argument) {
                //     if self.should_show_type_hint(&app_type) {
                //         hints.push(InlayHint {
                //             position: Position {
                //                 line: expr.span.line as u32,
                //                 character: expr.span.column as u32,
                //             },
                //             label: InlayHintLabel::String(format!(": {}", self.type_to_string(&app_type))),
                //             kind: Some(InlayHintKind::TYPE),
                //             text_edits: None,
                //             tooltip: None,
                //             padding_left: Some(false),
                //             padding_right: Some(true),
                //             data: None,
                //         });
                //     }
                // }
            }
            ExprKind::Let {
                name: _,
                value,
                body,
            } => {
                // Let expressions might need type hints for bindings
                self.walk_expression_for_type_hints(value, hints, range);

                // Add type hint for the binding if it doesn't have an annotation
                // Note: Type checker calls disabled in async version to avoid mutable reference issues
                // if let Ok(binding_type) = self.type_checker.infer_expression(value) {
                //     if self.should_show_type_hint(&binding_type) {
                //         hints.push(InlayHint {
                //             position: Position {
                //                 line: expr.span.line as u32,
                //                 character: expr.span.column as u32,
                //             },
                //             label: InlayHintLabel::String(format!(": {}", self.type_to_string(&binding_type))),
                //             kind: Some(InlayHintKind::TYPE),
                //             text_edits: None,
                //             tooltip: None,
                //             padding_left: Some(false),
                //             padding_right: Some(true),
                //             data: None,
                //         });
                //     }
                // }
                self.walk_expression_for_type_hints(body, hints, range);
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                // Functions might need type hints for parameters and return type
                if parameter_type.is_none() {
                    // Try to infer parameter type from usage
                    if let Ok(param_type) = self.infer_parameter_type_from_usage(parameter, body) {
                        if self.should_show_type_hint(&param_type) {
                            hints.push(InlayHint {
                                position: Position {
                                    line: expr.span.line as u32,
                                    character: expr.span.column as u32,
                                },
                                label: InlayHintLabel::String(format!(
                                    ": {}",
                                    self.type_to_string(&param_type)
                                )),
                                kind: Some(InlayHintKind::TYPE),
                                text_edits: None,
                                tooltip: None,
                                padding_left: Some(false),
                                padding_right: Some(true),
                                data: None,
                            });
                        }
                    }
                }
                self.walk_expression_for_type_hints(body, hints, range);
            }
            ExprKind::Match { scrutinee, cases } => {
                // Match expressions might need type hints
                self.walk_expression_for_type_hints(scrutinee, hints, range);
                for case in cases {
                    self.walk_expression_for_type_hints(&case.expression, hints, range);
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // If expressions might need type hints
                self.walk_expression_for_type_hints(condition, hints, range);
                self.walk_expression_for_type_hints(then_branch, hints, range);
                self.walk_expression_for_type_hints(else_branch, hints, range);
            }
            ExprKind::Record { fields } => {
                // Record expressions might need type hints
                for field in fields {
                    self.walk_expression_for_type_hints(&field.value, hints, range);
                }
            }
            ExprKind::FieldAccess { record, field: _ } => {
                // Record access might need type hints
                self.walk_expression_for_type_hints(record, hints, range);
            }
            ExprKind::Union { variant: _, value } => {
                // Union expressions might need type hints
                if let Some(value_expr) = value {
                    self.walk_expression_for_type_hints(value_expr, hints, range);
                }
            }
            ExprKind::BinaryOp {
                left,
                operator: _,
                right,
            } => {
                // Binary operations might need type hints
                self.walk_expression_for_type_hints(left, hints, range);
                self.walk_expression_for_type_hints(right, hints, range);
            }
            ExprKind::UnaryOp {
                operator: _,
                operand,
            } => {
                // Unary operations might need type hints
                self.walk_expression_for_type_hints(operand, hints, range);
            }
            ExprKind::Annotated {
                expression,
                type_annotation: _,
            } => {
                // Type annotated expressions don't need additional hints
                self.walk_expression_for_type_hints(expression, hints, range);
            }
        }
    }

    /// Get parameter name hints for function calls.
    fn get_parameter_hints(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Find function applications in the AST
        // 2. Look up the function definition to get parameter names
        // 3. Add parameter name hints for each argument

        Vec::new()
    }

    /// Get variable type hints.
    fn get_variable_type_hints(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Find variable declarations without type annotations
        // 2. Infer their types from usage
        // 3. Add type hints where helpful

        Vec::new()
    }

    /// Check if an expression is within the given range.
    fn expression_in_range(&self, expr: &Expr, range: Range) -> bool {
        let expr_start = Position {
            line: expr.span.start as u32,
            character: expr.span.start as u32,
        };
        let expr_end = Position {
            line: expr.span.end as u32,
            character: expr.span.end as u32,
        };

        expr_start >= range.start && expr_end <= range.end
    }

    /// Check if a type hint should be shown.
    fn should_show_type_hint(&self, type_: &Type) -> bool {
        // Don't show hints for obvious types
        match &type_.kind {
            TypeKind::Integer => false, // Obvious from literal
            TypeKind::Bool => false,    // Obvious from literal
            TypeKind::String => false,  // Obvious from literal
            TypeKind::Unit => false,    // Obvious
            _ => true,                  // Show hints for complex types
        }
    }

    /// Convert a type to a string representation.
    #[allow(clippy::only_used_in_recursion)]
    fn type_to_string(&self, type_: &Type) -> String {
        match &type_.kind {
            TypeKind::Integer => "Int".to_string(),
            TypeKind::Bool => "Bool".to_string(),
            TypeKind::String => "String".to_string(),
            TypeKind::Unit => "Unit".to_string(),
            TypeKind::Variable(name) => name.clone(),
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                format!(
                    "{} -> {}",
                    self.type_to_string(parameter),
                    self.type_to_string(return_type)
                )
            }
            TypeKind::List(element_type) => {
                format!("List {}", self.type_to_string(element_type))
            }
            TypeKind::Record { fields } => {
                let field_strings: Vec<String> = fields
                    .iter()
                    .map(|field| format!("{}: {}", field.name, self.type_to_string(&field.type_)))
                    .collect();
                format!("{{{}}}", field_strings.join(", "))
            }
            TypeKind::Union { variants } => {
                let variant_strings: Vec<String> = variants
                    .iter()
                    .map(|variant| {
                        if let Some(type_) = &variant.type_ {
                            format!("{} {}", variant.name, self.type_to_string(type_))
                        } else {
                            variant.name.clone()
                        }
                    })
                    .collect();
                variant_strings.join(" | ").to_string()
            }
            _ => format!("{:?}", type_.kind),
        }
    }

    /// Infer parameter type from function body usage.
    #[allow(dead_code)]
    fn infer_parameter_type(
        &self,
        param: &str,
        _body: &Expr,
    ) -> Result<Type, ligature_ast::AstError> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Analyze how the parameter is used in the function body
        // 2. Infer the type from usage patterns
        // 3. Return the inferred type

        // For now, return a generic type variable
        Ok(Type::variable(param.to_string(), Span::default()))
    }

    /// Infer parameter type from usage in function body.
    fn infer_parameter_type_from_usage(
        &self,
        parameter: &str,
        _body: &Expr,
    ) -> Result<Type, ligature_ast::AstError> {
        // This is a simplified implementation
        // In a full implementation, you would:
        // 1. Analyze how the parameter is used in the function body
        // 2. Infer the type from usage patterns
        // 3. Return the inferred type

        // For now, return a generic type variable
        Ok(Type::variable(
            parameter.to_string(),
            ligature_ast::Span::default(),
        ))
    }

    /// Clear the cache for a document.
    pub fn clear_cache(&mut self, uri: &str) {
        self.hints_cache.remove(uri);
    }

    /// Get cached hints for a document.
    pub fn get_cached_hints(&self, uri: &str) -> Option<&Vec<InlayHint>> {
        self.hints_cache.get(uri)
    }
}

impl Default for InlayHintsProvider {
    fn default() -> Self {
        Self::new()
    }
}
