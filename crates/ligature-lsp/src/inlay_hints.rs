//! Inlay hints provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{DeclarationKind, Expr, ExprKind, Program, Type, TypeKind};
// use ligature_types::checker::TypeChecker;
use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, Position, Range};

use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};

/// Provider for inlay hints (type annotations and parameter names).
pub struct InlayHintsProvider {
    /// Type checker for type inference.
    // type_checker: TypeChecker,
    /// Cache of inlay hints by document URI.
    hints_cache: HashMap<String, Vec<InlayHint>>,
    /// Async evaluation service for evaluation-based type inference.
    async_evaluation: Option<AsyncEvaluationService>,
}

impl InlayHintsProvider {
    /// Create a new inlay hints provider.
    pub fn new() -> Self {
        Self {
            // type_checker: TypeChecker::new(),
            hints_cache: HashMap::new(),
            async_evaluation: None,
        }
    }

    /// Create a new inlay hints provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let async_evaluation = AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        Self {
            // type_checker: TypeChecker::new(),
            hints_cache: HashMap::new(),
            async_evaluation,
        }
    }

    /// Provide inlay hints for a given range with async evaluation support.
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
            hints.extend(self.get_type_hints(program, range).await);

            // Parameter name hints for function calls
            hints.extend(self.get_parameter_hints(program, range).await);

            // Variable type hints
            hints.extend(self.get_variable_type_hints(program, range).await);

            // Evaluation-based hints
            if let Some(eval_service) = &self.async_evaluation {
                hints.extend(
                    self.get_evaluation_based_hints(program, range, eval_service)
                        .await,
                );
            }
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
            hints.extend(self.get_type_hints_sync(program, range));

            // Parameter name hints for function calls
            hints.extend(self.get_parameter_hints_sync(program, range));

            // Variable type hints
            hints.extend(self.get_variable_type_hints_sync(program, range));
        }

        hints
    }

    /// Get type hints for expressions with async evaluation.
    async fn get_type_hints(&self, program: &Program, range: Range) -> Vec<InlayHint> {
        let mut hints = Vec::new();

        // Walk through the AST and find expressions that could benefit from type hints
        self.walk_program_for_type_hints(program, &mut hints, range)
            .await;

        hints
    }

    /// Get type hints for expressions (synchronous version).
    fn get_type_hints_sync(&self, program: &Program, range: Range) -> Vec<InlayHint> {
        let mut hints = Vec::new();

        // Walk through the AST and find expressions that could benefit from type hints
        self.walk_program_for_type_hints_sync(program, &mut hints, range);

        hints
    }

    /// Get evaluation-based hints for expressions.
    async fn get_evaluation_based_hints(
        &self,
        program: &Program,
        range: Range,
        eval_service: &AsyncEvaluationService,
    ) -> Vec<InlayHint> {
        let mut hints = Vec::new();

        // Evaluate expressions to get runtime type information
        for declaration in &program.declarations {
            if let DeclarationKind::Value(value_decl) = &declaration.kind {
                if self.expression_in_range(&value_decl.value, range) {
                    if let Ok(eval_result) = eval_service
                        .evaluate_expression(
                            &value_decl.value,
                            Some(&format!("hint_{}", value_decl.name)),
                        )
                        .await
                    {
                        if eval_result.success && !eval_result.values.is_empty() {
                            let value = &eval_result.values[0];
                            let type_hint = self.value_to_type_hint(value, &value_decl.value);
                            if let Some(hint) = type_hint {
                                hints.push(hint);
                            }
                        }
                    }
                }
            }
        }

        hints
    }

    /// Convert a value to a type hint.
    fn value_to_type_hint(
        &self,
        value: &ligature_eval::value::Value,
        expr: &Expr,
    ) -> Option<InlayHint> {
        let type_string = match &value.kind {
            ligature_eval::value::ValueKind::Integer(_) => ": Int".to_string(),
            ligature_eval::value::ValueKind::Float(_) => ": Float".to_string(),
            ligature_eval::value::ValueKind::String(_) => ": String".to_string(),
            ligature_eval::value::ValueKind::Boolean(_) => ": Bool".to_string(),
            ligature_eval::value::ValueKind::List(_) => ": List".to_string(),
            ligature_eval::value::ValueKind::Record(_) => ": Record".to_string(),
            ligature_eval::value::ValueKind::Function { .. } => ": Function".to_string(),
            ligature_eval::value::ValueKind::Closure { .. } => ": Closure".to_string(),
            ligature_eval::value::ValueKind::Unit => ": Unit".to_string(),
            ligature_eval::value::ValueKind::Union { .. } => ": Union".to_string(),
            ligature_eval::value::ValueKind::Module { .. } => ": Module".to_string(),
        };

        Some(InlayHint {
            position: Position {
                line: expr.span.line as u32,
                character: expr.span.column as u32,
            },
            label: InlayHintLabel::String(type_string),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: None,
            padding_left: Some(false),
            padding_right: Some(true),
            data: None,
        })
    }

    /// Walk through the program to find expressions that need type hints (async version).
    async fn walk_program_for_type_hints(
        &self,
        program: &Program,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        for declaration in &program.declarations {
            match &declaration.kind {
                DeclarationKind::Value(value_decl) => {
                    self.walk_expression_for_type_hints(&value_decl.value, hints, range)
                        .await;
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

    /// Walk through the program to find expressions that need type hints (sync version).
    fn walk_program_for_type_hints_sync(
        &self,
        program: &Program,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        for declaration in &program.declarations {
            match &declaration.kind {
                DeclarationKind::Value(value_decl) => {
                    self.walk_expression_for_type_hints_sync(&value_decl.value, hints, range);
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

    /// Walk through an expression to find type hints (async version).
    async fn walk_expression_for_type_hints(
        &self,
        expr: &Expr,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        if !self.expression_in_range(expr, range) {
            return;
        }

        // Use the sync version to avoid recursion issues
        self.walk_expression_for_type_hints_sync(expr, hints, range);
    }

    /// Walk through an expression to find type hints (sync version).
    #[allow(clippy::only_used_in_recursion)]
    fn walk_expression_for_type_hints_sync(
        &self,
        expr: &Expr,
        hints: &mut Vec<InlayHint>,
        range: Range,
    ) {
        if !self.expression_in_range(expr, range) {
            return;
        }

        match &expr.kind {
            ExprKind::Literal(_) => {
                // Literals don't need type hints
            }
            ExprKind::Variable(_name) => {
                // Variables might need type hints if we can infer their type
                // TODO: Implement variable type inference
            }
            ExprKind::Application { function, argument } => {
                // Function applications might need type hints
                self.walk_expression_for_type_hints_sync(function, hints, range);
                self.walk_expression_for_type_hints_sync(argument, hints, range);
            }
            ExprKind::Let {
                name: _,
                value,
                body,
            } => {
                // Let expressions might need type hints for bindings
                self.walk_expression_for_type_hints_sync(value, hints, range);
                self.walk_expression_for_type_hints_sync(body, hints, range);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // If expressions might need type hints
                self.walk_expression_for_type_hints_sync(condition, hints, range);
                self.walk_expression_for_type_hints_sync(then_branch, hints, range);
                self.walk_expression_for_type_hints_sync(else_branch, hints, range);
            }
            ExprKind::BinaryOp {
                operator: _,
                left,
                right,
            } => {
                // Binary operations might need type hints
                self.walk_expression_for_type_hints_sync(left, hints, range);
                self.walk_expression_for_type_hints_sync(right, hints, range);
            }
            ExprKind::UnaryOp {
                operator: _,
                operand,
            } => {
                // Unary operations might need type hints
                self.walk_expression_for_type_hints_sync(operand, hints, range);
            }
            ExprKind::Match { scrutinee, cases } => {
                // Match expressions might need type hints
                self.walk_expression_for_type_hints_sync(scrutinee, hints, range);
                for case in cases {
                    self.walk_expression_for_type_hints_sync(&case.expression, hints, range);
                }
            }
            ExprKind::Record { fields } => {
                // Records might need type hints
                for field in fields {
                    self.walk_expression_for_type_hints_sync(&field.value, hints, range);
                }
            }
            ExprKind::FieldAccess { record, field: _ } => {
                // Record access might need type hints
                self.walk_expression_for_type_hints_sync(record, hints, range);
            }
            ExprKind::Union { variant: _, value } => {
                // Union expressions might need type hints
                if let Some(value_expr) = value {
                    self.walk_expression_for_type_hints_sync(value_expr, hints, range);
                }
            }
            ExprKind::Abstraction {
                parameter: _,
                parameter_type: _,
                body,
            } => {
                // Functions might need type hints
                self.walk_expression_for_type_hints_sync(body, hints, range);
            }
            ExprKind::Annotated {
                expression,
                type_annotation: _,
            } => {
                // Type annotated expressions don't need additional hints
                self.walk_expression_for_type_hints_sync(expression, hints, range);
            }
        }
    }

    /// Get parameter hints for function calls with async evaluation.
    async fn get_parameter_hints(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // TODO: Implement async parameter hints
        Vec::new()
    }

    /// Get parameter hints for function calls (synchronous version).
    fn get_parameter_hints_sync(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // TODO: Implement parameter hints
        Vec::new()
    }

    /// Get variable type hints with async evaluation.
    async fn get_variable_type_hints(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // TODO: Implement async variable type hints
        Vec::new()
    }

    /// Get variable type hints (synchronous version).
    fn get_variable_type_hints_sync(&self, _program: &Program, _range: Range) -> Vec<InlayHint> {
        // TODO: Implement variable type hints
        Vec::new()
    }

    /// Check if an expression is within the given range.
    fn expression_in_range(&self, expr: &Expr, range: Range) -> bool {
        let expr_start = Position {
            line: expr.span.line as u32,
            character: expr.span.column as u32,
        };
        let expr_end = Position {
            line: expr.span.line as u32,
            character: expr.span.column as u32,
        };

        expr_start >= range.start && expr_end <= range.end
    }

    #[allow(dead_code)]
    fn should_show_type_hint(&self, type_: &Type) -> bool {
        // Don't show hints for simple types
        matches!(
            type_.kind,
            TypeKind::Integer | TypeKind::String | TypeKind::Bool | TypeKind::Unit
        )
    }

    #[allow(dead_code)]
    fn type_to_string(&self, type_: &Type) -> String {
        match &type_.kind {
            TypeKind::Integer => "Int".to_string(),
            TypeKind::String => "String".to_string(),
            TypeKind::Bool => "Bool".to_string(),
            TypeKind::Unit => "Unit".to_string(),
            TypeKind::Variable(name) => name.clone(),
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                format!("{parameter:?} -> {return_type:?}")
            }
            TypeKind::Record { fields } => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|field| format!("{}: {:?}", field.name, field.type_))
                    .collect();
                format!("{{{}}}", field_strs.join(", "))
            }
            TypeKind::Union { variants } => {
                let variant_strs: Vec<String> = variants
                    .iter()
                    .map(|variant| {
                        if let Some(type_) = &variant.type_ {
                            format!("{} {:?}", variant.name, type_)
                        } else {
                            variant.name.clone()
                        }
                    })
                    .collect();
                variant_strs.join(" | ").to_string()
            }
            TypeKind::Application { function, argument } => {
                format!("{function:?} {argument:?}")
            }
            TypeKind::Refinement { base_type, .. } => {
                format!("{base_type:?}")
            }
            TypeKind::ConstraintType { base_type, .. } => {
                format!("{base_type:?}")
            }
            TypeKind::Module { name } => format!("module {name}"),
            _ => format!("{type_:?}"),
        }
    }

    // Type inference methods
    #[allow(dead_code)]
    fn infer_variable_type(&self, _name: &str, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_application_type(
        &self,
        _function: &Expr,
        _argument: &Expr,
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_binding_type(&self, _value: &Expr, _name: &str, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_conditional_type(
        &self,
        _condition: &Expr,
        _then_branch: &Expr,
        _else_branch: &Expr,
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_binary_op_type(&self, _left: &Expr, _right: &Expr, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_unary_op_type(&self, _operand: &Expr, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_match_type(
        &self,
        _scrutinee: &Expr,
        _cases: &[ligature_ast::MatchCase],
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_record_type(&self, _fields: &[(String, Expr)], _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_record_access_type(&self, _record: &Expr, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_list_type(&self, _elements: &[Expr], _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_list_cons_type(&self, _head: &Expr, _tail: &Expr, _expr: &Expr) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_lambda_type(
        &self,
        _parameter: &str,
        _parameter_type: Option<&Type>,
        _body: &Expr,
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_parameter_type(
        &self,
        _parameter: &str,
        _function_type: &Type,
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    #[allow(dead_code)]
    fn infer_parameter_type_from_usage(
        &self,
        _parameter: &str,
        _argument: &Expr,
        _expr: &Expr,
    ) -> Option<InlayHint> {
        // Placeholder implementation
        None
    }

    /// Clear the hints cache for a specific URI.
    pub fn clear_cache(&mut self, uri: &str) {
        self.hints_cache.remove(uri);
    }

    /// Get cached hints for a specific URI.
    pub fn get_cached_hints(&self, uri: &str) -> Option<&Vec<InlayHint>> {
        self.hints_cache.get(uri)
    }
}

impl Default for InlayHintsProvider {
    fn default() -> Self {
        Self::new()
    }
}
