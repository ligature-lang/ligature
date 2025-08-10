//! Formatting provider for the Ligature LSP server.

use ligature_ast::{Declaration, DeclarationKind, Expr, ExprKind, Program};
use lsp_types::{Position, Range, TextEdit};

use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};
use crate::config::FormattingConfig;

/// Provider for code formatting.
#[derive(Clone)]
pub struct FormattingProvider {
    /// Configuration for formatting options.
    config: FormattingConfig,
    /// Async evaluation service for evaluation-based formatting decisions.
    async_evaluation: Option<AsyncEvaluationService>,
}

impl FormattingProvider {
    /// Create a new formatting provider with default configuration.
    pub fn new() -> Self {
        Self {
            config: crate::config::FormattingConfig::default(),
            async_evaluation: None,
        }
    }

    /// Create a new formatting provider with custom configuration.
    pub fn with_config(config: crate::config::FormattingConfig) -> Self {
        Self {
            config,
            async_evaluation: None,
        }
    }

    /// Create a new formatting provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let async_evaluation = AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        Self {
            config: crate::config::FormattingConfig::default(),
            async_evaluation,
        }
    }

    /// Format an entire document with async evaluation support.
    pub async fn format_document(&self, uri: &str, content: &str) -> Vec<TextEdit> {
        // Try to parse the program for AST-based formatting
        let ast = ligature_parser::parse_program(content).ok();

        if let Some(program) = ast.as_ref() {
            // Use async evaluation to make formatting decisions
            if let Some(eval_service) = &self.async_evaluation {
                self.format_program_with_evaluation(uri, content, program, eval_service)
                    .await
            } else {
                self.format_program(uri, content, program)
            }
        } else {
            // If parsing failed, do basic formatting
            self.format_basic(content)
        }
    }

    /// Format an entire document (original method).
    pub fn format_document_sync(
        &self,
        uri: &str,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<TextEdit> {
        if let Some(program) = ast {
            self.format_program(uri, content, program)
        } else {
            // If parsing failed, do basic formatting
            self.format_basic(content)
        }
    }

    /// Format a specific range within a document with async evaluation support.
    pub async fn format_range(&self, uri: &str, content: &str, range: Range) -> Vec<TextEdit> {
        // Try to parse the program for AST-based formatting
        let ast = ligature_parser::parse_program(content).ok();

        if let Some(program) = ast.as_ref() {
            // Use async evaluation to make formatting decisions
            if let Some(eval_service) = &self.async_evaluation {
                self.format_program_range_with_evaluation(
                    uri,
                    content,
                    range,
                    program,
                    eval_service,
                )
                .await
            } else {
                self.format_program_range(uri, content, range, program)
            }
        } else {
            // If parsing failed, do basic formatting for the range
            self.format_basic_range(content, range)
        }
    }

    /// Format a specific range within a document (original method).
    pub fn format_range_sync(
        &self,
        uri: &str,
        content: &str,
        range: Range,
        ast: Option<&Program>,
    ) -> Vec<TextEdit> {
        if let Some(program) = ast {
            self.format_program_range(uri, content, range, program)
        } else {
            // If parsing failed, do basic formatting for the range
            self.format_basic_range(content, range)
        }
    }

    /// Format a program with evaluation-based decisions.
    async fn format_program_with_evaluation(
        &self,
        _uri: &str,
        content: &str,
        program: &Program,
        eval_service: &AsyncEvaluationService,
    ) -> Vec<TextEdit> {
        let mut edits = Vec::new();
        let mut formatted_content = String::new();
        let _current_pos = 0;

        for decl in &program.declarations {
            let formatted_decl = self
                .format_declaration_with_evaluation(decl, 0, eval_service)
                .await;
            formatted_content.push_str(&formatted_decl);
            formatted_content.push('\n');
        }

        // Create a single edit for the entire document
        edits.push(TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: content.lines().count() as u32,
                    character: 0,
                },
            },
            new_text: formatted_content,
        });

        edits
    }

    /// Format a program range with evaluation-based decisions.
    async fn format_program_range_with_evaluation(
        &self,
        _uri: &str,
        content: &str,
        range: Range,
        program: &Program,
        eval_service: &AsyncEvaluationService,
    ) -> Vec<TextEdit> {
        let mut edits = Vec::new();
        let _lines: Vec<&str> = content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        // Find declarations that fall within the range
        for decl in &program.declarations {
            let decl_start = decl.span.line;
            let decl_end = decl.span.line;

            if decl_start >= start_line && decl_end <= end_line {
                let formatted_decl = self
                    .format_declaration_with_evaluation(decl, 0, eval_service)
                    .await;

                // Create edit for this declaration
                edits.push(TextEdit {
                    range: Range {
                        start: Position {
                            line: decl_start as u32,
                            character: 0,
                        },
                        end: Position {
                            line: decl_end as u32,
                            character: 0,
                        },
                    },
                    new_text: formatted_decl,
                });
            }
        }

        edits
    }

    /// Format a declaration with evaluation-based decisions.
    async fn format_declaration_with_evaluation(
        &self,
        decl: &Declaration,
        indent_level: usize,
        eval_service: &AsyncEvaluationService,
    ) -> String {
        let _indent = "    ".repeat(indent_level);

        match &decl.kind {
            DeclarationKind::Value(value_decl) => {
                self.format_value_declaration_with_evaluation(
                    value_decl,
                    indent_level,
                    eval_service,
                )
                .await
            }
            DeclarationKind::TypeAlias(type_alias) => {
                self.format_type_alias(type_alias, indent_level)
            }
            DeclarationKind::TypeConstructor(type_constructor) => {
                self.format_type_constructor(type_constructor, indent_level)
            }
            DeclarationKind::TypeClass(type_class) => {
                self.format_type_class(type_class, indent_level)
            }
            DeclarationKind::Instance(instance_decl) => {
                self.format_instance_declaration(instance_decl, indent_level)
            }
            DeclarationKind::Import(import) => self.format_import(import, indent_level),
            DeclarationKind::Export(export) => self.format_export(export, indent_level),
        }
    }

    /// Format a value declaration with evaluation-based decisions.
    async fn format_value_declaration_with_evaluation(
        &self,
        value_decl: &ligature_ast::ValueDeclaration,
        indent_level: usize,
        eval_service: &AsyncEvaluationService,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        // Evaluate the value to determine formatting style
        let should_use_multiline = if let Ok(eval_result) = eval_service
            .evaluate_expression(
                &value_decl.value,
                Some(&format!("format_{}", value_decl.name)),
            )
            .await
        {
            // Use multiline formatting for complex values
            eval_result.success && self.is_complex_value(&eval_result.values)
        } else {
            // Fallback to simple formatting
            false
        };

        formatted.push_str(&indent);
        formatted.push_str("let ");
        formatted.push_str(&value_decl.name);

        if let Some(type_annotation) = &value_decl.type_annotation {
            formatted.push_str(" : ");
            formatted.push_str(&self.format_type(type_annotation));
        }

        formatted.push_str(" = ");

        if should_use_multiline {
            formatted.push('\n');
            formatted
                .push_str(&self.format_expression_multiline(&value_decl.value, indent_level + 1));
        } else {
            formatted.push_str(&self.format_expression(&value_decl.value, indent_level));
        }

        formatted.push(';');
        formatted
    }

    /// Check if a value is complex enough to warrant multiline formatting.
    fn is_complex_value(&self, values: &[ligature_eval::value::Value]) -> bool {
        if values.is_empty() {
            return false;
        }

        match &values[0].kind {
            ligature_eval::value::ValueKind::Record(fields) => fields.len() > 3,
            ligature_eval::value::ValueKind::List(elements) => elements.len() > 5,
            ligature_eval::value::ValueKind::Function { .. } => true,
            ligature_eval::value::ValueKind::Closure { .. } => true,
            _ => false,
        }
    }

    /// Format an expression in multiline style.
    fn format_expression_multiline(&self, expr: &Expr, indent_level: usize) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        match &expr.kind {
            ExprKind::Record { fields } => {
                formatted.push_str("{\n");
                for (i, field) in fields.iter().enumerate() {
                    formatted.push_str(&indent);
                    formatted.push_str("    ");
                    formatted.push_str(&field.name);
                    formatted.push_str(" = ");
                    formatted.push_str(&self.format_expression(&field.value, indent_level + 1));
                    if i < fields.len() - 1 {
                        formatted.push(',');
                    }
                    formatted.push('\n');
                }
                formatted.push_str(&indent);
                formatted.push('}');
            }
            ExprKind::Let { name, value, body } => {
                formatted.push_str("let\n");
                formatted.push_str(&indent);
                formatted.push_str("    ");
                formatted.push_str(name);
                formatted.push_str(" = ");
                formatted.push_str(&self.format_expression(value, indent_level + 1));
                formatted.push('\n');
                formatted.push_str(&indent);
                formatted.push_str("in ");
                formatted.push_str(&self.format_expression(body, indent_level));
            }
            _ => {
                // Fallback to single-line formatting
                formatted.push_str(&self.format_expression(expr, indent_level));
            }
        }

        formatted
    }

    /// Format a program with full AST analysis.
    fn format_program(&self, _uri: &str, content: &str, program: &Program) -> Vec<TextEdit> {
        let mut edits = Vec::new();
        let mut formatted_content = String::new();
        let _current_pos = 0;

        for decl in &program.declarations {
            let formatted_decl = self.format_declaration(decl, 0);
            formatted_content.push_str(&formatted_decl);
            formatted_content.push('\n');
        }

        // Create a single edit for the entire document
        edits.push(TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: content.lines().count() as u32,
                    character: 0,
                },
            },
            new_text: formatted_content,
        });

        edits
    }

    /// Format a program range with full AST analysis.
    fn format_program_range(
        &self,
        _uri: &str,
        _content: &str,
        range: Range,
        program: &Program,
    ) -> Vec<TextEdit> {
        let mut edits = Vec::new();

        // Find declarations that fall within the range
        for decl in &program.declarations {
            let decl_start = decl.span.line;
            let decl_end = decl.span.line;
            let range_start = range.start.line as usize;
            let range_end = range.end.line as usize;

            if decl_start >= range_start && decl_end <= range_end {
                let formatted_decl = self.format_declaration(decl, 0);

                // Create edit for this declaration
                edits.push(TextEdit {
                    range: Range {
                        start: Position {
                            line: decl_start as u32,
                            character: 0,
                        },
                        end: Position {
                            line: decl_end as u32,
                            character: 0,
                        },
                    },
                    new_text: formatted_decl,
                });
            }
        }

        edits
    }

    /// Format a declaration.
    fn format_declaration(&self, decl: &Declaration, indent_level: usize) -> String {
        let _indent = "    ".repeat(indent_level);

        match &decl.kind {
            DeclarationKind::Value(value_decl) => {
                self.format_value_declaration(value_decl, indent_level)
            }
            DeclarationKind::TypeAlias(type_alias) => {
                self.format_type_alias(type_alias, indent_level)
            }
            DeclarationKind::TypeConstructor(type_constructor) => {
                self.format_type_constructor(type_constructor, indent_level)
            }
            DeclarationKind::TypeClass(type_class) => {
                self.format_type_class(type_class, indent_level)
            }
            DeclarationKind::Instance(instance_decl) => {
                self.format_instance_declaration(instance_decl, indent_level)
            }
            DeclarationKind::Import(import) => self.format_import(import, indent_level),
            DeclarationKind::Export(export) => self.format_export(export, indent_level),
        }
    }

    /// Format a value declaration.
    fn format_value_declaration(
        &self,
        value_decl: &ligature_ast::ValueDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("let ");
        formatted.push_str(&value_decl.name);

        if let Some(type_annotation) = &value_decl.type_annotation {
            formatted.push_str(" : ");
            formatted.push_str(&self.format_type(type_annotation));
        }

        formatted.push_str(" = ");
        formatted.push_str(&self.format_expression(&value_decl.value, indent_level));
        formatted.push(';');
        formatted
    }

    /// Format a type alias.
    fn format_type_alias(
        &self,
        type_alias: &ligature_ast::TypeAlias,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("type ");
        formatted.push_str(&type_alias.name);

        if !type_alias.parameters.is_empty() {
            formatted.push(' ');
            formatted.push_str(&type_alias.parameters.join(" "));
        }

        formatted.push_str(" = ");
        formatted.push_str(&self.format_type(&type_alias.type_));
        formatted.push(';');
        formatted
    }

    /// Format a type constructor.
    fn format_type_constructor(
        &self,
        type_constructor: &ligature_ast::TypeConstructor,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("data ");
        formatted.push_str(&type_constructor.name);

        if !type_constructor.parameters.is_empty() {
            formatted.push(' ');
            formatted.push_str(&type_constructor.parameters.join(" "));
        }

        formatted.push_str(" = ");
        formatted.push_str(&self.format_type(&type_constructor.body));

        formatted.push(';');
        formatted
    }

    /// Format a type class.
    fn format_type_class(
        &self,
        type_class: &ligature_ast::TypeClassDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("class ");
        formatted.push_str(&type_class.name);

        if !type_class.parameters.is_empty() {
            formatted.push(' ');
            formatted.push_str(&type_class.parameters.join(" "));
        }

        // TypeClass doesn't have constraints field, skip for now

        formatted.push_str(" where");
        formatted.push('\n');

        for method in &type_class.methods {
            formatted.push_str(&indent);
            formatted.push_str("    ");
            formatted.push_str(&method.name);
            formatted.push_str(" : ");
            formatted.push_str(&self.format_type(&method.type_));
            formatted.push('\n');
        }

        formatted
    }

    /// Format an instance declaration.
    fn format_instance_declaration(
        &self,
        instance_decl: &ligature_ast::InstanceDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("instance ");
        formatted.push_str(&instance_decl.class_name);

        if let Some(constraints) = &instance_decl.constraints {
            if !constraints.is_empty() {
                formatted.push_str(" => ");
                for (i, constraint) in constraints.iter().enumerate() {
                    if i > 0 {
                        formatted.push_str(", ");
                    }
                    formatted.push_str(&self.format_type_class_constraint(constraint));
                }
            }
        }

        formatted.push_str(" where");
        formatted.push('\n');

        for method in &instance_decl.methods {
            formatted.push_str(&indent);
            formatted.push_str("    ");
            formatted.push_str(&method.name);
            formatted.push_str(" = ");
            formatted.push_str(&self.format_expression(&method.implementation, indent_level + 1));
            formatted.push('\n');
        }

        formatted
    }

    /// Format an import.
    fn format_import(&self, import: &ligature_ast::Import, indent_level: usize) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("import ");

        if let Some(alias) = &import.alias {
            formatted.push_str(&import.path);
            formatted.push_str(" as ");
            formatted.push_str(alias);
        } else {
            formatted.push_str(&import.path);
        }

        if let Some(items) = &import.items {
            if !items.is_empty() {
                formatted.push_str(" (");
                let items_str = items
                    .iter()
                    .map(|item| item.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                formatted.push_str(&items_str);
                formatted.push(')');
            }
        }

        formatted.push(';');
        formatted
    }

    /// Format an export.
    fn format_export(
        &self,
        export: &ligature_ast::ExportDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = "    ".repeat(indent_level);
        let mut formatted = String::new();

        formatted.push_str(&indent);
        formatted.push_str("export ");

        for (i, item) in export.items.iter().enumerate() {
            if i > 0 {
                formatted.push_str(", ");
            }
            formatted.push_str(&item.name);
        }

        formatted.push(';');
        formatted
    }

    /// Format an expression.
    fn format_expression(&self, expr: &Expr, indent_level: usize) -> String {
        match &expr.kind {
            ExprKind::Literal(literal) => self.format_literal(literal),
            ExprKind::Variable(name) => name.clone(),
            ExprKind::Application { function, argument } => {
                let func_str = self.format_expression(function, indent_level);
                let arg_str = self.format_expression(argument, indent_level);
                format!("{func_str} {arg_str}")
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                let param_str = if let Some(type_) = parameter_type {
                    format!("({}: {})", parameter, self.format_type(type_))
                } else {
                    parameter.clone()
                };
                let body_str = self.format_expression(body, indent_level);
                format!("\\{param_str} -> {body_str}")
            }
            ExprKind::Let { name, value, body } => {
                let value_str = self.format_expression(value, indent_level);
                let body_str = self.format_expression(body, indent_level);
                format!("let {name} = {value_str} in {body_str}")
            }
            ExprKind::Record { fields } => {
                let fields_str = fields
                    .iter()
                    .map(|field| {
                        format!(
                            "{} = {}",
                            field.name,
                            self.format_expression(&field.value, indent_level)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{fields_str}}}")
            }
            ExprKind::FieldAccess { record, field } => {
                let record_str = self.format_expression(record, indent_level);
                format!("{record_str}.{field}")
            }
            ExprKind::Union { variant, value } => {
                if let Some(value_expr) = value {
                    let value_str = self.format_expression(value_expr, indent_level);
                    format!("({variant} {value_str})")
                } else {
                    variant.clone()
                }
            }
            ExprKind::Match { scrutinee, cases } => {
                let mut formatted = String::new();
                formatted.push_str("match ");
                formatted.push_str(&self.format_expression(scrutinee, indent_level));
                formatted.push_str(" with");

                for case in cases {
                    formatted.push('\n');
                    formatted.push_str(&"    ".repeat(indent_level));
                    formatted.push_str("| ");
                    formatted.push_str(&self.format_pattern(&case.pattern));
                    if let Some(guard) = &case.guard {
                        formatted.push_str(" when ");
                        formatted.push_str(&self.format_expression(guard, indent_level));
                    }
                    formatted.push_str(" -> ");
                    formatted.push_str(&self.format_expression(&case.expression, indent_level + 1));
                }
                formatted
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_str = self.format_expression(condition, indent_level);
                let then_str = self.format_expression(then_branch, indent_level);
                let else_str = self.format_expression(else_branch, indent_level);
                format!("if {condition_str} then {then_str} else {else_str}")
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                let left_str = self.format_expression(left, indent_level);
                let right_str = self.format_expression(right, indent_level);
                let op_str = self.format_binary_operator(operator);
                format!("{left_str} {op_str} {right_str}")
            }
            ExprKind::UnaryOp { operator, operand } => {
                let operand_str = self.format_expression(operand, indent_level);
                let op_str = self.format_unary_operator(operator);
                format!("{op_str}{operand_str}")
            }
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => {
                let expr_str = self.format_expression(expression, indent_level);
                let type_str = self.format_type(type_annotation);
                format!("({expr_str}: {type_str})")
            }
        }
    }

    /// Format a literal.
    fn format_literal(&self, literal: &ligature_ast::Literal) -> String {
        match literal {
            ligature_ast::Literal::Integer(n) => n.to_string(),
            ligature_ast::Literal::Float(f) => f.to_string(),
            ligature_ast::Literal::String(s) => format!("\"{s}\""),
            ligature_ast::Literal::Boolean(b) => b.to_string(),
            ligature_ast::Literal::Unit => "()".to_string(),
            ligature_ast::Literal::List(_) => "[]".to_string(),
        }
    }

    /// Format a type.
    #[allow(clippy::only_used_in_recursion)]
    fn format_type(&self, type_: &ligature_ast::Type) -> String {
        match &type_.kind {
            ligature_ast::TypeKind::Variable(name) => name.clone(),
            ligature_ast::TypeKind::Application { function, argument } => {
                let func_str = self.format_type(function);
                let arg_str = self.format_type(argument);
                format!("{func_str} {arg_str}")
            }
            ligature_ast::TypeKind::Function {
                parameter,
                return_type,
            } => {
                let param_str = self.format_type(parameter);
                let result_str = self.format_type(return_type);
                format!("{param_str} -> {result_str}")
            }
            ligature_ast::TypeKind::Record { fields } => {
                let fields_str = fields
                    .iter()
                    .map(|field| format!("{}: {}", field.name, self.format_type(&field.type_)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{fields_str}}}")
            }
            ligature_ast::TypeKind::List(element_type) => {
                let element_str = self.format_type(element_type);
                format!("[{element_str}]")
            }
            ligature_ast::TypeKind::Unit => "()".to_string(),
            ligature_ast::TypeKind::Bool => "bool".to_string(),
            ligature_ast::TypeKind::String => "string".to_string(),
            ligature_ast::TypeKind::Integer => "int".to_string(),
            ligature_ast::TypeKind::Float => "float".to_string(),
            ligature_ast::TypeKind::Pi { .. } => "pi".to_string(),
            ligature_ast::TypeKind::Sigma { .. } => "sigma".to_string(),
            ligature_ast::TypeKind::Module { .. } => "module".to_string(),
            ligature_ast::TypeKind::Refinement { .. } => "refinement".to_string(),
            ligature_ast::TypeKind::ConstraintType { .. } => "constraint".to_string(),
            ligature_ast::TypeKind::Union { .. } => "union".to_string(),
            ligature_ast::TypeKind::ForAll { .. } => "forall".to_string(),
            ligature_ast::TypeKind::Exists { .. } => "exists".to_string(),
            ligature_ast::TypeKind::Constrained { .. } => "constrained".to_string(),
        }
    }

    /// Format a type class constraint.
    fn format_type_class_constraint(
        &self,
        constraint: &ligature_ast::TypeClassConstraint,
    ) -> String {
        let args_str = constraint
            .type_arguments
            .iter()
            .map(|t| format!("{t:?}"))
            .collect::<Vec<_>>()
            .join(" ");
        format!("{} {}", constraint.class_name, args_str)
    }

    #[allow(dead_code)]
    fn format_constraint(&self, constraint: &ligature_ast::ty::Constraint) -> String {
        match constraint {
            ligature_ast::ty::Constraint::ValueConstraint(expr) => {
                format!("where {}", self.format_expression(expr, 0))
            }
            ligature_ast::ty::Constraint::PatternConstraint { pattern, regex } => {
                if *regex {
                    format!("with regexp(\"{pattern}\")")
                } else {
                    format!("with pattern(\"{pattern}\")")
                }
            }
            ligature_ast::ty::Constraint::RangeConstraint { .. }
            | ligature_ast::ty::Constraint::CustomConstraint { .. }
            | ligature_ast::ty::Constraint::CrossFieldConstraint { .. } => {
                format!("{constraint:?}")
            }
        }
    }

    /// Format a pattern.
    fn format_pattern(&self, pattern: &ligature_ast::Pattern) -> String {
        match pattern {
            ligature_ast::Pattern::Literal(literal) => self.format_literal(literal),
            ligature_ast::Pattern::Variable(name) => name.clone(),
            ligature_ast::Pattern::Record { fields } => {
                let fields_str = fields
                    .iter()
                    .map(|field| {
                        format!("{} = {}", field.name, self.format_pattern(&field.pattern))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{fields_str}}}")
            }
            ligature_ast::Pattern::Union { variant, value } => {
                if let Some(value_pattern) = value {
                    let value_str = self.format_pattern(value_pattern);
                    format!("({variant} {value_str})")
                } else {
                    variant.clone()
                }
            }
            ligature_ast::Pattern::List { elements } => {
                let elements_str = elements
                    .iter()
                    .map(|element| self.format_pattern(element))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{elements_str}]")
            }
            ligature_ast::Pattern::Wildcard => "_".to_string(),
        }
    }

    /// Format a binary operator.
    fn format_binary_operator(&self, op: &ligature_ast::BinaryOperator) -> String {
        match op {
            ligature_ast::BinaryOperator::Add => "+".to_string(),
            ligature_ast::BinaryOperator::Subtract => "-".to_string(),
            ligature_ast::BinaryOperator::Multiply => "*".to_string(),
            ligature_ast::BinaryOperator::Divide => "/".to_string(),
            ligature_ast::BinaryOperator::Modulo => "%".to_string(),
            ligature_ast::BinaryOperator::Equal => "==".to_string(),
            ligature_ast::BinaryOperator::NotEqual => "!=".to_string(),
            ligature_ast::BinaryOperator::LessThan => "<".to_string(),
            ligature_ast::BinaryOperator::LessThanOrEqual => "<=".to_string(),
            ligature_ast::BinaryOperator::GreaterThan => ">".to_string(),
            ligature_ast::BinaryOperator::GreaterThanOrEqual => ">=".to_string(),
            ligature_ast::BinaryOperator::And => "&&".to_string(),
            ligature_ast::BinaryOperator::Or => "||".to_string(),
            ligature_ast::BinaryOperator::Concat => "++".to_string(),
        }
    }

    /// Format a unary operator.
    fn format_unary_operator(&self, op: &ligature_ast::UnaryOperator) -> String {
        match op {
            ligature_ast::UnaryOperator::Not => "!".to_string(),
            ligature_ast::UnaryOperator::Negate => "-".to_string(),
        }
    }

    /// Format basic content without AST analysis.
    fn format_basic(&self, content: &str) -> Vec<TextEdit> {
        let mut edits = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let mut formatted_lines = Vec::new();

        for line in &lines {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                formatted_lines.push(trimmed.to_string());
            }
        }

        let formatted_content = formatted_lines.join("\n");

        edits.push(TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: lines.len() as u32,
                    character: 0,
                },
            },
            new_text: formatted_content,
        });

        edits
    }

    /// Format basic content for a range without AST analysis.
    fn format_basic_range(&self, content: &str, range: Range) -> Vec<TextEdit> {
        let mut edits = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        let mut formatted_lines = Vec::new();
        for line in lines
            .iter()
            .take(end_line.min(lines.len()))
            .skip(start_line)
        {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                formatted_lines.push(trimmed.to_string());
            }
        }

        let formatted_content = formatted_lines.join("\n");

        edits.push(TextEdit {
            range: Range {
                start: Position {
                    line: start_line as u32,
                    character: 0,
                },
                end: Position {
                    line: end_line as u32,
                    character: 0,
                },
            },
            new_text: formatted_content,
        });

        edits
    }

    /// Update the configuration.
    pub fn update_config(&mut self, config: crate::config::FormattingConfig) {
        self.config = config;
    }

    /// Get the current configuration.
    pub fn get_config(&self) -> &crate::config::FormattingConfig {
        &self.config
    }
}

impl Default for FormattingProvider {
    fn default() -> Self {
        Self::new()
    }
}
