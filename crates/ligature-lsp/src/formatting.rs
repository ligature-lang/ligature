//! Formatting provider for the Ligature LSP server.

use crate::config::FormattingConfig;
use ligature_ast::{Declaration, DeclarationKind, Expr, ExprKind, Program};
use lsp_types::{Position, Range, TextEdit};

/// Provider for code formatting.
#[derive(Clone)]
pub struct FormattingProvider {
    /// Configuration for formatting options.
    config: FormattingConfig,
}

impl FormattingProvider {
    /// Create a new formatting provider with default configuration.
    pub fn new() -> Self {
        Self {
            config: crate::config::FormattingConfig::default(),
        }
    }

    /// Create a new formatting provider with custom configuration.
    pub fn with_config(config: crate::config::FormattingConfig) -> Self {
        Self { config }
    }

    /// Format an entire document.
    pub async fn format_document(&self, uri: &str, content: &str) -> Vec<TextEdit> {
        // Try to parse the program for AST-based formatting
        let ast = ligature_parser::parse_program(content).ok();

        if let Some(program) = ast.as_ref() {
            self.format_program(uri, content, program)
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

    /// Format a specific range within a document.
    pub async fn format_range(&self, uri: &str, content: &str, range: Range) -> Vec<TextEdit> {
        // Try to parse the program for AST-based formatting
        let ast = ligature_parser::parse_program(content).ok();

        if let Some(program) = ast.as_ref() {
            self.format_program_range(uri, content, range, program)
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

    /// Format a specific range within a program.
    fn format_program_range(
        &self,
        _uri: &str,
        _content: &str,
        range: Range,
        program: &Program,
    ) -> Vec<TextEdit> {
        let mut edits = Vec::new();

        // Find declarations that overlap with the range
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        for decl in &program.declarations {
            let decl_start_line = decl.span.line;
            let decl_end_line = decl.span.line;

            if decl_start_line >= start_line && decl_end_line <= end_line {
                let formatted_decl = self.format_declaration(decl, 0);
                edits.push(TextEdit {
                    range: Range {
                        start: Position {
                            line: decl_start_line as u32,
                            character: 0,
                        },
                        end: Position {
                            line: decl_end_line as u32,
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
        let _indent = " ".repeat(self.config.indent_size * indent_level);

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
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("let ");
        result.push_str(&value_decl.name);

        if let Some(type_annotation) = &value_decl.type_annotation {
            result.push_str(" : ");
            result.push_str(&self.format_type(type_annotation));
        }

        result.push_str(" = ");
        result.push_str(&self.format_expression(&value_decl.value, indent_level + 1));

        result
    }

    /// Format a type alias.
    fn format_type_alias(
        &self,
        type_alias: &ligature_ast::TypeAlias,
        indent_level: usize,
    ) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("type ");
        result.push_str(&type_alias.name);

        if !type_alias.parameters.is_empty() {
            result.push(' ');
            result.push_str(&type_alias.parameters.join(" "));
        }

        result.push_str(" = ");
        result.push_str(&self.format_type(&type_alias.type_));

        result
    }

    /// Format a type constructor.
    fn format_type_constructor(
        &self,
        type_constructor: &ligature_ast::TypeConstructor,
        indent_level: usize,
    ) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("data ");
        result.push_str(&type_constructor.name);

        if !type_constructor.parameters.is_empty() {
            result.push(' ');
            result.push_str(&type_constructor.parameters.join(" "));
        }

        result.push_str(" = ");
        result.push_str(&self.format_type(&type_constructor.body));

        result
    }

    /// Format a type class.
    fn format_type_class(
        &self,
        type_class: &ligature_ast::TypeClassDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("class ");
        result.push_str(&type_class.name);

        if !type_class.parameters.is_empty() {
            result.push(' ');
            result.push_str(&type_class.parameters.join(" "));
        }

        if !type_class.superclasses.is_empty() {
            result.push_str(" => ");
            result.push_str(
                &type_class
                    .superclasses
                    .iter()
                    .map(|c| c.class_name.as_str())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }

        result.push_str(" where\n");

        for method in &type_class.methods {
            result.push_str(&indent);
            result.push_str("  ");
            result.push_str(&method.name);
            result.push_str(" : ");
            result.push_str(&self.format_type(&method.type_));
            result.push('\n');
        }

        result
    }

    /// Format an instance declaration.
    fn format_instance_declaration(
        &self,
        instance_decl: &ligature_ast::InstanceDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("instance ");
        result.push_str(&instance_decl.class_name);
        result.push(' ');
        result.push_str(
            &instance_decl
                .type_arguments
                .iter()
                .map(|t| self.format_type(t))
                .collect::<Vec<_>>()
                .join(" "),
        );
        result.push_str(" where\n");

        for method in &instance_decl.methods {
            result.push_str(&indent);
            result.push_str("  ");
            result.push_str(&method.name);
            result.push_str(" = ");
            result.push_str(&self.format_expression(&method.implementation, indent_level + 2));
            result.push('\n');
        }

        result
    }

    /// Format an import statement.
    fn format_import(&self, import: &ligature_ast::Import, indent_level: usize) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("import ");
        result.push_str(&import.path);

        if let Some(alias) = &import.alias {
            result.push_str(" as ");
            result.push_str(alias);
        }

        if let Some(items) = &import.items {
            result.push_str(" (");
            result.push_str(
                &items
                    .iter()
                    .map(|item| {
                        if let Some(alias) = &item.alias {
                            format!("{} as {}", item.name, alias)
                        } else {
                            item.name.clone()
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            result.push(')');
        }

        result
    }

    /// Format an export statement.
    fn format_export(
        &self,
        export: &ligature_ast::ExportDeclaration,
        indent_level: usize,
    ) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);
        let mut result = String::new();

        result.push_str(&indent);
        result.push_str("export ");
        result.push_str(
            &export
                .items
                .iter()
                .map(|item| {
                    if let Some(alias) = &item.alias {
                        format!("{} as {}", item.name, alias)
                    } else {
                        item.name.clone()
                    }
                })
                .collect::<Vec<_>>()
                .join(", "),
        );

        result
    }

    /// Format an expression.
    fn format_expression(&self, expr: &Expr, indent_level: usize) -> String {
        let indent = " ".repeat(self.config.indent_size * indent_level);

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
                let mut result = format!("fun {parameter} ");
                if let Some(param_type) = parameter_type {
                    result.push_str(&format!(": {} ", self.format_type(param_type)));
                }
                result.push_str("-> ");
                result.push_str(&self.format_expression(body, indent_level + 1));
                result
            }
            ExprKind::Let { name, value, body } => {
                let mut result = String::new();
                result.push_str("let ");
                result.push_str(name);
                result.push_str(" = ");
                result.push_str(&self.format_expression(value, indent_level + 1));
                result.push_str(" in ");
                result.push_str(&self.format_expression(body, indent_level + 1));
                result
            }
            ExprKind::Record { fields } => {
                let mut result = String::new();
                result.push('{');
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&field.name);
                    result.push_str(" = ");
                    result.push_str(&self.format_expression(&field.value, indent_level));
                }
                result.push('}');
                result
            }
            ExprKind::FieldAccess { record, field } => {
                let record_str = self.format_expression(record, indent_level);
                format!("{record_str}.{field}")
            }
            ExprKind::Union { variant, value } => {
                let mut result = variant.clone();
                if let Some(val) = value {
                    result.push(' ');
                    result.push_str(&self.format_expression(val, indent_level));
                }
                result
            }
            ExprKind::Match { scrutinee, cases } => {
                let mut result = String::new();
                result.push_str("match ");
                result.push_str(&self.format_expression(scrutinee, indent_level));
                result.push_str(" with\n");

                for case in cases {
                    result.push_str(&indent);
                    result.push_str("| ");
                    result.push_str(&self.format_pattern(&case.pattern));
                    if let Some(guard) = &case.guard {
                        result.push_str(" when ");
                        result.push_str(&self.format_expression(guard, indent_level));
                    }
                    result.push_str(" -> ");
                    result.push_str(&self.format_expression(&case.expression, indent_level + 1));
                    result.push('\n');
                }
                result
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut result = String::new();
                result.push_str("if ");
                result.push_str(&self.format_expression(condition, indent_level));
                result.push_str(" then ");
                result.push_str(&self.format_expression(then_branch, indent_level));
                result.push_str(" else ");
                result.push_str(&self.format_expression(else_branch, indent_level));
                result
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
                format!("{expr_str} : {type_str}")
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
            ligature_ast::Literal::List(_) => "[...]".to_string(), // Placeholder for list formatting
        }
    }

    /// Format a type.
    fn format_type(&self, type_: &ligature_ast::Type) -> String {
        match &type_.kind {
            ligature_ast::TypeKind::Unit => "()".to_string(),
            ligature_ast::TypeKind::Bool => "Bool".to_string(),
            ligature_ast::TypeKind::String => "String".to_string(),
            ligature_ast::TypeKind::Integer => "Int".to_string(),
            ligature_ast::TypeKind::Float => "Float".to_string(),
            ligature_ast::TypeKind::Variable(name) => name.clone(),
            ligature_ast::TypeKind::Function {
                parameter,
                return_type,
            } => {
                let param_str = self.format_type(parameter);
                let return_str = self.format_type(return_type);
                format!("{param_str} -> {return_str}")
            }
            ligature_ast::TypeKind::Record { fields } => {
                let mut result = String::new();
                result.push('{');
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&field.name);
                    result.push_str(" : ");
                    result.push_str(&self.format_type(&field.type_));
                }
                result.push('}');
                result
            }
            ligature_ast::TypeKind::Union { variants } => {
                let mut result = String::new();
                for (i, variant) in variants.iter().enumerate() {
                    if i > 0 {
                        result.push_str(" | ");
                    }
                    result.push_str(&variant.name);
                    if let Some(type_) = &variant.type_ {
                        result.push(' ');
                        result.push_str(&self.format_type(type_));
                    }
                }
                result
            }
            ligature_ast::TypeKind::List(element_type) => {
                let element_str = self.format_type(element_type);
                format!("[{element_str}]")
            }
            ligature_ast::TypeKind::ForAll { parameter, body } => {
                let body_str = self.format_type(body);
                format!("forall {parameter}. {body_str}")
            }
            ligature_ast::TypeKind::Exists { parameter, body } => {
                let body_str = self.format_type(body);
                format!("exists {parameter}. {body_str}")
            }
            ligature_ast::TypeKind::Pi {
                parameter,
                parameter_type,
                return_type,
            } => {
                let param_type_str = self.format_type(parameter_type);
                let return_str = self.format_type(return_type);
                format!("Pi {parameter} : {param_type_str}. {return_str}")
            }
            ligature_ast::TypeKind::Sigma {
                parameter,
                parameter_type,
                return_type,
            } => {
                let param_type_str = self.format_type(parameter_type);
                let return_str = self.format_type(return_type);
                format!("Sigma {parameter} : {param_type_str}. {return_str}")
            }
            ligature_ast::TypeKind::Application { function, argument } => {
                let func_str = self.format_type(function);
                let arg_str = self.format_type(argument);
                format!("{func_str} {arg_str}")
            }
            ligature_ast::TypeKind::Module { name } => format!("Module {name}"),
            ligature_ast::TypeKind::Constrained { constraint, type_ } => {
                let constraint_str = self.format_type_class_constraint(constraint);
                let type_str = self.format_type(type_);
                format!("{constraint_str} => {type_str}")
            }
        }
    }

    /// Format a type class constraint.
    fn format_type_class_constraint(
        &self,
        constraint: &ligature_ast::TypeClassConstraint,
    ) -> String {
        let mut result = constraint.class_name.clone();
        if !constraint.type_arguments.is_empty() {
            result.push(' ');
            result.push_str(
                &constraint
                    .type_arguments
                    .iter()
                    .map(|t| self.format_type(t))
                    .collect::<Vec<_>>()
                    .join(" "),
            );
        }
        result
    }

    /// Format a pattern.
    fn format_pattern(&self, pattern: &ligature_ast::Pattern) -> String {
        match pattern {
            ligature_ast::Pattern::Literal(literal) => self.format_literal(literal),
            ligature_ast::Pattern::Variable(name) => name.clone(),
            ligature_ast::Pattern::Union { variant, value } => {
                let mut result = variant.clone();
                if let Some(val) = value {
                    result.push(' ');
                    result.push_str(&self.format_pattern(val));
                }
                result
            }
            ligature_ast::Pattern::Record { fields } => {
                let mut result = String::new();
                result.push('{');
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&field.name);
                    result.push_str(" = ");
                    result.push_str(&self.format_pattern(&field.pattern));
                }
                result.push('}');
                result
            }
            ligature_ast::Pattern::List { .. } => "[...]".to_string(), // Placeholder for list pattern formatting
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
            ligature_ast::UnaryOperator::Negate => "-".to_string(),
            ligature_ast::UnaryOperator::Not => "!".to_string(),
        }
    }

    /// Basic formatting when AST parsing fails.
    fn format_basic(&self, content: &str) -> Vec<TextEdit> {
        let mut formatted = String::new();
        let lines: Vec<&str> = content.lines().collect();

        for (i, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                formatted.push_str(trimmed);
            }
            if i < lines.len() - 1 {
                formatted.push('\n');
            }
        }

        vec![TextEdit {
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
            new_text: formatted,
        }]
    }

    /// Basic formatting for a range when AST parsing fails.
    fn format_basic_range(&self, content: &str, range: Range) -> Vec<TextEdit> {
        let lines: Vec<&str> = content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        let mut formatted = String::new();
        #[allow(clippy::needless_range_loop)]
        for i in start_line..=end_line.min(lines.len() - 1) {
            let trimmed = lines[i].trim();
            if !trimmed.is_empty() {
                formatted.push_str(trimmed);
            }
            if i < end_line {
                formatted.push('\n');
            }
        }

        vec![TextEdit {
            range,
            new_text: formatted,
        }]
    }

    /// Update the formatting configuration.
    pub fn update_config(&mut self, config: crate::config::FormattingConfig) {
        self.config = config;
    }

    /// Get the current formatting configuration.
    pub fn get_config(&self) -> &crate::config::FormattingConfig {
        &self.config
    }
}

impl Default for FormattingProvider {
    fn default() -> Self {
        Self::new()
    }
}
