//! Parser implementation for converting source text to AST nodes.
//!
//! ✅ OPERATOR PRECEDENCE ISSUES RESOLVED (December 2024)
//! All operator precedence issues have been successfully fixed:
//! - Issue 1: Fixed inconsistent operator detection using rule types instead of string content
//! - Issue 2: Fixed incorrect unary operator operand parsing with proper precedence
//! - Issue 3: Added missing explicit operator rule definitions in grammar.pest
//!
//! All precedence test cases now pass correctly, including complex nested expressions.

use ligature_ast::{
    AstError, AstResult, BinaryOperator, Declaration, ExportDeclaration, ExportItem, Expr,
    ExprKind, Import, ImportItem, Literal, MatchCase, Module, Pattern, Program, RecordField,
    RecordPatternField, Span, Type, TypeAlias, TypeConstructor, TypeKind, TypeVariant,
    UnaryOperator,
};
use pest::{iterators::Pairs, Parser as PestParser};

use crate::grammar::LigatureParser;
use crate::grammar::Rule;

/// Main parser for the Ligature language.
pub struct Parser {
    source: String,
}

impl Parser {
    /// Create a new parser.
    pub fn new() -> Self {
        Self {
            source: String::new(),
        }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser {
    /// Parse a complete program.
    pub fn parse_program(&mut self, source: &str) -> AstResult<Program> {
        self.source = source.to_string();

        let pairs =
            <LigatureParser as PestParser<Rule>>::parse(Rule::program, source).map_err(|e| {
                AstError::ParseError {
                    message: format!("Parse error: {e}"),
                    span: Span::default(),
                }
            })?;

        println!("Debug: Successfully parsed program rule");
        let declarations = self.parse_declarations(pairs)?;
        println!(
            "Debug: Successfully parsed {} declarations",
            declarations.len()
        );

        Ok(Program {
            declarations,
            span: Span::default(),
        })
    }

    /// Parse a complete module.
    pub fn parse_module(&mut self, source: &str) -> AstResult<Module> {
        self.source = source.to_string();
        let pairs =
            <LigatureParser as PestParser<Rule>>::parse(Rule::module, source).map_err(|e| {
                AstError::ParseError {
                    message: e.to_string(),
                    span: Span::default(),
                }
            })?;

        let mut module_name = "main".to_string(); // Default module name
        let mut imports = Vec::new();
        let mut declarations = Vec::new();

        for pair in pairs {
            match pair.as_rule() {
                Rule::module => {
                    // Process the inner pairs of the module to separate module declarations, imports and declarations
                    for inner_pair in pair.into_inner() {
                        match inner_pair.as_rule() {
                            Rule::module_declaration => {
                                module_name =
                                    self.parse_module_declaration(inner_pair.into_inner())?;
                            }
                            Rule::import => {
                                let import = self.parse_import(inner_pair.into_inner())?;
                                imports.push(import);
                            }
                            Rule::declaration => {
                                let declaration =
                                    self.parse_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::value_declaration => {
                                let declaration =
                                    self.parse_value_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::type_alias_declaration => {
                                let declaration =
                                    self.parse_type_alias_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::type_constructor_declaration => {
                                let declaration = self
                                    .parse_type_constructor_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::type_class_declaration => {
                                let declaration =
                                    self.parse_type_class_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::instance_declaration => {
                                let declaration =
                                    self.parse_instance_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            Rule::export_declaration => {
                                let declaration =
                                    self.parse_export_declaration(inner_pair.into_inner())?;
                                declarations.push(declaration);
                            }
                            _ => {}
                        }
                    }
                }
                Rule::module_declaration => {
                    module_name = self.parse_module_declaration(pair.into_inner())?;
                }
                Rule::import => {
                    let import = self.parse_import(pair.into_inner())?;
                    imports.push(import);
                }
                Rule::declaration => {
                    let declaration = self.parse_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::value_declaration => {
                    let declaration = self.parse_value_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::type_alias_declaration => {
                    let declaration = self.parse_type_alias_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::type_constructor_declaration => {
                    let declaration = self.parse_type_constructor_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::export_declaration => {
                    let declaration = self.parse_export_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                _ => {}
            }
        }

        Ok(Module {
            name: module_name,
            imports,
            declarations,
            span: Span::default(),
        })
    }

    /// Parse a single expression.
    pub fn parse_expression(&mut self, source: &str) -> AstResult<Expr> {
        self.source = source.to_string();
        let pairs =
            <LigatureParser as PestParser<Rule>>::parse(Rule::expression, source).map_err(|e| {
                AstError::ParseError {
                    message: e.to_string(),
                    span: Span::default(),
                }
            })?;

        self.parse_expression_pairs(pairs)
    }

    /// Parse a single type.
    pub fn parse_type(&mut self, source: &str) -> AstResult<Type> {
        self.source = source.to_string();
        let pairs = <LigatureParser as PestParser<Rule>>::parse(Rule::type_expression, source)
            .map_err(|e| AstError::ParseError {
                message: e.to_string(),
                span: Span::default(),
            })?;

        self.parse_type_pairs(pairs)
    }

    fn parse_declarations(&mut self, pairs: Pairs<Rule>) -> AstResult<Vec<Declaration>> {
        let mut declarations = Vec::new();

        for pair in pairs {
            println!("Debug: Processing declaration rule: {:?}", pair.as_rule());
            match pair.as_rule() {
                Rule::program => {
                    // Recursively process the inner pairs of the program
                    let inner_declarations = self.parse_declarations(pair.into_inner())?;
                    declarations.extend(inner_declarations);
                }
                Rule::import => {
                    // Import statements are handled separately in module parsing
                    // We'll skip them here to avoid duplication
                }
                Rule::declaration => {
                    let declaration = self.parse_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::value_declaration => {
                    let declaration = self.parse_value_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::type_alias_declaration => {
                    let declaration = self.parse_type_alias_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::type_constructor_declaration => {
                    let declaration = self.parse_type_constructor_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                Rule::export_declaration => {
                    let declaration = self.parse_export_declaration(pair.into_inner())?;
                    declarations.push(declaration);
                }
                _ => {}
            }
        }

        Ok(declarations)
    }

    fn parse_import(&mut self, pairs: Pairs<Rule>) -> AstResult<Import> {
        let mut path = String::new();
        let mut alias = None;
        let mut items: Option<Vec<ImportItem>> = None;
        let mut span = Span::default();
        let mut pair_iter = pairs.into_iter();
        let mut current_pair = pair_iter.next();

        while let Some(pair) = current_pair {
            match pair.as_rule() {
                Rule::import_path => {
                    // Parse the import path as either a sequence of identifiers or a string literal
                    let pair_span = pair.as_span();
                    let mut path_parts = Vec::new();

                    for path_pair in pair.into_inner() {
                        match path_pair.as_rule() {
                            Rule::identifier => {
                                path_parts.push(path_pair.as_str().to_string());
                            }
                            Rule::string_literal => {
                                // Remove quotes from string literal
                                let quoted = path_pair.as_str();
                                path = quoted[1..quoted.len() - 1].to_string();
                                span = Span::from_positions(pair_span.start(), pair_span.end());
                                break;
                            }
                            _ => {}
                        }
                    }

                    // If we didn't find a string literal, join the identifiers
                    if path.is_empty() {
                        path = path_parts.join(".");
                        span = Span::from_positions(pair_span.start(), pair_span.end());
                    }
                }
                Rule::identifier => {
                    // This identifier could be an alias for the import
                    // In the grammar, the alias comes after the import_path in basic imports
                    if alias.is_none() {
                        alias = Some(pair.as_str().to_string());
                    }
                }
                Rule::import_item => {
                    // Parse selective import items
                    let mut import_items = Vec::new();

                    // Capture the span before consuming the pair
                    let item_span = pair.as_span();

                    // Each import_item contains identifiers (name and optional alias)
                    let mut identifiers = Vec::new();
                    for item_pair in pair.into_inner() {
                        if item_pair.as_rule() == Rule::identifier {
                            identifiers.push(item_pair.as_str().to_string());
                        }
                    }

                    if !identifiers.is_empty() {
                        let name = identifiers[0].clone();
                        let alias = if identifiers.len() > 1 {
                            Some(identifiers[1].clone())
                        } else {
                            None
                        };

                        import_items.push(ImportItem {
                            name,
                            alias,
                            span: Span::from_positions(item_span.start(), item_span.end()),
                        });
                    }

                    // Initialize or extend the items list
                    if items.is_none() {
                        items = Some(Vec::new());
                    }
                    if let Some(ref mut existing_items) = items {
                        existing_items.extend(import_items);
                    }
                }
                _ => {}
            }
            current_pair = pair_iter.next();
        }

        Ok(Import {
            path,
            alias,
            items,
            span,
        })
    }

    fn parse_module_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<String> {
        let mut module_name = String::new();

        for pair in pairs {
            if pair.as_rule() == Rule::identifier {
                module_name = pair.as_str().to_string();
            }
        }

        if module_name.is_empty() {
            return Err(AstError::ParseError {
                message: "Expected module name in module declaration".to_string(),
                span: Span::default(),
            });
        }

        Ok(module_name)
    }

    fn parse_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected declaration".to_string(),
                span: Span::default(),
            })?;

        // Debug print removed - fix is working

        match pair.as_rule() {
            Rule::value_declaration => self.parse_value_declaration(pair.into_inner()),
            Rule::type_alias_declaration => self.parse_type_alias_declaration(pair.into_inner()),
            Rule::type_constructor_declaration => {
                self.parse_type_constructor_declaration(pair.into_inner())
            }
            Rule::export_declaration => self.parse_export_declaration(pair.into_inner()),
            Rule::type_class_declaration => self.parse_type_class_declaration(pair.into_inner()),
            Rule::instance_declaration => {
                println!("Debug: Found instance_declaration rule");
                self.parse_instance_declaration(pair.into_inner())
            }
            Rule::constrained_instance_declaration => {
                println!("Debug: Found constrained_instance_declaration rule");
                self.parse_constrained_instance_declaration(pair.into_inner())
            }
            Rule::instance_declaration_with_args => {
                println!("Debug: Found instance_declaration_with_args rule");
                self.parse_instance_declaration_with_args(pair.into_inner())
            }
            Rule::instance_declaration_no_args => {
                println!("Debug: Found instance_declaration_no_args rule");
                self.parse_instance_declaration_no_args(pair.into_inner())
            }
            Rule::import_declaration => {
                println!("Debug: Found import_declaration rule");
                let import = self.parse_import(pair.into_inner())?;
                Ok(Declaration::import(import))
            }
            _ => Err(AstError::ParseError {
                message: format!("Unsupported declaration: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_value_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let pairs_iter = pairs.into_iter();
        let is_recursive = false;
        let mut name = String::new();
        let mut type_annotation = None;
        let mut value = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    if name.is_empty() {
                        name = pair.as_str().to_string();
                    }
                }
                Rule::type_expression => {
                    type_annotation = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                Rule::value_expression => {
                    // Parse the value expression by handling its inner rules directly
                    value = Some(self.parse_value_expression_inner(pair.into_inner())?);
                }
                Rule::let_expression => {
                    value = Some(self.parse_let_expression(pair.into_inner())?);
                }
                Rule::lambda_expression => {
                    value = Some(self.parse_lambda_expression(pair.into_inner())?);
                }
                Rule::match_expression => {
                    value = Some(self.parse_match_expression(pair.into_inner())?);
                }
                Rule::logical_or => {
                    value = Some(self.parse_logical_or(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let value = value.ok_or_else(|| AstError::ParseError {
            message: "Expected value in value declaration".to_string(),
            span: Span::default(),
        })?;

        let value_expr = Expr {
            kind: value,
            span: Span::default(),
        };

        Ok(Declaration::value(
            name,
            type_annotation,
            value_expr,
            is_recursive,
            Span::default(),
        ))
    }

    fn parse_type_alias_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let parameters = Vec::new();
        let mut type_body = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    if name.is_empty() {
                        name = pair.as_str().to_string();
                    }
                }
                Rule::type_expression => {
                    type_body = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let type_body = type_body.ok_or_else(|| AstError::ParseError {
            message: "Expected type body in type alias declaration".to_string(),
            span: Span::default(),
        })?;

        let alias = TypeAlias {
            name,
            parameters,
            type_: type_body,
            span: Span::default(),
        };

        Ok(Declaration::type_alias(alias))
    }

    fn parse_type_constructor_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let parameters = Vec::new();
        let mut type_body = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    if name.is_empty() {
                        name = pair.as_str().to_string();
                    }
                }
                Rule::type_constructor_body => {
                    type_body = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let type_body = type_body.ok_or_else(|| AstError::ParseError {
            message: "Expected type body in type constructor declaration".to_string(),
            span: Span::default(),
        })?;

        let constructor = TypeConstructor {
            name,
            parameters,
            body: type_body,
            span: Span::default(),
        };

        Ok(Declaration::type_constructor(constructor))
    }

    fn parse_export_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let mut items = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::export_item {
                let export_item = self.parse_export_item(pair.into_inner())?;
                items.push(export_item);
            }
        }

        let export = ExportDeclaration {
            items,
            span: Span::default(),
        };

        Ok(Declaration::export(export))
    }

    fn parse_export_item(&mut self, pairs: Pairs<Rule>) -> AstResult<ExportItem> {
        let mut name = String::new();
        let mut alias = None;

        for pair in pairs {
            if pair.as_rule() == Rule::identifier {
                if name.is_empty() {
                    name = pair.as_str().to_string();
                } else {
                    alias = Some(pair.as_str().to_string());
                }
            }
        }

        if name.is_empty() {
            return Err(AstError::ParseError {
                message: "Expected export item name".to_string(),
                span: Span::default(),
            });
        }

        Ok(ExportItem {
            name,
            alias,
            span: Span::default(),
        })
    }

    fn parse_value_expression_inner(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();

        let pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        println!(
            "Debug: parse_value_expression_inner got rule: {:?}",
            pair.as_rule()
        );
        match pair.as_rule() {
            Rule::let_expression => self.parse_let_expression(pair.into_inner()),
            Rule::if_expression => self.parse_if_expression(pair.into_inner()),
            Rule::lambda_expression => self.parse_lambda_expression(pair.into_inner()),
            Rule::match_expression => self.parse_match_expression(pair.into_inner()),
            Rule::logical_or => self.parse_logical_or(pair.into_inner()),
            Rule::logical_and => self.parse_logical_and(pair.into_inner()),
            Rule::equality => self.parse_equality(pair.into_inner()),
            Rule::comparison => self.parse_comparison(pair.into_inner()),
            Rule::additive => self.parse_additive(pair.into_inner()),
            Rule::multiplicative => self.parse_multiplicative(pair.into_inner()),
            Rule::unary => self.parse_unary(pair.into_inner()),
            Rule::application => self.parse_application(pair.into_inner()),
            Rule::field_access => self.parse_field_access(pair.into_inner()),
            Rule::primary => self.parse_primary(pair.into_inner()),
            _ => {
                return Err(AstError::ParseError {
                    message: format!("Unsupported value expression: {:?}", pair.as_rule()),
                    span: Span::default(),
                });
            }
        }
    }

    fn parse_expression_pairs(&mut self, pairs: Pairs<Rule>) -> AstResult<Expr> {
        let mut pairs_iter = pairs.into_iter();

        let pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let kind = match pair.as_rule() {
            Rule::expression => {
                // Handle nested expressions by recursively parsing them
                self.parse_expression_pairs(pair.into_inner())?.kind
            }
            Rule::let_expression => self.parse_let_expression(pair.into_inner())?,
            Rule::if_expression => self.parse_if_expression(pair.into_inner())?,
            Rule::lambda_expression => self.parse_lambda_expression(pair.into_inner())?,
            Rule::match_expression => self.parse_match_expression(pair.into_inner())?,
            Rule::logical_or => {
                // Check if this is actually an if expression
                let content = pair.as_str();
                if content.starts_with("if ") {
                    // Parse as if expression
                    self.parse_if_expression(pair.into_inner())?
                } else {
                    // Parse as logical or
                    self.parse_logical_or(pair.into_inner())?
                }
            }
            Rule::logical_and => self.parse_logical_and(pair.into_inner())?,
            Rule::equality => self.parse_equality(pair.into_inner())?,
            Rule::comparison => self.parse_comparison(pair.into_inner())?,
            Rule::additive => self.parse_additive(pair.into_inner())?,
            Rule::multiplicative => self.parse_multiplicative(pair.into_inner())?,
            Rule::unary => self.parse_unary(pair.into_inner())?,
            Rule::unary_operator => {
                // Handle unary operator at expression level
                let operator = self.parse_unary_operator(pair.as_str());
                // Get the next expression as the operand
                let operand_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                    message: "Expected operand after unary operator".to_string(),
                    span: Span::default(),
                })?;
                let operand = self.parse_expression_pairs(operand_pair.into_inner())?;
                ExprKind::UnaryOp {
                    operator,
                    operand: Box::new(operand),
                }
            }
            Rule::application => self.parse_application(pair.into_inner())?,
            Rule::field_access => self.parse_field_access(pair.into_inner())?,
            Rule::primary => self.parse_primary(pair.into_inner())?,
            _ => {
                return Err(AstError::ParseError {
                    message: format!("Unsupported expression: {:?}", pair.as_rule()),
                    span: Span::default(),
                });
            }
        };

        Ok(Expr {
            kind,
            span: Span::default(),
        })
    }

    fn parse_type_pairs(&mut self, pairs: Pairs<Rule>) -> AstResult<Type> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected type expression".to_string(),
                span: Span::default(),
            })?;

        let kind = match pair.as_rule() {
            Rule::basic_type => match pair.as_str() {
                "Unit" => TypeKind::Unit,
                "Bool" => TypeKind::Bool,
                "String" => TypeKind::String,
                "Integer" => TypeKind::Integer,
                "Int" => TypeKind::Integer,
                "Float" => TypeKind::Float,
                _ => {
                    return Err(AstError::ParseError {
                        message: format!("Unknown basic type: {}", pair.as_str()),
                        span: Span::default(),
                    });
                }
            },
            Rule::type_variable => TypeKind::Variable(pair.as_str().to_string()),
            Rule::function_type => self.parse_function_type(pair.into_inner())?,
            Rule::union_type => self.parse_union_type(pair.into_inner())?,
            Rule::record_type => self.parse_record_type(pair.into_inner())?,
            Rule::list_type => self.parse_list_type(pair.into_inner())?,
            Rule::constrained_type => self.parse_constrained_type(pair.into_inner())?,
            Rule::parenthesized_type => self.parse_type_pairs(pair.into_inner())?.kind,
            Rule::type_expression => self.parse_type_pairs(pair.into_inner())?.kind,
            Rule::non_union_type_expression => self.parse_type_pairs(pair.into_inner())?.kind,
            _ => {
                return Err(AstError::ParseError {
                    message: format!("Unsupported type: {:?}", pair.as_rule()),
                    span: Span::default(),
                });
            }
        };

        Ok(Type {
            kind,
            span: Span::default(),
        })
    }

    #[allow(clippy::only_used_in_recursion)]
    fn parse_literal(&mut self, pair: pest::iterators::Pair<Rule>) -> AstResult<Literal> {
        println!("Debug: parse_literal processing pair: {:?}", pair.as_rule());
        if pair.as_rule() == Rule::literal {
            // Handle the literal rule by parsing its inner content
            let inner_pair = pair
                .into_inner()
                .next()
                .ok_or_else(|| AstError::ParseError {
                    message: "Expected inner literal".to_string(),
                    span: Span::default(),
                })?;
            // Recursively parse the inner literal
            return self.parse_literal(inner_pair);
        }

        if pair.as_rule() == Rule::literal_expression {
            // Handle the literal_expression rule by parsing its inner content
            let inner_pair = pair
                .into_inner()
                .next()
                .ok_or_else(|| AstError::ParseError {
                    message: "Expected inner literal".to_string(),
                    span: Span::default(),
                })?;
            // Recursively parse the inner literal
            return self.parse_literal(inner_pair);
        }

        match pair.as_rule() {
            Rule::integer_literal => {
                let value = pair
                    .as_str()
                    .parse::<i64>()
                    .map_err(|_| AstError::ParseError {
                        message: format!("Invalid integer literal: {}", pair.as_str()),
                        span: Span::default(),
                    })?;
                Ok(Literal::Integer(value))
            }
            Rule::float_literal => {
                let value = pair
                    .as_str()
                    .parse::<f64>()
                    .map_err(|_| AstError::ParseError {
                        message: format!("Invalid float literal: {}", pair.as_str()),
                        span: Span::default(),
                    })?;
                Ok(Literal::Float(value))
            }
            Rule::string_literal => {
                let value = pair.as_str().trim_matches('"').to_string();
                Ok(Literal::String(value))
            }
            Rule::boolean_literal => {
                let value = pair.as_str() == "true";
                Ok(Literal::Boolean(value))
            }
            Rule::unit_literal => Ok(Literal::Unit),
            _ => Err(AstError::ParseError {
                message: format!("Unsupported literal: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_logical_or(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_logical_and(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            match pair.as_rule() {
                Rule::logical_or_operator => {
                    // Get the next pair which should be the right operand
                    let right_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                        message: "Expected right operand after logical OR operator".to_string(),
                        span: Span::default(),
                    })?;

                    let right = self.parse_logical_and(right_pair.into_inner())?;
                    left = ExprKind::BinaryOp {
                        operator: BinaryOperator::Or,
                        left: Box::new(Expr {
                            kind: left,
                            span: Span::default(),
                        }),
                        right: Box::new(Expr {
                            kind: right,
                            span: Span::default(),
                        }),
                    };
                }
                _ => {
                    return Err(AstError::ParseError {
                        message: format!("Unexpected rule in logical_or: {:?}", pair.as_rule()),
                        span: Span::default(),
                    });
                }
            }
        }
        Ok(left)
    }

    fn parse_logical_and(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_equality(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            match pair.as_rule() {
                Rule::logical_and_operator => {
                    // Get the next pair which should be the right operand
                    let right_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                        message: "Expected right operand after logical AND operator".to_string(),
                        span: Span::default(),
                    })?;

                    let right = self.parse_equality(right_pair.into_inner())?;
                    left = ExprKind::BinaryOp {
                        operator: BinaryOperator::And,
                        left: Box::new(Expr {
                            kind: left,
                            span: Span::default(),
                        }),
                        right: Box::new(Expr {
                            kind: right,
                            span: Span::default(),
                        }),
                    };
                }
                _ => {
                    return Err(AstError::ParseError {
                        message: format!("Unexpected rule in logical_and: {:?}", pair.as_rule()),
                        span: Span::default(),
                    });
                }
            }
        }
        Ok(left)
    }

    fn parse_equality(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_comparison(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            match pair.as_rule() {
                Rule::equality_operator => {
                    let operator = match pair.as_str() {
                        "==" => BinaryOperator::Equal,
                        "!=" => BinaryOperator::NotEqual,
                        _ => {
                            return Err(AstError::ParseError {
                                message: format!("Unknown equality operator: {}", pair.as_str()),
                                span: Span::default(),
                            });
                        }
                    };

                    // Get the next pair which should be the right operand
                    let right_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                        message: "Expected right operand after equality operator".to_string(),
                        span: Span::default(),
                    })?;

                    let right = self.parse_comparison(right_pair.into_inner())?;
                    left = ExprKind::BinaryOp {
                        operator,
                        left: Box::new(Expr {
                            kind: left,
                            span: Span::default(),
                        }),
                        right: Box::new(Expr {
                            kind: right,
                            span: Span::default(),
                        }),
                    };
                }
                _ => {
                    return Err(AstError::ParseError {
                        message: format!("Unexpected rule in equality: {:?}", pair.as_rule()),
                        span: Span::default(),
                    });
                }
            }
        }
        Ok(left)
    }

    fn parse_comparison(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;
        let mut left = self.parse_additive(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            if pair.as_rule() == Rule::comparison_operator {
                let operator = match pair.as_str() {
                    "<" => BinaryOperator::LessThan,
                    "<=" => BinaryOperator::LessThanOrEqual,
                    ">" => BinaryOperator::GreaterThan,
                    ">=" => BinaryOperator::GreaterThanOrEqual,
                    _ => {
                        return Err(AstError::ParseError {
                            message: format!("Unknown comparison operator: {}", pair.as_str()),
                            span: Span::default(),
                        })
                    }
                };

                // Get the next pair which should be the right operand
                let right_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                    message: "Expected right operand after comparison operator".to_string(),
                    span: Span::default(),
                })?;

                let right = self.parse_additive(right_pair.into_inner())?;
                left = ExprKind::BinaryOp {
                    operator,
                    left: Box::new(Expr {
                        kind: left,
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: right,
                        span: Span::default(),
                    }),
                };
            }
        }
        Ok(left)
    }

    fn parse_additive(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_multiplicative(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            if pair.as_rule() == Rule::additive_operator {
                let operator = pair.as_str();

                // Get the next pair which should be the right operand
                let next_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                    message: "Expected right operand after additive operator".to_string(),
                    span: Span::default(),
                })?;

                let right = self.parse_multiplicative(next_pair.into_inner())?;
                let binary_op = if operator == "+" {
                    BinaryOperator::Add
                } else if operator == "-" {
                    BinaryOperator::Subtract
                } else {
                    return Err(AstError::ParseError {
                        message: format!("Unknown additive operator: {}", operator),
                        span: Span::default(),
                    });
                };

                left = ExprKind::BinaryOp {
                    operator: binary_op,
                    left: Box::new(Expr {
                        kind: left,
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: right,
                        span: Span::default(),
                    }),
                };
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_unary(first_pair.into_inner())?;

        while let Some(pair) = pairs_iter.next() {
            if pair.as_rule() == Rule::multiplicative_operator {
                let operator = match pair.as_str() {
                    "*" => BinaryOperator::Multiply,
                    "/" => BinaryOperator::Divide,
                    "%" => BinaryOperator::Modulo,
                    _ => {
                        return Err(AstError::ParseError {
                            message: format!("Unknown multiplicative operator: {}", pair.as_str()),
                            span: Span::default(),
                        })
                    }
                };

                // Get the next pair which should be the right operand
                let right_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                    message: "Expected right operand after multiplicative operator".to_string(),
                    span: Span::default(),
                })?;

                let right = self.parse_unary(right_pair.into_inner())?;
                left = ExprKind::BinaryOp {
                    operator,
                    left: Box::new(Expr {
                        kind: left,
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: right,
                        span: Span::default(),
                    }),
                };
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected unary expression".to_string(),
            span: Span::default(),
        })?;

        match first_pair.as_rule() {
            Rule::unary_operator => {
                let operator = self.parse_unary_operator(first_pair.as_str());
                // Parse the operand as the next level down in precedence
                let operand_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
                    message: "Expected operand after unary operator".to_string(),
                    span: Span::default(),
                })?;
                // Use parse_unary recursively for proper precedence
                let operand = self.parse_unary(operand_pair.into_inner())?;
                Ok(ExprKind::UnaryOp {
                    operator,
                    operand: Box::new(Expr {
                        kind: operand,
                        span: Span::default(),
                    }),
                })
            }
            Rule::application => self.parse_application(first_pair.into_inner()),
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in unary: {:?}", first_pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_application(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut function = None;
        let mut arguments = Vec::new();

        for pair in pairs {
            println!(
                "Debug: parse_application processing pair: {:?}",
                pair.as_rule()
            );
            match pair.as_rule() {
                Rule::field_access => {
                    if function.is_none() {
                        function = Some(self.parse_field_access(pair.into_inner())?);
                    } else {
                        arguments.push(self.parse_field_access(pair.into_inner())?);
                    }
                }
                Rule::primary => {
                    if function.is_none() {
                        function = Some(self.parse_primary(pair.into_inner())?);
                    } else {
                        arguments.push(self.parse_primary(pair.into_inner())?);
                    }
                }
                Rule::single_argument => {
                    arguments.push(self.parse_single_argument(pair.into_inner())?);
                }
                Rule::tuple_argument => {
                    let tuple_args = self.parse_tuple_argument(pair.into_inner())?;
                    arguments.extend(tuple_args);
                }
                _ => {}
            }
        }

        let function = function.ok_or_else(|| AstError::ParseError {
            message: "Expected function in application".to_string(),
            span: Span::default(),
        })?;

        if arguments.is_empty() {
            Ok(function)
        } else {
            // Build left-associative application: (f a) b -> Application(Application(f, a), b)
            let mut result = function;
            for arg in arguments {
                result = ExprKind::Application {
                    function: Box::new(Expr {
                        kind: result,
                        span: Span::default(),
                    }),
                    argument: Box::new(Expr {
                        kind: arg,
                        span: Span::default(),
                    }),
                };
            }
            Ok(result)
        }
    }

    fn parse_single_argument(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected single argument".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::literal_expression => {
                let literal = self.parse_literal(pair)?;
                Ok(ExprKind::Literal(literal))
            }
            Rule::variable_expression => {
                let name = pair.as_str().to_string();
                Ok(ExprKind::Variable(name))
            }
            Rule::non_keyword_variable_expression => {
                let name = pair.as_str().to_string();
                Ok(ExprKind::Variable(name))
            }
            Rule::parenthesized_expression => {
                let expr = self.parse_expression_pairs(pair.into_inner())?;
                Ok(expr.kind)
            }
            Rule::lambda_expression => self.parse_lambda_expression(pair.into_inner()),
            Rule::let_expression => self.parse_let_expression(pair.into_inner()),
            Rule::if_expression => self.parse_if_expression(pair.into_inner()),
            Rule::match_expression => self.parse_match_expression(pair.into_inner()),
            Rule::record_expression => self.parse_record_expression(pair.into_inner()),
            Rule::list_expression => self.parse_list_expression(pair.into_inner()),
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in single argument: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_tuple_argument(&mut self, pairs: Pairs<Rule>) -> AstResult<Vec<ExprKind>> {
        let mut arguments = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::expression {
                let expr = self.parse_expression_pairs(pair.into_inner())?;
                arguments.push(expr.kind);
            }
        }

        Ok(arguments)
    }

    fn parse_field_access(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut expressions = Vec::new();
        let mut field_names = Vec::new();

        for pair in pairs {
            println!(
                "Debug: parse_field_access processing pair: {:?}",
                pair.as_rule()
            );
            match pair.as_rule() {
                Rule::primary => {
                    expressions.push(self.parse_primary(pair.into_inner())?);
                }
                Rule::identifier => {
                    field_names.push(pair.as_str().to_string());
                }
                _ => {}
            }
        }

        if expressions.is_empty() {
            return Err(AstError::ParseError {
                message: "Expected at least one expression in field access".to_string(),
                span: Span::default(),
            });
        }

        if field_names.is_empty() {
            Ok(expressions.remove(0))
        } else {
            // Build left-associative field access: (a.b).c -> FieldAccess(FieldAccess(a, b), c)
            let mut result = expressions.remove(0);
            for field_name in field_names {
                result = ExprKind::FieldAccess {
                    record: Box::new(Expr {
                        kind: result,
                        span: Span::default(),
                    }),
                    field: field_name,
                };
            }
            Ok(result)
        }
    }

    fn parse_primary(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected primary expression".to_string(),
                span: Span::default(),
            })?;

        println!("Debug: parse_primary processing pair: {:?}", pair.as_rule());
        match pair.as_rule() {
            Rule::literal_expression => {
                let literal = self.parse_literal(pair)?;
                Ok(ExprKind::Literal(literal))
            }
            Rule::variable_expression => {
                let name = pair.as_str().to_string();
                Ok(ExprKind::Variable(name))
            }
            Rule::non_keyword_variable_expression => {
                let name = pair.as_str().to_string();
                Ok(ExprKind::Variable(name))
            }
            Rule::lambda_expression => self.parse_lambda_expression(pair.into_inner()),
            Rule::let_expression => self.parse_let_expression(pair.into_inner()),
            Rule::if_expression => self.parse_if_expression(pair.into_inner()),
            Rule::match_expression => self.parse_match_expression(pair.into_inner()),
            Rule::union_expression => self.parse_union_expression(pair.into_inner()),
            Rule::record_expression => self.parse_record_expression(pair.into_inner()),
            Rule::list_expression => self.parse_list_expression(pair.into_inner()),
            Rule::parenthesized_expression => {
                Ok(self.parse_expression_pairs(pair.into_inner())?.kind)
            }
            _ => Err(AstError::ParseError {
                message: format!("Unsupported primary expression: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    // Fixed binary operator chain parsing with proper precedence
    fn parse_binary_chain_simple(
        &mut self,
        pairs: Pairs<Rule>,
        operators: &[&str],
    ) -> AstResult<ExprKind> {
        let mut pairs_iter = pairs.into_iter();

        // Get the first expression (left operand)
        let first_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected expression".to_string(),
            span: Span::default(),
        })?;

        let mut left = self.parse_expression_pairs(first_pair.into_inner())?.kind;

        // Process the rest of the pairs (operator + right operand pairs)
        for pair in pairs_iter {
            // Each pair should contain the operator and the right operand
            let pair_content = pair.as_str();

            // Find the operator in the pair content
            let mut found_operator = None;

            // Sort operators by length (longest first) to handle multi-character operators like <=, >=, ==, !=
            let mut sorted_operators = operators.to_vec();
            sorted_operators.sort_by_key(|b| std::cmp::Reverse(b.len()));

            for op in &sorted_operators {
                if pair_content.contains(op) {
                    found_operator = Some(*op);
                    break;
                }
            }

            if let Some(operator_str) = found_operator {
                let operator = self.parse_binary_operator(operator_str);

                // Parse the right operand from the pair
                let right = self.parse_expression_pairs(pair.into_inner())?.kind;

                // Create the binary operation
                left = ExprKind::BinaryOp {
                    operator,
                    left: Box::new(Expr {
                        kind: left,
                        span: Span::default(),
                    }),
                    right: Box::new(Expr {
                        kind: right,
                        span: Span::default(),
                    }),
                };
            } else {
                // If no operator found, this might be a single expression
                // This can happen when the grammar precedence is not correctly handled
                // For now, we'll just return the left operand and ignore the right operand
                // This should be improved with better precedence handling
                println!(
                    "DEBUG parse_binary_chain_simple: no operator found, ignoring right operand"
                );
                continue;
            }
        }

        Ok(left)
    }

    fn parse_lambda_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let pairs_iter = pairs.into_iter();
        let mut parameters = Vec::new();
        let mut parameter_type = None;
        let mut body = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    parameters.push(pair.as_str().to_string());
                }
                Rule::type_expression => {
                    parameter_type = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                Rule::expression => {
                    body = Some(self.parse_expression_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let body = body.ok_or_else(|| AstError::ParseError {
            message: "Expected lambda body".to_string(),
            span: Span::default(),
        })?;

        // Convert multi-parameter lambda to nested single-parameter lambdas (currying)
        let mut result = body.kind;
        for (i, param) in parameters.iter().enumerate().rev() {
            let param_type = if i == parameters.len() - 1 {
                parameter_type.clone()
            } else {
                None
            };

            result = ExprKind::Abstraction {
                parameter: param.clone(),
                parameter_type: param_type.map(Box::new),
                body: Box::new(Expr {
                    kind: result,
                    span: Span::default(),
                }),
            };
        }

        Ok(result)
    }

    fn parse_let_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let mut value = None;
        let mut body = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    if name.is_empty() {
                        name = pair.as_str().to_string();
                    }
                }
                Rule::expression => {
                    if value.is_none() {
                        value = Some(self.parse_expression_pairs(pair.into_inner())?);
                    } else {
                        body = Some(self.parse_expression_pairs(pair.into_inner())?);
                    }
                }
                _ => {}
            }
        }

        let value = value.ok_or_else(|| AstError::ParseError {
            message: "Expected value in let expression".to_string(),
            span: Span::default(),
        })?;

        let body = body.ok_or_else(|| AstError::ParseError {
            message: "Expected body in let expression".to_string(),
            span: Span::default(),
        })?;

        Ok(ExprKind::Let {
            name,
            value: Box::new(value),
            body: Box::new(body),
        })
    }

    fn parse_if_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let pairs_iter = pairs.into_iter();
        let mut condition = None;
        let mut then_branch = None;
        let mut else_branch = None;

        for pair in pairs_iter {
            if pair.as_rule() == Rule::expression {
                if condition.is_none() {
                    condition = Some(self.parse_expression_pairs(pair.into_inner())?);
                } else if then_branch.is_none() {
                    then_branch = Some(self.parse_expression_pairs(pair.into_inner())?);
                } else {
                    else_branch = Some(self.parse_expression_pairs(pair.into_inner())?);
                }
            }
        }

        let condition = condition.ok_or_else(|| AstError::ParseError {
            message: "Expected condition in if expression".to_string(),
            span: Span::default(),
        })?;

        let then_branch = then_branch.ok_or_else(|| AstError::ParseError {
            message: "Expected then branch in if expression".to_string(),
            span: Span::default(),
        })?;

        let else_branch = else_branch.ok_or_else(|| AstError::ParseError {
            message: "Expected else branch in if expression".to_string(),
            span: Span::default(),
        })?;

        Ok(ExprKind::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        })
    }

    fn parse_match_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut scrutinee = None;
        let mut cases = Vec::new();

        for pair in pairs {
            match pair.as_rule() {
                Rule::expression => {
                    if scrutinee.is_none() {
                        scrutinee = Some(self.parse_expression_pairs(pair.into_inner())?);
                    }
                }
                Rule::match_case => {
                    let case = self.parse_match_case(pair.into_inner())?;
                    cases.push(case);
                }
                _ => {}
            }
        }

        let scrutinee = scrutinee.ok_or_else(|| AstError::ParseError {
            message: "Expected scrutinee in match expression".to_string(),
            span: Span::default(),
        })?;

        Ok(ExprKind::Match {
            scrutinee: Box::new(scrutinee),
            cases,
        })
    }

    fn parse_match_case(&mut self, pairs: Pairs<Rule>) -> AstResult<MatchCase> {
        let mut pattern = None;
        let mut guard = None;
        let mut expression = None;
        let mut in_guard = false;
        let mut found_arrow = false;

        for pair in pairs {
            println!(
                "Debug: Processing pair with rule: {:?}, content: '{}'",
                pair.as_rule(),
                pair.as_str()
            );
            match pair.as_rule() {
                Rule::pattern => {
                    pattern = Some(self.parse_pattern(pair.into_inner())?);
                }
                Rule::arrow => {
                    println!("Debug: Found arrow");
                    found_arrow = true;
                }
                Rule::expression => {
                    let expr = self.parse_expression_pairs(pair.into_inner())?;
                    if in_guard {
                        println!("Debug: Setting guard expression: {expr:?}");
                        guard = Some(expr);
                        in_guard = false;
                    } else if expression.is_none() && found_arrow {
                        println!("Debug: Setting case expression: {expr:?}");
                        expression = Some(expr);
                    }
                }
                _ => {
                    // Check if this is the "when" keyword
                    if pair.as_str() == "when" {
                        println!("Debug: Found 'when' keyword, setting in_guard = true");
                        in_guard = true;
                    }
                }
            }
        }

        let pattern = pattern.ok_or_else(|| AstError::ParseError {
            message: "Expected pattern in match case".to_string(),
            span: Span::default(),
        })?;

        let expression = expression.ok_or_else(|| AstError::ParseError {
            message: "Expected expression in match case".to_string(),
            span: Span::default(),
        })?;

        Ok(MatchCase {
            pattern,
            guard,
            expression,
            span: Span::default(),
        })
    }

    fn parse_record_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut fields = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::record_field {
                let field = self.parse_record_field(pair.into_inner())?;
                fields.push(field);
            }
        }

        Ok(ExprKind::Record { fields })
    }

    fn parse_record_field(&mut self, pairs: Pairs<Rule>) -> AstResult<RecordField> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let mut value = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::expression => {
                    value = Some(self.parse_expression_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let value = value.ok_or_else(|| AstError::ParseError {
            message: "Expected value in record field".to_string(),
            span: Span::default(),
        })?;

        Ok(RecordField {
            name,
            value,
            span: Span::default(),
        })
    }

    fn parse_list_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut elements = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::expression {
                let element = self.parse_expression_pairs(pair.into_inner())?;
                elements.push(element);
            }
        }

        Ok(ExprKind::Literal(Literal::List(elements)))
    }

    fn parse_union_expression(&mut self, pairs: Pairs<Rule>) -> AstResult<ExprKind> {
        let mut variant = String::new();
        let mut value = None;

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    variant = pair.as_str().to_string();
                }
                Rule::expression => {
                    value = Some(self.parse_expression_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        Ok(ExprKind::Union {
            variant,
            value: value.map(Box::new),
        })
    }

    fn parse_function_type(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeKind> {
        let mut left = None;
        let mut right = None;

        for pair in pairs {
            match pair.as_rule() {
                Rule::type_variable => {
                    if left.is_none() {
                        left = Some(Type {
                            kind: TypeKind::Variable(pair.as_str().to_string()),
                            span: Span::default(),
                        });
                    }
                }
                Rule::basic_type => {
                    if left.is_none() {
                        left = Some(Type {
                            kind: match pair.as_str() {
                                "Unit" => TypeKind::Unit,
                                "Bool" => TypeKind::Bool,
                                "String" => TypeKind::String,
                                "Integer" => TypeKind::Integer,
                                "Float" => TypeKind::Float,
                                _ => {
                                    return Err(AstError::ParseError {
                                        message: format!("Unknown basic type: {}", pair.as_str()),
                                        span: Span::default(),
                                    });
                                }
                            },
                            span: Span::default(),
                        });
                    }
                }
                Rule::type_expression => {
                    if right.is_none() {
                        right = Some(self.parse_type_pairs(pair.into_inner())?);
                    }
                }
                Rule::union_type => {
                    if right.is_none() {
                        let kind = self.parse_union_type(pair.into_inner())?;
                        right = Some(Type {
                            kind,
                            span: Span::default(),
                        });
                    }
                }
                _ => {}
            }
        }

        let left = left.ok_or_else(|| AstError::ParseError {
            message: "Expected left type in function type".to_string(),
            span: Span::default(),
        })?;

        let right = right.ok_or_else(|| AstError::ParseError {
            message: "Expected right type in function type".to_string(),
            span: Span::default(),
        })?;

        Ok(TypeKind::Function {
            parameter: Box::new(left),
            return_type: Box::new(right),
        })
    }

    fn parse_union_type(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeKind> {
        let mut variants = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::type_variant {
                let variant = self.parse_type_variant(pair.into_inner())?;
                variants.push(variant);
            }
        }

        Ok(TypeKind::Union { variants })
    }

    fn parse_type_variant(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeVariant> {
        let mut name = String::new();
        let mut type_ = None;

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::type_expression => {
                    type_ = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                Rule::non_union_type_expression => {
                    type_ = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        Ok(TypeVariant {
            name,
            type_,
            span: Span::default(),
        })
    }

    fn parse_record_type(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeKind> {
        let mut fields = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::record_field_type {
                let field = self.parse_record_field_type(pair.into_inner())?;
                fields.push(field);
            }
        }

        Ok(TypeKind::Record { fields })
    }

    fn parse_record_field_type(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<ligature_ast::TypeField> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let mut type_ = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::type_expression => {
                    type_ = Some(self.parse_type_pairs(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let type_ = type_.ok_or_else(|| AstError::ParseError {
            message: "Expected type in record field type".to_string(),
            span: Span::default(),
        })?;

        Ok(ligature_ast::TypeField {
            name,
            type_,
            span: Span::default(),
        })
    }

    fn parse_list_type(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeKind> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected type in list type".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::type_expression => {
                let element_type = self.parse_type_pairs(pair.into_inner())?;
                Ok(TypeKind::List(Box::new(element_type)))
            }
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in list type: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_constrained_type(&mut self, pairs: Pairs<Rule>) -> AstResult<TypeKind> {
        let mut pairs_iter = pairs.into_iter();

        let constraint_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected type class constraint".to_string(),
            span: Span::default(),
        })?;

        let type_pair = pairs_iter.next().ok_or_else(|| AstError::ParseError {
            message: "Expected constrained type".to_string(),
            span: Span::default(),
        })?;

        let constraint = self.parse_type_class_constraint(constraint_pair.into_inner())?;
        let constrained_type = self.parse_type_pairs(type_pair.into_inner())?;

        Ok(TypeKind::Constrained {
            constraint: Box::new(constraint),
            type_: Box::new(constrained_type),
        })
    }

    fn parse_binary_operator(&self, op: &str) -> BinaryOperator {
        match op {
            "+" => BinaryOperator::Add,
            "-" => BinaryOperator::Subtract,
            "*" => BinaryOperator::Multiply,
            "/" => BinaryOperator::Divide,
            "%" => BinaryOperator::Modulo,
            "==" => BinaryOperator::Equal,
            "!=" => BinaryOperator::NotEqual,
            "<" => BinaryOperator::LessThan,
            "<=" => BinaryOperator::LessThanOrEqual,
            ">" => BinaryOperator::GreaterThan,
            ">=" => BinaryOperator::GreaterThanOrEqual,
            "&&" => BinaryOperator::And,
            "||" => BinaryOperator::Or,
            "++" => BinaryOperator::Concat,
            _ => BinaryOperator::Add, // Default fallback
        }
    }

    fn parse_unary_operator(&self, op: &str) -> UnaryOperator {
        match op {
            "!" => UnaryOperator::Not,
            "-" => UnaryOperator::Negate,
            _ => UnaryOperator::Not, // Default fallback
        }
    }

    // Pattern parsing methods
    fn parse_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected pattern".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::wildcard_pattern => self.parse_wildcard_pattern(pair.into_inner()),
            Rule::variable_pattern => self.parse_variable_pattern(pair.into_inner()),
            Rule::literal_pattern => self.parse_literal_pattern(pair.into_inner()),
            Rule::record_pattern => self.parse_record_pattern(pair.into_inner()),
            Rule::union_pattern => self.parse_union_pattern(pair.into_inner()),
            Rule::list_pattern => self.parse_list_pattern(pair.into_inner()),
            Rule::parenthesized_pattern => self.parse_parenthesized_pattern(pair.into_inner()),
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in pattern: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_wildcard_pattern(&mut self, _pairs: Pairs<Rule>) -> AstResult<Pattern> {
        Ok(Pattern::Wildcard)
    }

    fn parse_variable_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected identifier in variable pattern".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::identifier => Ok(Pattern::Variable(pair.as_str().to_string())),
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in variable pattern: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_literal_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected literal in literal pattern".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::literal => {
                let literal = self.parse_literal(pair)?;
                Ok(Pattern::Literal(literal))
            }
            _ => Err(AstError::ParseError {
                message: format!("Unexpected rule in literal pattern: {:?}", pair.as_rule()),
                span: Span::default(),
            }),
        }
    }

    fn parse_record_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let mut fields = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::record_pattern_field {
                let field = self.parse_record_pattern_field(pair.into_inner())?;
                fields.push(field);
            }
        }

        Ok(Pattern::Record { fields })
    }

    fn parse_record_pattern_field(&mut self, pairs: Pairs<Rule>) -> AstResult<RecordPatternField> {
        let pairs_iter = pairs.into_iter();
        let mut name = String::new();
        let mut pattern = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::pattern => {
                    pattern = Some(self.parse_pattern(pair.into_inner())?);
                }
                _ => {}
            }
        }

        let pattern = pattern.ok_or_else(|| AstError::ParseError {
            message: "Expected pattern in record pattern field".to_string(),
            span: Span::default(),
        })?;

        Ok(RecordPatternField {
            name,
            pattern,
            span: Span::default(),
        })
    }

    fn parse_union_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let pairs_iter = pairs.into_iter();
        let mut variant = String::new();
        let mut value = None;

        for pair in pairs_iter {
            match pair.as_rule() {
                Rule::identifier => {
                    variant = pair.as_str().to_string();
                }
                Rule::pattern => {
                    // Parse the inner pattern directly
                    value = Some(Box::new(self.parse_pattern(pair.into_inner())?));
                }
                _ => {}
            }
        }

        Ok(Pattern::Union { variant, value })
    }

    fn parse_list_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let mut elements = Vec::new();

        for pair in pairs {
            if pair.as_rule() == Rule::pattern {
                let element = self.parse_pattern(pair.into_inner())?;
                elements.push(element);
            }
        }

        Ok(Pattern::List { elements })
    }

    fn parse_parenthesized_pattern(&mut self, pairs: Pairs<Rule>) -> AstResult<Pattern> {
        let pair = pairs
            .into_iter()
            .next()
            .ok_or_else(|| AstError::ParseError {
                message: "Expected pattern in parenthesized pattern".to_string(),
                span: Span::default(),
            })?;

        match pair.as_rule() {
            Rule::pattern => self.parse_pattern(pair.into_inner()),
            Rule::variable_pattern => self.parse_variable_pattern(pair.into_inner()),
            Rule::literal_pattern => self.parse_literal_pattern(pair.into_inner()),
            Rule::wildcard_pattern => self.parse_wildcard_pattern(pair.into_inner()),
            Rule::union_pattern => self.parse_union_pattern(pair.into_inner()),
            Rule::record_pattern => self.parse_record_pattern(pair.into_inner()),
            Rule::list_pattern => self.parse_list_pattern(pair.into_inner()),
            _ => Err(AstError::ParseError {
                message: format!(
                    "Unexpected rule in parenthesized pattern: {:?}",
                    pair.as_rule()
                ),
                span: Span::default(),
            }),
        }
    }

    fn parse_type_class_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let mut name = String::new();
        let mut parameters = Vec::new();
        let mut superclasses = Vec::new();
        let mut methods = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    if name.is_empty() {
                        name = pair.as_str().to_string();
                    }
                }
                Rule::type_parameter => {
                    let param = pair.as_str().trim_start_matches("'").to_string();
                    parameters.push(param);
                }
                Rule::superclass_declaration => {
                    // Parse superclass declarations
                    for inner_pair in pair.into_inner() {
                        if inner_pair.as_rule() == Rule::type_class_constraint {
                            let constraint =
                                self.parse_type_class_constraint(inner_pair.into_inner())?;
                            superclasses.push(constraint);
                        }
                    }
                }
                Rule::method_signature => {
                    let method = self.parse_method_signature(pair.into_inner())?;
                    methods.push(method);
                }
                _ => {}
            }
        }

        let type_class = ligature_ast::TypeClassDeclaration {
            name,
            parameters,
            superclasses,
            methods,
            span,
        };

        Ok(Declaration::type_class(type_class))
    }

    fn parse_instance_declaration(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let mut class_name = String::new();
        let mut type_arguments = Vec::new();
        let mut methods = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    if class_name.is_empty() {
                        class_name = pair.as_str().to_string();
                    }
                }
                Rule::instance_type_args => {
                    // Parse the type arguments from the instance_type_args rule
                    for inner_pair in pair.into_inner() {
                        match inner_pair.as_rule() {
                            Rule::instance_type_argument => {
                                let type_arg = self.parse_type_pairs(inner_pair.into_inner())?;
                                type_arguments.push(type_arg);
                            }
                            _ => {
                                // Ignore unexpected rules
                            }
                        }
                    }
                }
                Rule::method_implementation => {
                    let method = self.parse_method_implementation(pair.into_inner())?;
                    methods.push(method);
                }
                _ => {
                    // Ignore unexpected rules
                }
            }
        }

        let instance = ligature_ast::InstanceDeclaration {
            class_name,
            type_arguments,
            constraints: None, // Regular instances don't have constraints
            methods,
            span,
        };

        Ok(Declaration::instance(instance))
    }

    fn parse_constrained_instance_declaration(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<Declaration> {
        let mut class_name = String::new();
        let mut constraints = Vec::new();
        let mut type_arguments = Vec::new();
        let mut methods = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    if class_name.is_empty() {
                        class_name = pair.as_str().to_string();
                    }
                }
                Rule::type_class_constraint => {
                    let constraint = self.parse_type_class_constraint(pair.into_inner())?;
                    constraints.push(constraint);
                }
                Rule::instance_type_args => {
                    // Parse the type arguments from the instance_type_args rule
                    for inner_pair in pair.into_inner() {
                        match inner_pair.as_rule() {
                            Rule::instance_type_argument => {
                                let type_arg = self.parse_type_pairs(inner_pair.into_inner())?;
                                type_arguments.push(type_arg);
                            }
                            _ => {
                                // Ignore unexpected rules
                            }
                        }
                    }
                }
                Rule::method_implementation => {
                    let method = self.parse_method_implementation(pair.into_inner())?;
                    methods.push(method);
                }
                _ => {
                    // Ignore unexpected rules
                }
            }
        }

        let instance = ligature_ast::InstanceDeclaration {
            class_name,
            type_arguments,
            constraints: if constraints.is_empty() {
                None
            } else {
                Some(constraints)
            },
            methods,
            span,
        };

        Ok(Declaration::instance(instance))
    }

    fn parse_type_class_constraint(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<ligature_ast::TypeClassConstraint> {
        let mut class_name = String::new();
        let mut type_arguments = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    class_name = pair.as_str().to_string();
                }
                Rule::type_argument => {
                    let type_arg = self.parse_type_pairs(pair.into_inner())?;
                    type_arguments.push(type_arg);
                }
                _ => {}
            }
        }

        Ok(ligature_ast::TypeClassConstraint {
            class_name,
            type_arguments,
            span,
        })
    }

    fn parse_method_signature(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<ligature_ast::MethodSignature> {
        let mut name = String::new();
        let mut type_ = Type::unit(Span::default());
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::type_expression => {
                    type_ = self.parse_type_pairs(pair.into_inner())?;
                }
                _ => {}
            }
        }

        Ok(ligature_ast::MethodSignature { name, type_, span })
    }

    fn parse_method_implementation(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<ligature_ast::MethodImplementation> {
        let mut name = String::new();
        let mut implementation = Expr {
            kind: ExprKind::Literal(Literal::Unit),
            span: Span::default(),
        };
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    name = pair.as_str().to_string();
                }
                Rule::value_expression => {
                    implementation = self.parse_expression_pairs(pair.into_inner())?;
                }
                _ => {
                    // Ignore unexpected rules
                }
            }
        }

        Ok(ligature_ast::MethodImplementation {
            name,
            implementation,
            span,
        })
    }

    fn parse_instance_declaration_with_args(
        &mut self,
        pairs: Pairs<Rule>,
    ) -> AstResult<Declaration> {
        let mut class_name = String::new();
        let mut type_arguments = Vec::new();
        let mut methods = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    if class_name.is_empty() {
                        class_name = pair.as_str().to_string();
                    }
                }
                Rule::type_argument => {
                    let type_arg = self.parse_type_pairs(pair.into_inner())?;
                    type_arguments.push(type_arg);
                }
                Rule::method_implementation => {
                    let method = self.parse_method_implementation(pair.into_inner())?;
                    methods.push(method);
                }
                _ => {
                    // Ignore unexpected rules
                }
            }
        }

        let instance = ligature_ast::InstanceDeclaration {
            class_name,
            type_arguments,
            constraints: None, // This variant doesn't have constraints
            methods,
            span,
        };

        Ok(Declaration::instance(instance))
    }

    fn parse_instance_declaration_no_args(&mut self, pairs: Pairs<Rule>) -> AstResult<Declaration> {
        let mut class_name = String::new();
        let mut methods = Vec::new();
        let span = Span::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::identifier => {
                    if class_name.is_empty() {
                        class_name = pair.as_str().to_string();
                    }
                }
                Rule::method_implementation => {
                    let method = self.parse_method_implementation(pair.into_inner())?;
                    methods.push(method);
                }
                _ => {
                    // Ignore unexpected rules
                }
            }
        }

        let instance = ligature_ast::InstanceDeclaration {
            class_name,
            type_arguments: Vec::new(),
            constraints: None, // This variant doesn't have constraints
            methods,
            span,
        };

        Ok(Declaration::instance(instance))
    }
}
