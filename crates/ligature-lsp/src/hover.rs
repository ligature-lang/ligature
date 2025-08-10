//! Hover provider for the Ligature LSP server.

use std::collections::HashMap;

use ligature_ast::{
    DeclarationKind, Expr, ExprKind, Program, TypeAlias, TypeConstructor, ValueDeclaration,
};
use lsp_types::{Hover, HoverContents, MarkedString, Position};

use crate::async_evaluation::{AsyncEvaluationConfig, AsyncEvaluationService};

/// Provider for hover information.
#[derive(Clone)]
pub struct HoverProvider {
    /// Built-in functions and their documentation.
    builtins: HashMap<&'static str, BuiltinInfo>,
    /// Built-in types and their documentation.
    builtin_types: HashMap<&'static str, &'static str>,
    /// Async evaluation service for evaluation-based hover information.
    async_evaluation: Option<AsyncEvaluationService>,
}

/// Information about a built-in function.
#[derive(Debug, Clone)]
struct BuiltinInfo {
    signature: String,
    documentation: String,
    examples: Vec<String>,
}

impl HoverProvider {
    /// Create a new hover provider.
    pub fn new() -> Self {
        let mut builtins = HashMap::new();
        builtins.insert(
            "add",
            BuiltinInfo {
                signature: "add : Int -> Int -> Int".to_string(),
                documentation: "Adds two integers together.".to_string(),
                examples: vec!["add 5 3 = 8".to_string()],
            },
        );
        builtins.insert(
            "sub",
            BuiltinInfo {
                signature: "sub : Int -> Int -> Int".to_string(),
                documentation: "Subtracts the second integer from the first.".to_string(),
                examples: vec!["sub 5 3 = 2".to_string()],
            },
        );
        builtins.insert(
            "mul",
            BuiltinInfo {
                signature: "mul : Int -> Int -> Int".to_string(),
                documentation: "Multiplies two integers.".to_string(),
                examples: vec!["mul 5 3 = 15".to_string()],
            },
        );
        builtins.insert(
            "div",
            BuiltinInfo {
                signature: "div : Int -> Int -> Int".to_string(),
                documentation: "Divides the first integer by the second.".to_string(),
                examples: vec!["div 6 2 = 3".to_string()],
            },
        );
        builtins.insert(
            "eq",
            BuiltinInfo {
                signature: "eq : a -> a -> Bool".to_string(),
                documentation: "Checks if two values are equal.".to_string(),
                examples: vec!["eq 5 5 = true".to_string(), "eq 5 3 = false".to_string()],
            },
        );
        builtins.insert(
            "lt",
            BuiltinInfo {
                signature: "lt : Int -> Int -> Bool".to_string(),
                documentation: "Checks if the first integer is less than the second.".to_string(),
                examples: vec!["lt 3 5 = true".to_string(), "lt 5 3 = false".to_string()],
            },
        );
        builtins.insert(
            "gt",
            BuiltinInfo {
                signature: "gt : Int -> Int -> Bool".to_string(),
                documentation: "Checks if the first integer is greater than the second."
                    .to_string(),
                examples: vec!["gt 5 3 = true".to_string(), "gt 3 5 = false".to_string()],
            },
        );
        builtins.insert(
            "concat",
            BuiltinInfo {
                signature: "concat : String -> String -> String".to_string(),
                documentation: "Concatenates two strings.".to_string(),
                examples: vec!["concat \"hello\" \" world\" = \"hello world\"".to_string()],
            },
        );
        builtins.insert(
            "length",
            BuiltinInfo {
                signature: "length : List a -> Int".to_string(),
                documentation: "Returns the length of a list.".to_string(),
                examples: vec!["length [1, 2, 3] = 3".to_string()],
            },
        );
        builtins.insert(
            "head",
            BuiltinInfo {
                signature: "head : List a -> Maybe a".to_string(),
                documentation: "Returns the first element of a list, or Nothing if the list is \
                                empty."
                    .to_string(),
                examples: vec![
                    "head [1, 2, 3] = Just 1".to_string(),
                    "head [] = Nothing".to_string(),
                ],
            },
        );
        builtins.insert(
            "tail",
            BuiltinInfo {
                signature: "tail : List a -> Maybe (List a)".to_string(),
                documentation: "Returns all elements of a list except the first, or Nothing if \
                                the list is empty."
                    .to_string(),
                examples: vec![
                    "tail [1, 2, 3] = Just [2, 3]".to_string(),
                    "tail [] = Nothing".to_string(),
                ],
            },
        );
        builtins.insert(
            "map",
            BuiltinInfo {
                signature: "map : (a -> b) -> List a -> List b".to_string(),
                documentation: "Applies a function to each element of a list, returning a new \
                                list with the results."
                    .to_string(),
                examples: vec!["map (\\x -> x * 2) [1, 2, 3] = [2, 4, 6]".to_string()],
            },
        );
        builtins.insert(
            "filter",
            BuiltinInfo {
                signature: "filter : (a -> Bool) -> List a -> List a".to_string(),
                documentation: "Filters a list based on a predicate function, keeping only \
                                elements that satisfy the condition."
                    .to_string(),
                examples: vec!["filter (\\x -> x > 2) [1, 2, 3, 4] = [3, 4]".to_string()],
            },
        );
        builtins.insert(
            "fold",
            BuiltinInfo {
                signature: "fold : (b -> a -> b) -> b -> List a -> b".to_string(),
                documentation: "Folds a list with a function and initial value, accumulating a \
                                result."
                    .to_string(),
                examples: vec!["fold (\\acc x -> acc + x) 0 [1, 2, 3] = 6".to_string()],
            },
        );
        builtins.insert(
            "contains",
            BuiltinInfo {
                signature: "contains : String -> String -> Bool".to_string(),
                documentation: "Checks if a string contains a substring.".to_string(),
                examples: vec!["contains \"hello world\" \"world\" = true".to_string()],
            },
        );
        builtins.insert(
            "toString",
            BuiltinInfo {
                signature: "toString : a -> String".to_string(),
                documentation: "Converts a value to its string representation.".to_string(),
                examples: vec!["toString 42 = \"42\"".to_string()],
            },
        );

        let mut builtin_types = HashMap::new();
        builtin_types.insert("Int", "The integer type. Supports arithmetic operations.");
        builtin_types.insert("Float", "The floating-point number type.");
        builtin_types.insert(
            "String",
            "The string type. Supports concatenation and other string operations.",
        );
        builtin_types.insert("Bool", "The boolean type with values true and false.");
        builtin_types.insert("List", "A list type that can contain elements of any type.");
        builtin_types.insert(
            "Maybe",
            "A type that can represent either a value (Just) or nothing (Nothing).",
        );
        builtin_types.insert("Unit", "The unit type with a single value ().");

        Self {
            builtins,
            builtin_types,
            async_evaluation: None,
        }
    }

    /// Create a new hover provider with async evaluation.
    pub fn with_async_evaluation() -> Self {
        let mut provider = Self::new();
        provider.async_evaluation =
            AsyncEvaluationService::new(AsyncEvaluationConfig::default()).ok();
        provider
    }

    /// Get hover information for a position in a document.
    pub async fn provide_hover(
        &self,
        _uri: &str,
        content: &str,
        position: Position,
    ) -> Option<Hover> {
        // Try to parse the program for context-aware hover
        let ast = ligature_parser::parse_program(content).ok();
        self.get_hover(position, content, ast.as_ref()).await
    }

    pub async fn get_hover(
        &self,
        position: Position,
        content: &str,
        ast: Option<&Program>,
    ) -> Option<Hover> {
        let word = self.get_word_at_position(content, position);
        if word.is_empty() {
            return None;
        }

        // Check built-in functions
        if let Some(builtin) = self.builtins.get(word.as_str()) {
            return Some(self.create_builtin_hover(builtin));
        }

        // Check built-in types
        if let Some(type_doc) = self.builtin_types.get(word.as_str()) {
            return Some(self.create_type_hover(word, type_doc));
        }

        // Check symbols from AST
        if let Some(program) = ast {
            if let Some(hover) = self.get_symbol_hover(program, &word) {
                return Some(hover);
            }
        }

        // Check for literals and expressions
        if let Some(hover) = self.get_expression_hover(content, position, ast) {
            return Some(hover);
        }

        // Add evaluation-based hover if available
        if let Some(eval_service) = &self.async_evaluation {
            if let Some(program) = ast {
                if let Some(hover) = self
                    .get_evaluation_based_hover(program, &word, eval_service)
                    .await
                {
                    return Some(hover);
                }
            }
        }

        None
    }

    /// Get evaluation-based hover information.
    async fn get_evaluation_based_hover(
        &self,
        program: &Program,
        word: &str,
        eval_service: &AsyncEvaluationService,
    ) -> Option<Hover> {
        // Try to evaluate the program to get runtime information
        match eval_service.evaluate_program(program, None).await {
            Ok(result) => {
                if result.success {
                    // Look for the word in the evaluated results
                    for (i, value) in result.values.iter().enumerate() {
                        let value_str = format!("{value:?}");
                        if value_str.to_lowercase().contains(&word.to_lowercase()) {
                            let contents = vec![
                                MarkedString::LanguageString(lsp_types::LanguageString {
                                    language: "ligature".to_string(),
                                    value: format!("result_{i} = {value_str}"),
                                }),
                                MarkedString::String(format!(
                                    "**Evaluated Value**\n\nThis value was computed at \
                                     runtime.\n\n**Performance**: {}ms\n**Cache Hit Rate**: {:.1}%",
                                    result.evaluation_time.as_millis(),
                                    result.metrics.cache_hit_rate() * 100.0
                                )),
                            ];

                            return Some(Hover {
                                contents: HoverContents::Array(contents),
                                range: None,
                            });
                        }
                    }

                    // Add performance information hover
                    if result.evaluation_time.as_millis() > 100 {
                        let contents = vec![
                            MarkedString::String("**Performance Warning**".to_string()),
                            MarkedString::String(format!(
                                "Evaluation took {}ms, which is slower than \
                                 expected.\n\nConsider:\n- Caching frequently used values\n- \
                                 Simplifying complex expressions\n- Using more efficient data \
                                 structures",
                                result.evaluation_time.as_millis()
                            )),
                        ];

                        return Some(Hover {
                            contents: HoverContents::Array(contents),
                            range: None,
                        });
                    }
                } else {
                    // Show error information
                    if let Some(error) = result.error {
                        let contents = vec![
                            MarkedString::String("**Evaluation Error**".to_string()),
                            MarkedString::LanguageString(lsp_types::LanguageString {
                                language: "ligature".to_string(),
                                value: error.clone(),
                            }),
                            MarkedString::String(
                                "Consider fixing this error before continuing.".to_string(),
                            ),
                        ];

                        return Some(Hover {
                            contents: HoverContents::Array(contents),
                            range: None,
                        });
                    }
                }
            }
            Err(e) => {
                // Show service error information
                let contents = vec![
                    MarkedString::String("**Evaluation Service Error**".to_string()),
                    MarkedString::LanguageString(lsp_types::LanguageString {
                        language: "ligature".to_string(),
                        value: format!("{e}"),
                    }),
                    MarkedString::String(
                        "The evaluation service encountered an error.".to_string(),
                    ),
                ];

                return Some(Hover {
                    contents: HoverContents::Array(contents),
                    range: None,
                });
            }
        }

        None
    }

    /// Create hover information for a built-in function.
    fn create_builtin_hover(&self, builtin: &BuiltinInfo) -> Hover {
        let mut contents = vec![
            MarkedString::LanguageString(lsp_types::LanguageString {
                language: "ligature".to_string(),
                value: builtin.signature.clone(),
            }),
            MarkedString::String(builtin.documentation.clone()),
        ];

        if !builtin.examples.is_empty() {
            contents.push(MarkedString::String("**Examples:**".to_string()));
            for example in &builtin.examples {
                contents.push(MarkedString::LanguageString(lsp_types::LanguageString {
                    language: "ligature".to_string(),
                    value: example.clone(),
                }));
            }
        }

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    /// Create hover information for a built-in type.
    fn create_type_hover(&self, type_name: String, documentation: &str) -> Hover {
        let contents = vec![
            MarkedString::LanguageString(lsp_types::LanguageString {
                language: "ligature".to_string(),
                value: format!("type {type_name}"),
            }),
            MarkedString::String(documentation.to_string()),
        ];

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    /// Get hover information for a symbol defined in the AST.
    fn get_symbol_hover(&self, program: &Program, symbol_name: &str) -> Option<Hover> {
        for decl in &program.declarations {
            match &decl.kind {
                DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        return Some(self.create_value_hover(value_decl));
                    }
                }
                DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        return Some(self.create_type_alias_hover(type_alias));
                    }
                }
                DeclarationKind::TypeConstructor(type_ctor) => {
                    if type_ctor.name == symbol_name {
                        return Some(self.create_type_constructor_hover(type_ctor));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Create hover information for a value declaration.
    fn create_value_hover(&self, value_decl: &ValueDeclaration) -> Hover {
        let mut contents = Vec::new();

        // Add signature
        let signature = if let Some(ref type_ann) = value_decl.type_annotation {
            format!("{} : {:?}", value_decl.name, type_ann)
        } else {
            format!("{} : <inferred>", value_decl.name)
        };

        contents.push(MarkedString::LanguageString(lsp_types::LanguageString {
            language: "ligature".to_string(),
            value: signature,
        }));

        // Add value definition (simplified)
        let value_str = self.expr_to_string(&value_decl.value);
        if value_str.len() < 100 {
            contents.push(MarkedString::LanguageString(lsp_types::LanguageString {
                language: "ligature".to_string(),
                value: format!("= {value_str}"),
            }));
        } else {
            contents.push(MarkedString::String("= <complex expression>".to_string()));
        }

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    /// Create hover information for a type alias.
    fn create_type_alias_hover(&self, type_alias: &TypeAlias) -> Hover {
        let contents = vec![MarkedString::LanguageString(lsp_types::LanguageString {
            language: "ligature".to_string(),
            value: format!("type {} = {:?}", type_alias.name, type_alias.type_),
        })];

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    /// Create hover information for a type constructor.
    fn create_type_constructor_hover(&self, type_ctor: &TypeConstructor) -> Hover {
        let mut contents = Vec::new();

        // Add type signature
        let signature = format!("data {}", type_ctor.name);
        contents.push(MarkedString::LanguageString(lsp_types::LanguageString {
            language: "ligature".to_string(),
            value: signature,
        }));

        // Add body type
        contents.push(MarkedString::LanguageString(lsp_types::LanguageString {
            language: "ligature".to_string(),
            value: format!("= {:?}", type_ctor.body),
        }));

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    /// Get hover information for expressions at a position.
    fn get_expression_hover(
        &self,
        _content: &str,
        _position: Position,
        _ast: Option<&Program>,
    ) -> Option<Hover> {
        // This is a simplified implementation
        // In a full implementation, you would traverse the AST to find the expression at the given position
        None
    }

    /// Convert an expression to a string representation.
    fn expr_to_string(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Literal(literal) => self.literal_to_string(literal),
            ExprKind::Variable(name) => name.clone(),
            ExprKind::Application { function, argument } => {
                format!(
                    "({} {})",
                    self.expr_to_string(function),
                    self.expr_to_string(argument)
                )
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                let type_ann = if let Some(ty) = parameter_type {
                    format!(" : {ty:?}")
                } else {
                    String::new()
                };
                format!(
                    "fun {}{} => {}",
                    parameter,
                    type_ann,
                    self.expr_to_string(body)
                )
            }
            ExprKind::Let { name, value, body } => {
                format!(
                    "let {} = {} in {}",
                    name,
                    self.expr_to_string(value),
                    self.expr_to_string(body)
                )
            }
            ExprKind::Record { fields } => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|field| format!("{} = {}", field.name, self.expr_to_string(&field.value)))
                    .collect();
                format!("{{ {} }}", field_strs.join(", "))
            }
            ExprKind::FieldAccess { record, field } => {
                format!("{}.{}", self.expr_to_string(record), field)
            }
            ExprKind::Union { variant, value } => {
                if let Some(val) = value {
                    format!("{} {}", variant, self.expr_to_string(val))
                } else {
                    variant.clone()
                }
            }
            ExprKind::Match { scrutinee, cases } => {
                let case_strs: Vec<String> = cases
                    .iter()
                    .map(|case| {
                        format!(
                            "  {} => {}",
                            self.pattern_to_string(&case.pattern),
                            self.expr_to_string(&case.expression)
                        )
                    })
                    .collect();
                format!(
                    "case {} of\n{}",
                    self.expr_to_string(scrutinee),
                    case_strs.join("\n")
                )
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                format!(
                    "if {} then {} else {}",
                    self.expr_to_string(condition),
                    self.expr_to_string(then_branch),
                    self.expr_to_string(else_branch)
                )
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                format!(
                    "({} {} {})",
                    self.expr_to_string(left),
                    self.binary_op_to_string(operator),
                    self.expr_to_string(right)
                )
            }
            ExprKind::UnaryOp { operator, operand } => {
                format!(
                    "({} {})",
                    self.unary_op_to_string(operator),
                    self.expr_to_string(operand)
                )
            }
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => {
                format!(
                    "({} : {:?})",
                    self.expr_to_string(expression),
                    type_annotation
                )
            }
        }
    }

    /// Convert a literal to a string representation.
    fn literal_to_string(&self, literal: &ligature_ast::Literal) -> String {
        match literal {
            ligature_ast::Literal::String(s) => format!("\"{s}\""),
            ligature_ast::Literal::Integer(i) => i.to_string(),
            ligature_ast::Literal::Float(f) => f.to_string(),
            ligature_ast::Literal::Boolean(b) => b.to_string(),
            ligature_ast::Literal::Unit => "()".to_string(),
            ligature_ast::Literal::List(elements) => {
                let element_strs: Vec<String> =
                    elements.iter().map(|e| self.expr_to_string(e)).collect();
                format!("[{}]", element_strs.join(", "))
            }
        }
    }

    /// Convert a pattern to a string representation.
    fn pattern_to_string(&self, pattern: &ligature_ast::Pattern) -> String {
        match pattern {
            ligature_ast::Pattern::Wildcard => "_".to_string(),
            ligature_ast::Pattern::Variable(name) => name.clone(),
            ligature_ast::Pattern::Literal(literal) => self.literal_to_string(literal),
            ligature_ast::Pattern::Record { fields } => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|field| {
                        format!(
                            "{} = {}",
                            field.name,
                            self.pattern_to_string(&field.pattern)
                        )
                    })
                    .collect();
                format!("{{ {} }}", field_strs.join(", "))
            }
            ligature_ast::Pattern::Union { variant, value } => {
                if let Some(val) = value {
                    format!("{} {}", variant, self.pattern_to_string(val))
                } else {
                    variant.clone()
                }
            }
            ligature_ast::Pattern::List { elements } => {
                let element_strs: Vec<String> =
                    elements.iter().map(|e| self.pattern_to_string(e)).collect();
                format!("[{}]", element_strs.join(", "))
            }
        }
    }

    /// Convert a binary operator to a string representation.
    fn binary_op_to_string(&self, op: &ligature_ast::BinaryOperator) -> &'static str {
        match op {
            ligature_ast::BinaryOperator::Add => "+",
            ligature_ast::BinaryOperator::Subtract => "-",
            ligature_ast::BinaryOperator::Multiply => "*",
            ligature_ast::BinaryOperator::Divide => "/",
            ligature_ast::BinaryOperator::Modulo => "%",
            ligature_ast::BinaryOperator::Equal => "==",
            ligature_ast::BinaryOperator::NotEqual => "!=",
            ligature_ast::BinaryOperator::LessThan => "<",
            ligature_ast::BinaryOperator::LessThanOrEqual => "<=",
            ligature_ast::BinaryOperator::GreaterThan => ">",
            ligature_ast::BinaryOperator::GreaterThanOrEqual => ">=",
            ligature_ast::BinaryOperator::And => "&&",
            ligature_ast::BinaryOperator::Or => "||",
            ligature_ast::BinaryOperator::Concat => "++",
        }
    }

    /// Convert a unary operator to a string representation.
    fn unary_op_to_string(&self, op: &ligature_ast::UnaryOperator) -> &'static str {
        match op {
            ligature_ast::UnaryOperator::Not => "!",
            ligature_ast::UnaryOperator::Negate => "-",
        }
    }

    /// Get the word at a specific position in the content.
    fn get_word_at_position(&self, content: &str, position: Position) -> String {
        let lines: Vec<&str> = content.lines().collect();
        if position.line as usize >= lines.len() {
            return String::new();
        }

        let line = lines[position.line as usize];
        let char_pos = position.character as usize;

        if char_pos >= line.len() {
            return String::new();
        }

        // Find the start of the word
        let mut start = char_pos;
        while start > 0
            && line
                .chars()
                .nth(start - 1)
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            start -= 1;
        }

        // Find the end of the word
        let mut end = char_pos;
        while end < line.len()
            && line
                .chars()
                .nth(end)
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            end += 1;
        }

        line[start..end].to_string()
    }
}

impl Default for HoverProvider {
    fn default() -> Self {
        Self::new()
    }
}
