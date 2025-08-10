//! Workspace symbol management functionality.

use tower_lsp::lsp_types::*;

use super::types::*;
use crate::async_evaluation::AsyncEvaluationService;

/// Convert our custom symbol to LSP WorkspaceSymbol
pub fn convert_to_lsp_symbol(symbol: &WorkspaceSymbolWithMetadata) -> WorkspaceSymbol {
    WorkspaceSymbol {
        name: symbol.name.clone(),
        kind: symbol.kind,
        location: OneOf::Left(symbol.location.clone()),
        container_name: symbol.container_name.clone(),
        tags: Some(symbol.tags.clone()),
        data: None,
    }
}

/// Extract symbols from program with evaluation support
pub async fn extract_symbols_from_program_with_evaluation(
    ast: &Option<ligature_ast::Program>,
    uri: &str,
    async_evaluation: Option<&AsyncEvaluationService>,
) -> Vec<WorkspaceSymbolWithMetadata> {
    let mut symbols = Vec::new();

    if let Some(program) = ast {
        for declaration in &program.declarations {
            let mut evaluation_metadata = None;

            // Evaluate the declaration if async evaluation is available
            if let Some(eval_service) = async_evaluation {
                if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                    let start_time = std::time::Instant::now();
                    let cache_key = format!("symbol_{}_{}", uri, value_decl.name);

                    if let Ok(eval_result) = eval_service
                        .evaluate_expression(&value_decl.value, Some(&cache_key))
                        .await
                    {
                        let evaluation_time = start_time.elapsed();
                        let evaluated_value =
                            if eval_result.success && !eval_result.values.is_empty() {
                                Some(format!("{:?}", eval_result.values[0]))
                            } else {
                                None
                            };

                        evaluation_metadata = Some(SymbolEvaluationMetadata {
                            evaluated: eval_result.success,
                            evaluated_value,
                            evaluation_time_ms: evaluation_time.as_millis() as u64,
                            is_constant: is_constant_expression(&value_decl.value),
                            is_function: is_function_expression(&value_decl.value),
                        });
                    }
                }
            }

            let symbol = create_symbol_from_declaration(declaration, uri, evaluation_metadata);
            symbols.push(symbol);
        }
    }

    symbols
}

/// Extract symbols from program (original method)
pub fn extract_symbols_from_program(
    ast: &Option<ligature_ast::Program>,
    uri: &str,
) -> Vec<WorkspaceSymbolWithMetadata> {
    let mut symbols = Vec::new();

    if let Some(program) = ast {
        for declaration in &program.declarations {
            let symbol = create_symbol_from_declaration(declaration, uri, None);
            symbols.push(symbol);
        }
    }

    symbols
}

/// Create symbol from declaration
pub fn create_symbol_from_declaration(
    declaration: &ligature_ast::Declaration,
    uri: &str,
    evaluation_metadata: Option<SymbolEvaluationMetadata>,
) -> WorkspaceSymbolWithMetadata {
    match &declaration.kind {
        ligature_ast::DeclarationKind::Value(value_decl) => WorkspaceSymbolWithMetadata {
            name: value_decl.name.clone(),
            kind: SymbolKind::VARIABLE,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata,
        },
        ligature_ast::DeclarationKind::TypeAlias(type_alias) => WorkspaceSymbolWithMetadata {
            name: type_alias.name.clone(),
            kind: SymbolKind::TYPE_PARAMETER,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata: None,
        },
        ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
            WorkspaceSymbolWithMetadata {
                name: type_constructor.name.clone(),
                kind: SymbolKind::CLASS,
                location: span_to_location(&declaration.span, uri),
                container_name: None,
                documentation: None,
                tags: Vec::new(),
                evaluation_metadata: None,
            }
        }
        ligature_ast::DeclarationKind::TypeClass(type_class) => WorkspaceSymbolWithMetadata {
            name: type_class.name.clone(),
            kind: SymbolKind::INTERFACE,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata: None,
        },
        ligature_ast::DeclarationKind::Instance(_) => WorkspaceSymbolWithMetadata {
            name: "instance".to_string(),
            kind: SymbolKind::METHOD,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata: None,
        },
        ligature_ast::DeclarationKind::Import(_) => WorkspaceSymbolWithMetadata {
            name: "import".to_string(),
            kind: SymbolKind::NAMESPACE,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata: None,
        },
        ligature_ast::DeclarationKind::Export(_) => WorkspaceSymbolWithMetadata {
            name: "export".to_string(),
            kind: SymbolKind::NAMESPACE,
            location: span_to_location(&declaration.span, uri),
            container_name: None,
            documentation: None,
            tags: Vec::new(),
            evaluation_metadata: None,
        },
    }
}

/// Check if an expression is a constant
pub fn is_constant_expression(expr: &ligature_ast::Expr) -> bool {
    matches!(expr.kind, ligature_ast::ExprKind::Literal(_))
}

/// Check if an expression is a function
pub fn is_function_expression(expr: &ligature_ast::Expr) -> bool {
    matches!(expr.kind, ligature_ast::ExprKind::Abstraction { .. })
}

/// Convert span to location
pub fn span_to_location(span: &ligature_ast::Span, uri: &str) -> Location {
    Location {
        uri: uri.parse().unwrap_or_else(|_| {
            format!("file://{uri}")
                .parse()
                .unwrap_or_else(|_| "file:///invalid".parse().unwrap())
        }),
        range: Range {
            start: Position {
                line: span.line as u32,
                character: span.column as u32,
            },
            end: Position {
                line: span.line as u32,
                character: span.column as u32,
            },
        },
    }
}

/// Check if expression references a symbol
pub fn expression_references_symbol(expr: &ligature_ast::Expr, symbol_name: &str) -> bool {
    match &expr.kind {
        ligature_ast::ExprKind::Variable(name) => name == symbol_name,
        ligature_ast::ExprKind::Application { function, argument } => {
            expression_references_symbol(function, symbol_name)
                || expression_references_symbol(argument, symbol_name)
        }
        ligature_ast::ExprKind::Abstraction {
            parameter,
            parameter_type,
            body,
        } => {
            parameter == symbol_name
                || parameter_type
                    .as_ref()
                    .is_some_and(|ty| type_references_symbol(ty, symbol_name))
                || expression_references_symbol(body, symbol_name)
        }
        ligature_ast::ExprKind::Let { name, value, body } => {
            name == symbol_name
                || expression_references_symbol(value, symbol_name)
                || expression_references_symbol(body, symbol_name)
        }
        ligature_ast::ExprKind::Record { fields } => fields
            .iter()
            .any(|field| expression_references_symbol(&field.value, symbol_name)),
        ligature_ast::ExprKind::FieldAccess { record, field: _ } => {
            expression_references_symbol(record, symbol_name)
        }
        ligature_ast::ExprKind::Union { variant: _, value } => value
            .as_ref()
            .is_some_and(|val| expression_references_symbol(val, symbol_name)),
        ligature_ast::ExprKind::Match { scrutinee, cases } => {
            expression_references_symbol(scrutinee, symbol_name)
                || cases.iter().any(|case| {
                    pattern_references_symbol(&case.pattern, symbol_name)
                        || case
                            .guard
                            .as_ref()
                            .is_some_and(|guard| expression_references_symbol(guard, symbol_name))
                        || expression_references_symbol(&case.expression, symbol_name)
                })
        }
        ligature_ast::ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_references_symbol(condition, symbol_name)
                || expression_references_symbol(then_branch, symbol_name)
                || expression_references_symbol(else_branch, symbol_name)
        }
        ligature_ast::ExprKind::BinaryOp {
            operator: _,
            left,
            right,
        } => {
            expression_references_symbol(left, symbol_name)
                || expression_references_symbol(right, symbol_name)
        }
        ligature_ast::ExprKind::UnaryOp {
            operator: _,
            operand,
        } => expression_references_symbol(operand, symbol_name),
        ligature_ast::ExprKind::Annotated {
            expression,
            type_annotation,
        } => {
            expression_references_symbol(expression, symbol_name)
                || type_references_symbol(type_annotation, symbol_name)
        }
        ligature_ast::ExprKind::Literal(_) => false,
    }
}

/// Check if a type references a symbol.
pub fn type_references_symbol(ty: &ligature_ast::Type, symbol_name: &str) -> bool {
    match &ty.kind {
        ligature_ast::TypeKind::Variable(name) => name == symbol_name,
        ligature_ast::TypeKind::Function {
            parameter,
            return_type,
        } => {
            type_references_symbol(parameter, symbol_name)
                || type_references_symbol(return_type, symbol_name)
        }
        ligature_ast::TypeKind::Record { fields } => fields
            .iter()
            .any(|field| type_references_symbol(&field.type_, symbol_name)),
        ligature_ast::TypeKind::Union { variants } => variants.iter().any(|variant| {
            variant
                .type_
                .as_ref()
                .is_some_and(|ty| type_references_symbol(ty, symbol_name))
        }),
        ligature_ast::TypeKind::List(element_type) => {
            type_references_symbol(element_type, symbol_name)
        }
        ligature_ast::TypeKind::Application { function, argument } => {
            type_references_symbol(function, symbol_name)
                || type_references_symbol(argument, symbol_name)
        }
        ligature_ast::TypeKind::ForAll { body, .. } => type_references_symbol(body, symbol_name),
        ligature_ast::TypeKind::Exists { body, .. } => type_references_symbol(body, symbol_name),
        ligature_ast::TypeKind::Constrained {
            constraint: _,
            type_,
        } => type_references_symbol(type_, symbol_name),
        ligature_ast::TypeKind::Unit => false,
        ligature_ast::TypeKind::Bool => false,
        ligature_ast::TypeKind::String => false,
        ligature_ast::TypeKind::Integer => false,
        ligature_ast::TypeKind::Float => false,
        ligature_ast::TypeKind::Pi { .. } => false,
        ligature_ast::TypeKind::Sigma { .. } => false,
        ligature_ast::TypeKind::Module { .. } => false,
        ligature_ast::TypeKind::Refinement { .. } => false,
        ligature_ast::TypeKind::ConstraintType { .. } => false,
    }
}

/// Check if a pattern references a symbol.
pub fn pattern_references_symbol(pattern: &ligature_ast::Pattern, symbol_name: &str) -> bool {
    match pattern {
        ligature_ast::Pattern::Variable(name) => name == symbol_name,
        ligature_ast::Pattern::Record { fields } => fields
            .iter()
            .any(|field| pattern_references_symbol(&field.pattern, symbol_name)),
        ligature_ast::Pattern::Union { variant: _, value } => value
            .as_ref()
            .is_some_and(|val| pattern_references_symbol(val, symbol_name)),
        ligature_ast::Pattern::List { elements } => elements
            .iter()
            .any(|element| pattern_references_symbol(element, symbol_name)),
        ligature_ast::Pattern::Literal(_) => false,
        ligature_ast::Pattern::Wildcard => false,
    }
}

/// Check if a constraint references a symbol.
pub fn constraint_references_symbol(
    constraint: &ligature_ast::ty::Constraint,
    symbol_name: &str,
) -> bool {
    match constraint {
        ligature_ast::ty::Constraint::ValueConstraint(expr) => {
            expression_references_symbol(expr, symbol_name)
        }
        ligature_ast::ty::Constraint::RangeConstraint { min, max, .. } => {
            min.as_ref()
                .is_some_and(|expr| expression_references_symbol(expr, symbol_name))
                || max
                    .as_ref()
                    .is_some_and(|expr| expression_references_symbol(expr, symbol_name))
        }
        ligature_ast::ty::Constraint::CustomConstraint {
            function,
            arguments,
        } => {
            function == symbol_name
                || arguments
                    .iter()
                    .any(|expr| expression_references_symbol(expr, symbol_name))
        }
        ligature_ast::ty::Constraint::CrossFieldConstraint { predicate, .. } => {
            expression_references_symbol(predicate, symbol_name)
        }
        ligature_ast::ty::Constraint::PatternConstraint { .. } => false,
    }
}
