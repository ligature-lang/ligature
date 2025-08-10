//! Workspace evaluation integration functionality.

use std::collections::HashMap;

use tower_lsp::lsp_types::WorkspaceFolder;

use super::symbols::*;
use super::types::*;
use crate::async_evaluation::AsyncEvaluationService;

/// Update file with evaluation support
pub async fn update_file_with_evaluation(
    uri: &str,
    content: String,
    files: &mut HashMap<String, WorkspaceFile>,
    symbols: &mut HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    async_evaluation: Option<&AsyncEvaluationService>,
) {
    if let Some(file) = files.get_mut(uri) {
        file.content = content.clone();
        file.ast = ligature_parser::parse_program(&content).ok();
        file.last_modified = std::time::SystemTime::now();

        // Re-evaluate the file if async evaluation is available
        if let Some(eval_service) = async_evaluation {
            if let Some(program) = &file.ast {
                let start_time = std::time::Instant::now();
                let cache_key = format!("update_{uri}");

                match eval_service
                    .evaluate_program(program, Some(&cache_key))
                    .await
                {
                    Ok(eval_result) => {
                        let evaluation_time = start_time.elapsed();
                        file.evaluation_metadata = Some(FileEvaluationMetadata {
                            evaluated: eval_result.success,
                            evaluation_time_ms: evaluation_time.as_millis() as u64,
                            expressions_evaluated: program.declarations.len(),
                            evaluation_errors: eval_result
                                .error
                                .map(|e| vec![e])
                                .unwrap_or_default(),
                            performance_metrics: Some(format!("{:?}", eval_result.metrics)),
                        });
                    }
                    Err(e) => {
                        file.evaluation_metadata = Some(FileEvaluationMetadata {
                            evaluated: false,
                            evaluation_time_ms: 0,
                            expressions_evaluated: 0,
                            evaluation_errors: vec![format!("Evaluation failed: {}", e)],
                            performance_metrics: None,
                        });
                    }
                }
            }
        }

        // Update symbols
        let new_symbols =
            extract_symbols_from_program_with_evaluation(&file.ast, uri, async_evaluation).await;
        symbols.insert(uri.to_string(), new_symbols);
    }
}

/// Get workspace symbols with evaluation metadata
pub async fn get_workspace_symbols_with_evaluation(
    symbols: &HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    query: &str,
) -> Vec<WorkspaceSymbolWithMetadata> {
    let mut result = Vec::new();

    for symbol_list in symbols.values() {
        for symbol in symbol_list {
            if symbol.name.to_lowercase().contains(&query.to_lowercase()) {
                result.push(symbol.clone());
            }
        }
    }

    result
}

/// Find symbol definition with evaluation support
pub async fn find_symbol_definition_with_evaluation(
    symbols: &HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    symbol_name: &str,
) -> Option<tower_lsp::lsp_types::Location> {
    for symbol_list in symbols.values() {
        for symbol in symbol_list {
            if symbol.name == symbol_name {
                // Check if symbol has been evaluated
                if let Some(eval_metadata) = &symbol.evaluation_metadata {
                    if eval_metadata.evaluated {
                        return Some(symbol.location.clone());
                    }
                }
                return Some(symbol.location.clone());
            }
        }
    }

    None
}

/// Find symbol references with evaluation support
pub async fn find_symbol_references_with_evaluation(
    files: &HashMap<String, WorkspaceFile>,
    symbol_name: &str,
) -> Vec<tower_lsp::lsp_types::Location> {
    let mut references = Vec::new();

    for file in files.values() {
        if let Some(program) = &file.ast {
            for declaration in &program.declarations {
                if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                    if expression_references_symbol(&value_decl.value, symbol_name) {
                        references.push(span_to_location(&declaration.span, &file.uri));
                    }
                }
            }
        }
    }

    references
}

/// Find type definition with evaluation support
pub async fn find_type_definition_with_evaluation(
    symbols: &HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    symbol_name: &str,
) -> Option<tower_lsp::lsp_types::Location> {
    for symbol_list in symbols.values() {
        for symbol in symbol_list {
            if symbol.name == symbol_name
                && symbol.kind == tower_lsp::lsp_types::SymbolKind::TYPE_PARAMETER
            {
                return Some(symbol.location.clone());
            }
        }
    }

    None
}

/// Find implementations with evaluation support
pub async fn find_implementations_with_evaluation(
    symbols: &HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    symbol_name: &str,
) -> Vec<tower_lsp::lsp_types::Location> {
    let mut implementations = Vec::new();

    for symbol_list in symbols.values() {
        for symbol in symbol_list {
            if symbol.name == symbol_name && symbol.kind == tower_lsp::lsp_types::SymbolKind::METHOD
            {
                implementations.push(symbol.location.clone());
            }
        }
    }

    implementations
}

/// Get workspace stats with evaluation information
pub async fn get_workspace_stats_with_evaluation(
    files: &HashMap<String, WorkspaceFile>,
    symbols: &HashMap<String, Vec<WorkspaceSymbolWithMetadata>>,
    folders: &[WorkspaceFolder],
) -> WorkspaceStatsWithEvaluation {
    let mut total_evaluation_time = 0u64;
    let mut evaluated_files = 0usize;
    let mut total_expressions = 0usize;

    for file in files.values() {
        if let Some(eval_metadata) = &file.evaluation_metadata {
            if eval_metadata.evaluated {
                evaluated_files += 1;
                total_evaluation_time += eval_metadata.evaluation_time_ms;
                total_expressions += eval_metadata.expressions_evaluated;
            }
        }
    }

    WorkspaceStatsWithEvaluation {
        total_files: files.len(),
        total_symbols: symbols.values().map(|s| s.len()).sum(),
        total_size: files.values().map(|f| f.size).sum(),
        folder_count: folders.len(),
        evaluated_files,
        total_evaluation_time_ms: total_evaluation_time,
        total_expressions_evaluated: total_expressions,
        avg_evaluation_time_per_file: if evaluated_files > 0 {
            total_evaluation_time / evaluated_files as u64
        } else {
            0
        },
    }
}
