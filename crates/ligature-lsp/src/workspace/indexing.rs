//! Workspace indexing functionality.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tokio::sync::RwLock;
use tower_lsp::lsp_types::WorkspaceFolder;
use tracing::info;

use super::types::*;
use crate::async_evaluation::AsyncEvaluationService;
use crate::config::WorkspaceConfig;

/// Type alias for workspace files
type WorkspaceFiles = Arc<RwLock<HashMap<String, WorkspaceFile>>>;

/// Type alias for workspace symbols
type WorkspaceSymbols = Arc<RwLock<HashMap<String, Vec<WorkspaceSymbolWithMetadata>>>>;

/// Scan directory for Ligature files
pub async fn scan_directory(dir: &Path, workspace_config: &WorkspaceConfig) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut entries = Vec::new();

    if let Ok(mut read_dir) = tokio::fs::read_dir(dir).await {
        while let Ok(Some(entry)) = read_dir.next_entry().await {
            entries.push(entry);
        }
    }

    for entry in entries {
        let path = entry.path();
        if path.is_file() {
            if let Some(extension) = path.extension() {
                if extension == "lig" {
                    files.push(path);
                }
            }
        } else if path.is_dir() {
            // Check if directory should be excluded
            let should_exclude = workspace_config
                .exclude_patterns
                .iter()
                .any(|pattern| matches_pattern(path.to_str().unwrap_or(""), pattern));

            if !should_exclude {
                let sub_files = Box::pin(scan_directory(&path, workspace_config)).await;
                files.extend(sub_files);
            }
        }
    }

    files
}

/// Index file with evaluation support
pub async fn index_file_with_evaluation(
    path: &Path,
    async_evaluation: Option<&AsyncEvaluationService>,
) -> std::io::Result<(WorkspaceFile, Vec<WorkspaceSymbolWithMetadata>)> {
    let content = tokio::fs::read_to_string(path).await?;
    let metadata = tokio::fs::metadata(path).await?;
    let uri = format!("file://{}", path.to_string_lossy());

    let ast = ligature_parser::parse_program(&content).ok();
    let mut evaluation_metadata = None;

    // Evaluate the file if async evaluation is available
    if let Some(eval_service) = async_evaluation {
        if let Some(program) = &ast {
            let start_time = std::time::Instant::now();
            let cache_key = format!("index_{}", path.to_string_lossy());

            match eval_service
                .evaluate_program(program, Some(&cache_key))
                .await
            {
                Ok(eval_result) => {
                    let evaluation_time = start_time.elapsed();
                    evaluation_metadata = Some(FileEvaluationMetadata {
                        evaluated: eval_result.success,
                        evaluation_time_ms: evaluation_time.as_millis() as u64,
                        expressions_evaluated: program.declarations.len(),
                        evaluation_errors: eval_result.error.map(|e| vec![e]).unwrap_or_default(),
                        performance_metrics: Some(format!("{:?}", eval_result.metrics)),
                    });
                }
                Err(e) => {
                    evaluation_metadata = Some(FileEvaluationMetadata {
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

    let workspace_file = WorkspaceFile {
        uri,
        path: path.to_path_buf(),
        content,
        ast,
        size: metadata.len() as usize,
        last_modified: metadata.modified()?,
        indexed: true,
        evaluation_metadata,
    };

    let symbols = super::symbols::extract_symbols_from_program_with_evaluation(
        &workspace_file.ast,
        &workspace_file.uri,
        async_evaluation,
    )
    .await;

    Ok((workspace_file, symbols))
}

/// Index file (original method)
pub async fn index_file(
    path: &Path,
) -> std::io::Result<(WorkspaceFile, Vec<WorkspaceSymbolWithMetadata>)> {
    let content = tokio::fs::read_to_string(path).await?;
    let metadata = tokio::fs::metadata(path).await?;
    let uri = format!("file://{}", path.to_string_lossy());

    let ast = ligature_parser::parse_program(&content).ok();

    let workspace_file = WorkspaceFile {
        uri,
        path: path.to_path_buf(),
        content,
        ast,
        size: metadata.len() as usize,
        last_modified: metadata.modified()?,
        indexed: true,
        evaluation_metadata: None,
    };

    let symbols =
        super::symbols::extract_symbols_from_program(&workspace_file.ast, &workspace_file.uri);

    Ok((workspace_file, symbols))
}

/// Internal indexing with evaluation support
pub async fn index_workspace_internal_with_evaluation(
    folders: Vec<WorkspaceFolder>,
    files: WorkspaceFiles,
    symbols: WorkspaceSymbols,
    indexing_status: std::sync::Arc<RwLock<IndexingStatus>>,
    async_evaluation: Option<AsyncEvaluationService>,
) {
    let mut all_files = Vec::new();
    let workspace_config = WorkspaceConfig::default();

    // Scan all folders for files
    for folder in &folders {
        let folder_path = &folder.uri;
        if let Ok(path) = folder_path.to_file_path() {
            let folder_files = scan_directory(&path, &workspace_config).await;
            all_files.extend(folder_files);
        }
    }

    // Update total files count
    {
        let mut status = indexing_status.write().await;
        status.total_files = all_files.len();
        if let Some(ref mut eval_progress) = status.evaluation_progress {
            eval_progress.total_files_to_evaluate = all_files.len();
        }
    }

    let mut files_map = files.write().await;
    let mut symbols_map = symbols.write().await;
    let mut total_evaluation_time = 0u64;

    for (i, path) in all_files.iter().enumerate() {
        match index_file_with_evaluation(path, async_evaluation.as_ref()).await {
            Ok((workspace_file, file_symbols)) => {
                let uri = workspace_file.uri.clone();
                files_map.insert(uri.clone(), workspace_file);
                symbols_map.insert(uri.clone(), file_symbols);

                // Update evaluation progress
                if let Some(eval_metadata) = &files_map.get(&uri).unwrap().evaluation_metadata {
                    total_evaluation_time += eval_metadata.evaluation_time_ms;
                    let avg_time = total_evaluation_time / (i + 1) as u64;

                    let mut status = indexing_status.write().await;
                    status.files_indexed = i + 1;
                    if let Some(ref mut eval_progress) = status.evaluation_progress {
                        eval_progress.files_evaluated = i + 1;
                        eval_progress.current_evaluation_time_ms = total_evaluation_time;
                        eval_progress.avg_evaluation_time_ms = avg_time;
                    }
                }
            }
            Err(e) => {
                let mut status = indexing_status.write().await;
                status
                    .errors
                    .push(format!("Failed to index {}: {}", path.display(), e));
            }
        }
    }

    // Mark indexing as complete
    {
        let mut status = indexing_status.write().await;
        status.indexing = false;
        status.last_indexed = Some(std::time::SystemTime::now());
    }

    info!("Workspace indexing with evaluation completed");
}

/// Internal indexing (original method)
pub async fn index_workspace_internal(
    folders: Vec<WorkspaceFolder>,
    files: WorkspaceFiles,
    symbols: WorkspaceSymbols,
    indexing_status: std::sync::Arc<RwLock<IndexingStatus>>,
) {
    let mut all_files = Vec::new();
    let workspace_config = WorkspaceConfig::default();

    // Scan all folders for files
    for folder in &folders {
        let folder_path = &folder.uri;
        if let Ok(path) = folder_path.to_file_path() {
            let folder_files = scan_directory(&path, &workspace_config).await;
            all_files.extend(folder_files);
        }
    }

    // Update total files count
    {
        let mut status = indexing_status.write().await;
        status.total_files = all_files.len();
    }

    let mut files_map = files.write().await;
    let mut symbols_map = symbols.write().await;

    for (i, path) in all_files.iter().enumerate() {
        match index_file(path).await {
            Ok((workspace_file, file_symbols)) => {
                let uri = workspace_file.uri.clone();
                files_map.insert(uri.clone(), workspace_file);
                symbols_map.insert(uri, file_symbols);

                let mut status = indexing_status.write().await;
                status.files_indexed = i + 1;
            }
            Err(e) => {
                let mut status = indexing_status.write().await;
                status
                    .errors
                    .push(format!("Failed to index {}: {}", path.display(), e));
            }
        }
    }

    // Mark indexing as complete
    {
        let mut status = indexing_status.write().await;
        status.indexing = false;
        status.last_indexed = Some(std::time::SystemTime::now());
    }

    info!("Workspace indexing completed");
}

/// Check if path matches pattern
pub fn matches_pattern(path: &str, pattern: &str) -> bool {
    // Simple pattern matching - can be enhanced with regex
    path.contains(pattern)
}
