//! Workspace types and data structures.

use tower_lsp::lsp_types::*;

/// Workspace file information
#[derive(Debug, Clone)]
pub struct WorkspaceFile {
    /// File URI
    pub uri: String,
    /// File path
    pub path: std::path::PathBuf,
    /// File content
    pub content: String,
    /// Parsed AST
    pub ast: Option<ligature_ast::Program>,
    /// File size in bytes
    pub size: usize,
    /// Last modified time
    pub last_modified: std::time::SystemTime,
    /// Whether the file is indexed
    pub indexed: bool,
    /// Evaluation metadata for the file
    pub evaluation_metadata: Option<FileEvaluationMetadata>,
}

/// Evaluation metadata for a file
#[derive(Debug, Clone)]
pub struct FileEvaluationMetadata {
    /// Whether the file has been evaluated
    pub evaluated: bool,
    /// Evaluation time in milliseconds
    pub evaluation_time_ms: u64,
    /// Number of expressions evaluated
    pub expressions_evaluated: usize,
    /// Evaluation errors if any
    pub evaluation_errors: Vec<String>,
    /// Performance metrics
    pub performance_metrics: Option<String>,
}

/// Workspace symbol information with evaluation metadata
#[derive(Debug, Clone)]
pub struct WorkspaceSymbolWithMetadata {
    /// Symbol name
    pub name: String,
    /// Symbol kind
    pub kind: SymbolKind,
    /// Symbol location
    pub location: Location,
    /// Symbol container name
    pub container_name: Option<String>,
    /// Symbol documentation
    pub documentation: Option<String>,
    /// Symbol tags
    pub tags: Vec<SymbolTag>,
    /// Evaluation-based metadata
    pub evaluation_metadata: Option<SymbolEvaluationMetadata>,
}

/// Evaluation metadata for a symbol
#[derive(Debug, Clone)]
pub struct SymbolEvaluationMetadata {
    /// Whether the symbol has been evaluated
    pub evaluated: bool,
    /// Evaluated value if available
    pub evaluated_value: Option<String>,
    /// Evaluation time in milliseconds
    pub evaluation_time_ms: u64,
    /// Whether the symbol is a constant
    pub is_constant: bool,
    /// Whether the symbol is a function
    pub is_function: bool,
}

/// Indexing status
#[derive(Debug, Clone, Default)]
pub struct IndexingStatus {
    /// Whether indexing is in progress
    pub indexing: bool,
    /// Number of files indexed
    pub files_indexed: usize,
    /// Total number of files to index
    pub total_files: usize,
    /// Indexing errors
    pub errors: Vec<String>,
    /// Last indexing time
    pub last_indexed: Option<std::time::SystemTime>,
    /// Evaluation-based indexing progress
    pub evaluation_progress: Option<EvaluationProgress>,
}

/// Evaluation progress information
#[derive(Debug, Clone)]
pub struct EvaluationProgress {
    /// Number of files evaluated
    pub files_evaluated: usize,
    /// Total number of files to evaluate
    pub total_files_to_evaluate: usize,
    /// Current evaluation time in milliseconds
    pub current_evaluation_time_ms: u64,
    /// Average evaluation time per file
    pub avg_evaluation_time_ms: u64,
}

/// Workspace statistics with evaluation information
pub struct WorkspaceStatsWithEvaluation {
    /// Total number of files
    pub total_files: usize,
    /// Total number of symbols
    pub total_symbols: usize,
    /// Total size in bytes
    pub total_size: usize,
    /// Number of folders
    pub folder_count: usize,
    /// Number of files that have been evaluated
    pub evaluated_files: usize,
    /// Total evaluation time in milliseconds
    pub total_evaluation_time_ms: u64,
    /// Total number of expressions evaluated
    pub total_expressions_evaluated: usize,
    /// Average evaluation time per file in milliseconds
    pub avg_evaluation_time_per_file: u64,
}

/// Workspace statistics
pub struct WorkspaceStats {
    /// Total number of files
    pub total_files: usize,
    /// Total number of symbols
    pub total_symbols: usize,
    /// Total size in bytes
    pub total_size: usize,
    /// Number of folders
    pub folder_count: usize,
}
