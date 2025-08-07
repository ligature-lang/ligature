//! Specification management for Baton formal verification.
//!
//! This crate provides specification management for the Baton
//! formal verification system.

use baton_core::prelude::*;
use baton_error::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::process::Command;
use tokio::time::{timeout, Duration};

/// Lean specification manager.
pub struct LeanSpecification {
    /// Path to specification directory
    spec_path: PathBuf,
    /// Specification files cache
    files_cache: HashMap<String, String>,
    /// Build status cache
    build_cache: HashMap<String, bool>,
    /// Dependency graph
    dependency_graph: HashMap<String, Vec<String>>,
    /// File modification times
    modification_times: HashMap<String, u64>,
    /// Build configuration
    build_config: BuildConfig,
}

/// Build configuration for Lean specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildConfig {
    /// Whether to enable incremental builds
    pub incremental: bool,
    /// Whether to enable parallel builds
    pub parallel: bool,
    /// Build timeout in seconds
    pub timeout: u64,
    /// Whether to enable verbose output
    pub verbose: bool,
    /// Additional build flags
    pub build_flags: Vec<String>,
    /// Target libraries to build
    pub targets: Vec<String>,
}

impl Default for BuildConfig {
    fn default() -> Self {
        Self {
            incremental: true,
            parallel: false,
            timeout: 300, // 5 minutes
            verbose: false,
            build_flags: vec![],
            targets: vec![
                "Ligature".to_string(),
                "TypeSystem".to_string(),
                "OperationalSemantics".to_string(),
            ],
        }
    }
}

/// Specification file information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecFileInfo {
    /// File path
    pub path: String,
    /// File content hash
    pub hash: String,
    /// Last modified timestamp
    pub modified: u64,
    /// Whether file is valid
    pub valid: bool,
    /// Compilation errors if any
    pub errors: Vec<String>,
    /// Compilation warnings if any
    pub warnings: Vec<String>,
    /// File dependencies
    pub dependencies: Vec<String>,
    /// File size in bytes
    pub size: u64,
    /// File type
    pub file_type: SpecFileType,
}

/// Specification file type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpecFileType {
    /// Main specification file
    Main,
    /// Type system specification
    TypeSystem,
    /// Operational semantics specification
    OperationalSemantics,
    /// Configuration language specification
    ConfigurationLanguage,
    /// Test specification
    Test,
    /// Documentation
    Documentation,
    /// Build configuration
    BuildConfig,
    /// Other
    Other,
}

/// Build status information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildStatus {
    /// Whether build was successful
    pub success: bool,
    /// Build errors
    pub errors: Vec<String>,
    /// Build warnings
    pub warnings: Vec<String>,
    /// Build time in milliseconds
    pub build_time: u64,
    /// Dependencies
    pub dependencies: Vec<String>,
    /// Built targets
    pub built_targets: Vec<String>,
    /// Build artifacts
    pub artifacts: Vec<String>,
    /// Build configuration used
    pub build_config: BuildConfig,
}

/// Validation result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Whether validation was successful
    pub success: bool,
    /// Validation errors
    pub errors: Vec<ValidationError>,
    /// Validation warnings
    pub warnings: Vec<ValidationWarning>,
    /// Validation time in milliseconds
    pub validation_time: u64,
    /// Files validated
    pub files_validated: Vec<String>,
}

/// Validation error.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationError {
    /// Error type
    pub error_type: ValidationErrorType,
    /// File path
    pub file: String,
    /// Line number
    pub line: Option<u32>,
    /// Column number
    pub column: Option<u32>,
    /// Error message
    pub message: String,
    /// Error severity
    pub severity: ErrorSeverity,
}

/// Validation warning.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationWarning {
    /// Warning type
    pub warning_type: ValidationWarningType,
    /// File path
    pub file: String,
    /// Line number
    pub line: Option<u32>,
    /// Column number
    pub column: Option<u32>,
    /// Warning message
    pub message: String,
}

/// Validation error type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationErrorType {
    Syntax,
    Type,
    Semantics,
    Dependency,
    Build,
    Configuration,
}

/// Validation warning type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationWarningType {
    Deprecated,
    Unused,
    Performance,
    Style,
    Documentation,
}

/// Error severity level.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

impl LeanSpecification {
    /// Create a new specification manager.
    pub fn new(spec_path: PathBuf) -> Self {
        Self {
            spec_path,
            files_cache: HashMap::new(),
            build_cache: HashMap::new(),
            dependency_graph: HashMap::new(),
            modification_times: HashMap::new(),
            build_config: BuildConfig::default(),
        }
    }

    /// Create a new specification manager with default path.
    pub fn new_default() -> BatonResult<Self> {
        let spec_path = Self::find_default_spec_path()?;
        Ok(Self::new(spec_path))
    }

    /// Find default specification path.
    fn find_default_spec_path() -> BatonResult<PathBuf> {
        let spec_paths = [
            PathBuf::from("./spec"),
            PathBuf::from("./specifications"),
            PathBuf::from("./lean-spec"),
            PathBuf::from("../spec"),
            PathBuf::from("../specifications"),
        ];

        for path in spec_paths {
            if path.exists() {
                return Ok(path);
            }
        }

        // Create default specification directory
        let default_path = PathBuf::from("./spec");
        fs::create_dir_all(&default_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to create spec directory: {}", e))
        })?;

        Ok(default_path)
    }

    /// Create a new specification manager with custom configuration.
    pub fn with_config(spec_path: PathBuf, build_config: BuildConfig) -> Self {
        Self {
            spec_path,
            files_cache: HashMap::new(),
            build_cache: HashMap::new(),
            dependency_graph: HashMap::new(),
            modification_times: HashMap::new(),
            build_config,
        }
    }

    /// Get specification path.
    pub fn spec_path(&self) -> &Path {
        &self.spec_path
    }

    /// Get build configuration.
    pub fn build_config(&self) -> &BuildConfig {
        &self.build_config
    }

    /// Set build configuration.
    pub fn set_build_config(&mut self, config: BuildConfig) {
        self.build_config = config;
        self.clear_caches();
    }

    /// List all specification files.
    pub fn list_files(&self) -> BatonResult<Vec<SpecFileInfo>> {
        let mut files = Vec::new();

        if !self.spec_path.exists() {
            return Ok(files);
        }

        for entry in fs::read_dir(&self.spec_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to read spec directory: {}", e))
        })? {
            let entry = entry.map_err(|e| {
                BatonError::FileSystemError(format!("Failed to read directory entry: {}", e))
            })?;

            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "lean") {
                let file_info = self.get_file_info(&path)?;
                files.push(file_info);
            }
        }

        Ok(files)
    }

    /// Get file information.
    pub fn get_file_info(&self, file_path: &Path) -> BatonResult<SpecFileInfo> {
        let file_name = file_path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| {
                BatonError::FileSystemError("Invalid file name".to_string())
            })?;

        let content = fs::read_to_string(file_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to read file {}: {}", file_name, e))
        })?;

        let metadata = fs::metadata(file_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to get file metadata: {}", e))
        })?;

        let modified = metadata
            .modified()
            .unwrap_or(UNIX_EPOCH)
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        let hash = self.compute_hash(&content);
        let file_type = self.determine_file_type(file_name);
        let dependencies = self.extract_dependencies(&content)?;

        Ok(SpecFileInfo {
            path: file_path.to_string_lossy().to_string(),
            hash,
            modified,
            valid: true, // Will be validated during build
            errors: Vec::new(),
            warnings: Vec::new(),
            dependencies,
            size: metadata.len(),
            file_type,
        })
    }

    /// Read file content.
    pub fn read_file(&self, file_name: &str) -> BatonResult<String> {
        let file_path = self.get_file_path(file_name);
        
        if !file_path.exists() {
            return Err(BatonError::SpecificationFileNotFound { path: file_path });
        }

        fs::read_to_string(&file_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to read file {}: {}", file_name, e))
        })
    }

    /// Write file content.
    pub fn write_file(&mut self, file_name: &str, content: &str) -> BatonResult<()> {
        let file_path = self.get_file_path(file_name);
        
        // Create parent directories if they don't exist
        if let Some(parent) = file_path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                BatonError::FileSystemError(format!("Failed to create directory: {}", e))
            })?;
        }

        fs::write(&file_path, content).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to write file {}: {}", file_name, e))
        })?;

        // Update cache
        self.files_cache.insert(file_name.to_string(), content.to_string());
        self.build_cache.clear();

        Ok(())
    }

    /// Check if file exists.
    pub fn file_exists(&self, file_name: &str) -> bool {
        self.get_file_path(file_name).exists()
    }

    /// Get file path.
    pub fn get_file_path(&self, file_name: &str) -> PathBuf {
        self.spec_path.join(file_name)
    }

    /// Validate file content.
    pub fn validate_file_content(
        &self,
        content: &str,
        file_name: &str,
    ) -> (bool, Vec<String>, Vec<String>) {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Basic syntax validation
        if content.trim().is_empty() {
            warnings.push("File is empty".to_string());
        }

        // Check for common Lean syntax issues
        if !content.contains("import") && !content.contains("def") && !content.contains("theorem") {
            warnings.push("File may not contain valid Lean code".to_string());
        }

        // Check for unmatched braces/parentheses
        let open_braces = content.matches('{').count();
        let close_braces = content.matches('}').count();
        if open_braces != close_braces {
            errors.push("Unmatched braces".to_string());
        }

        let open_parens = content.matches('(').count();
        let close_parens = content.matches(')').count();
        if open_parens != close_parens {
            errors.push("Unmatched parentheses".to_string());
        }

        let valid = errors.is_empty();
        (valid, errors, warnings)
    }

    /// Build specification.
    pub async fn build(&mut self) -> BatonResult<BuildStatus> {
        let start_time = std::time::Instant::now();

        if !self.spec_path.exists() {
            return Err(BatonError::SpecificationNotFound(
                "Specification directory does not exist".to_string(),
            ));
        }

        let mut command = Command::new("lean");
        command.arg("--make");

        if self.build_config.verbose {
            command.arg("--verbose");
        }

        for flag in &self.build_config.build_flags {
            command.arg(flag);
        }

        command.arg(&self.spec_path);

        let build_future = command.output();
        let output = if self.build_config.timeout > 0 {
            timeout(Duration::from_secs(self.build_config.timeout), build_future)
                .await
                .map_err(|_| BatonError::Timeout("Build timeout".to_string()))?
        } else {
            build_future.await
        }
        .map_err(|e| BatonError::BuildSystemError(format!("Build command failed: {}", e)))?;

        let build_time = start_time.elapsed().as_millis() as u64;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let success = output.status.success();
        let errors: Vec<String> = stderr
            .lines()
            .filter(|line| line.contains("error") || line.contains("Error"))
            .map(|s| s.to_string())
            .collect();

        let warnings: Vec<String> = stderr
            .lines()
            .filter(|line| line.contains("warning") || line.contains("Warning"))
            .map(|s| s.to_string())
            .collect();

        let dependencies = self.extract_dependencies_from_build(&stdout)?;
        let artifacts = self.get_build_artifacts().await?;

        let build_status = BuildStatus {
            success,
            errors,
            warnings,
            build_time,
            dependencies,
            built_targets: self.build_config.targets.clone(),
            artifacts,
            build_config: self.build_config.clone(),
        };

        // Update cache
        if success {
            self.build_cache.insert("build".to_string(), true);
        }

        Ok(build_status)
    }

    /// Check if specification is up to date.
    pub fn is_up_to_date(&self) -> bool {
        // Check if any files have been modified since last build
        for file_info in self.list_files().unwrap_or_default() {
            if let Some(last_build) = self.modification_times.get(&file_info.path) {
                if file_info.modified > *last_build {
                    return false;
                }
            } else {
                return false;
            }
        }

        // Check if build cache indicates successful build
        self.build_cache.get("build").copied().unwrap_or(false)
    }

    /// Clean build artifacts.
    pub async fn clean(&mut self) -> BatonResult<()> {
        let mut command = Command::new("lean");
        command.arg("--make");
        command.arg("--clean");
        command.arg(&self.spec_path);

        let output = command
            .output()
            .await
            .map_err(|e| BatonError::BuildSystemError(format!("Clean command failed: {}", e)))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(BatonError::BuildSystemError(format!(
                "Clean failed: {}",
                stderr
            )));
        }

        // Clear caches
        self.clear_caches();

        Ok(())
    }

    /// Get specification version.
    pub fn get_version(&self) -> BatonResult<String> {
        // Try to read version from a version file or extract from build
        let version_file = self.spec_path.join("version.txt");
        
        if version_file.exists() {
            fs::read_to_string(version_file).map_err(|e| {
                BatonError::FileSystemError(format!("Failed to read version file: {}", e))
            })
        } else {
            Ok("1.0.0".to_string()) // Default version
        }
    }

    /// Extract dependencies from file content.
    fn extract_dependencies(&self, content: &str) -> BatonResult<Vec<String>> {
        let mut dependencies = Vec::new();

        for line in content.lines() {
            let line = line.trim();
            if line.starts_with("import") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 2 {
                    dependencies.push(parts[1].to_string());
                }
            }
        }

        Ok(dependencies)
    }

    /// Extract dependencies from build output.
    fn extract_dependencies_from_build(&self, output: &str) -> BatonResult<Vec<String>> {
        let mut dependencies = Vec::new();

        for line in output.lines() {
            if line.contains("import") || line.contains("depend") {
                // Extract dependency information from build output
                // This is a simplified implementation
                if let Some(dep) = line.split_whitespace().nth(1) {
                    dependencies.push(dep.to_string());
                }
            }
        }

        Ok(dependencies)
    }

    /// Get build artifacts.
    async fn get_build_artifacts(&self) -> BatonResult<Vec<String>> {
        let mut artifacts = Vec::new();

        // Look for common build artifact directories
        let artifact_dirs = ["build", "target", "out", ".lake"];

        for dir_name in artifact_dirs {
            let dir_path = self.spec_path.join(dir_name);
            if dir_path.exists() && dir_path.is_dir() {
                if let Ok(entries) = fs::read_dir(dir_path) {
                    for entry in entries {
                        if let Ok(entry) = entry {
                            artifacts.push(entry.path().to_string_lossy().to_string());
                        }
                    }
                }
            }
        }

        Ok(artifacts)
    }

    /// Determine file type based on name and content.
    fn determine_file_type(&self, file_name: &str) -> SpecFileType {
        let lower_name = file_name.to_lowercase();
        
        if lower_name.contains("main") || lower_name.contains("core") {
            SpecFileType::Main
        } else if lower_name.contains("type") || lower_name.contains("typing") {
            SpecFileType::TypeSystem
        } else if lower_name.contains("op") || lower_name.contains("semantics") {
            SpecFileType::OperationalSemantics
        } else if lower_name.contains("config") || lower_name.contains("conf") {
            SpecFileType::ConfigurationLanguage
        } else if lower_name.contains("test") || lower_name.contains("spec") {
            SpecFileType::Test
        } else if lower_name.contains("doc") || lower_name.contains("readme") {
            SpecFileType::Documentation
        } else if lower_name.contains("lake") || lower_name.contains("build") {
            SpecFileType::BuildConfig
        } else {
            SpecFileType::Other
        }
    }

    /// Compute content hash.
    fn compute_hash(&self, content: &str) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        content.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    /// Clear all caches.
    pub fn clear_caches(&mut self) {
        self.files_cache.clear();
        self.build_cache.clear();
        self.dependency_graph.clear();
        self.modification_times.clear();
    }

    /// Validate specification.
    pub async fn validate(&self) -> BatonResult<ValidationResult> {
        let start_time = std::time::Instant::now();
        let mut errors = Vec::new();
        let mut warnings = Vec::new();
        let mut files_validated = Vec::new();

        // Validate each file
        for file_info in self.list_files()? {
            files_validated.push(file_info.path.clone());
            
            let (valid, file_errors, file_warnings) = 
                self.validate_file_content(&self.read_file(&file_info.path)?, &file_info.path);

            for error in file_errors {
                errors.push(ValidationError {
                    error_type: ValidationErrorType::Syntax,
                    file: file_info.path.clone(),
                    line: None,
                    column: None,
                    message: error,
                    severity: ErrorSeverity::Error,
                });
            }

            for warning in file_warnings {
                warnings.push(ValidationWarning {
                    warning_type: ValidationWarningType::Style,
                    file: file_info.path.clone(),
                    line: None,
                    column: None,
                    message: warning,
                });
            }
        }

        // Check dependencies
        let dep_errors = self.check_dependencies()?;
        errors.extend(dep_errors);

        let validation_time = start_time.elapsed().as_millis() as u64;
        let success = errors.is_empty();

        Ok(ValidationResult {
            success,
            errors,
            warnings,
            validation_time,
            files_validated,
        })
    }

    /// Check dependencies for issues.
    fn check_dependencies(&self) -> BatonResult<Vec<ValidationError>> {
        let mut errors = Vec::new();

        // Check for circular dependencies
        if let Some(cycle) = self.find_circular_dependencies() {
            errors.push(ValidationError {
                error_type: ValidationErrorType::Dependency,
                file: "dependency_graph".to_string(),
                line: None,
                column: None,
                message: format!("Circular dependency detected: {}", cycle.join(" -> ")),
                severity: ErrorSeverity::Error,
            });
        }

        // Check for missing dependencies
        for (file, deps) in &self.dependency_graph {
            for dep in deps {
                if !self.is_external_dependency(dep) && !self.file_exists(dep) {
                    errors.push(ValidationError {
                        error_type: ValidationErrorType::Dependency,
                        file: file.clone(),
                        line: None,
                        column: None,
                        message: format!("Missing dependency: {}", dep),
                        severity: ErrorSeverity::Error,
                    });
                }
            }
        }

        Ok(errors)
    }

    /// Find circular dependencies using DFS.
    fn find_circular_dependencies(&self) -> Option<Vec<String>> {
        let mut visited = std::collections::HashSet::new();
        let mut rec_stack = std::collections::HashSet::new();

        for node in self.dependency_graph.keys() {
            if !visited.contains(node) {
                let mut path = Vec::new();
                if let Some(cycle) = self.dfs_cycle_detection(node, &mut visited, &mut rec_stack, &mut path) {
                    return Some(cycle);
                }
            }
        }

        None
    }

    /// DFS cycle detection helper.
    fn dfs_cycle_detection(
        &self,
        node: &str,
        visited: &mut std::collections::HashSet<String>,
        rec_stack: &mut std::collections::HashSet<String>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        visited.insert(node.to_string());
        rec_stack.insert(node.to_string());
        path.push(node.to_string());

        if let Some(deps) = self.dependency_graph.get(node) {
            for dep in deps {
                if !visited.contains(dep) {
                    if let Some(cycle) = self.dfs_cycle_detection(dep, visited, rec_stack, path) {
                        return Some(cycle);
                    }
                } else if rec_stack.contains(dep) {
                    // Found a cycle
                    let cycle_start = path.iter().position(|x| x == dep).unwrap_or(0);
                    return Some(path[cycle_start..].to_vec());
                }
            }
        }

        rec_stack.remove(node);
        path.pop();
        None
    }

    /// Check if dependency is external.
    fn is_external_dependency(&self, dep: &str) -> bool {
        // Common external dependencies
        let external_deps = [
            "Init", "Lean", "Std", "Mathlib", "Aesop", "Tactic", "Meta", "Core",
        ];

        external_deps.iter().any(|&external| dep.starts_with(external))
    }

    /// Check specification file.
    pub async fn check_specification(&self, file_name: &str) -> BatonResult<bool> {
        let file_path = self.get_file_path(file_name);
        
        if !file_path.exists() {
            return Err(BatonError::SpecificationFileNotFound { path: file_path });
        }

        let content = self.read_file(file_name)?;
        let (valid, _, _) = self.validate_file_content(&content, file_name);

        Ok(valid)
    }

    /// Get specification statistics.
    pub fn get_statistics(&self) -> BatonResult<SpecStatistics> {
        let files = self.list_files()?;
        let total_files = files.len();
        let total_size: u64 = files.iter().map(|f| f.size).sum();
        let valid_files = files.iter().filter(|f| f.valid).count();
        let error_count: usize = files.iter().map(|f| f.errors.len()).sum();
        let warning_count: usize = files.iter().map(|f| f.warnings.len()).sum();
        let file_types: Vec<SpecFileType> = files.iter().map(|f| f.file_type.clone()).collect();

        Ok(SpecStatistics {
            total_files,
            total_size,
            valid_files,
            error_count,
            warning_count,
            file_types,
        })
    }
}

/// Specification statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecStatistics {
    /// Total number of files
    pub total_files: usize,
    /// Total size in bytes
    pub total_size: u64,
    /// Number of valid files
    pub valid_files: usize,
    /// Total number of errors
    pub error_count: usize,
    /// Total number of warnings
    pub warning_count: usize,
    /// File types present
    pub file_types: Vec<SpecFileType>,
}

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        LeanSpecification, BuildConfig, SpecFileInfo, SpecFileType,
        BuildStatus, ValidationResult, ValidationError, ValidationWarning,
        ValidationErrorType, ValidationWarningType, ErrorSeverity, SpecStatistics,
    };
} 