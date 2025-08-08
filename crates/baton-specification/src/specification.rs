//! Core specification management functionality.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use baton_engine_plugin::prelude::*;
use tokio::process::Command;

use crate::types::*;

/// Generic specification manager that can work with any verification engine.
pub struct Specification {
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
    /// Engine configuration
    #[allow(dead_code)]
    engine_config: EngineConfig,
    /// Engine name for file extensions and commands
    engine_name: String,
}

impl Specification {
    /// Create a new specification manager.
    pub fn new(spec_path: PathBuf, engine_name: String, engine_config: EngineConfig) -> Self {
        Self {
            spec_path,
            files_cache: HashMap::new(),
            build_cache: HashMap::new(),
            dependency_graph: HashMap::new(),
            modification_times: HashMap::new(),
            build_config: engine_config.build_config.clone(),
            engine_config,
            engine_name,
        }
    }

    /// Create a new specification manager with default path.
    pub fn new_default(engine_name: String, engine_config: EngineConfig) -> BatonResult<Self> {
        let spec_path = Self::find_default_spec_path(&engine_name)?;
        Ok(Self::new(spec_path, engine_name, engine_config))
    }

    /// Find default specification path.
    fn find_default_spec_path(engine_name: &str) -> BatonResult<PathBuf> {
        let spec_paths = [
            PathBuf::from("./spec"),
            PathBuf::from("./specifications"),
            PathBuf::from(&format!("./{engine_name}-spec")),
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
        std::fs::create_dir_all(&default_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to create spec directory: {e}"))
        })?;

        Ok(default_path)
    }

    /// Create a new specification manager with custom configuration.
    pub fn with_config(
        spec_path: PathBuf,
        engine_name: String,
        engine_config: EngineConfig,
        build_config: BuildConfig,
    ) -> Self {
        Self {
            spec_path,
            files_cache: HashMap::new(),
            build_cache: HashMap::new(),
            dependency_graph: HashMap::new(),
            modification_times: HashMap::new(),
            build_config,
            engine_config,
            engine_name,
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

    /// Get engine name.
    pub fn engine_name(&self) -> &str {
        &self.engine_name
    }

    /// List all specification files.
    pub fn list_files(&self) -> BatonResult<Vec<SpecFileInfo>> {
        let mut files = Vec::new();

        if !self.spec_path.exists() {
            return Ok(files);
        }

        for entry in std::fs::read_dir(&self.spec_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to read spec directory: {e}"))
        })? {
            let entry = entry.map_err(|e| {
                BatonError::FileSystemError(format!("Failed to read directory entry: {e}"))
            })?;

            let path = entry.path();
            if path.is_file() && self.is_specification_file(&path) {
                let file_info = self.get_file_info(&path)?;
                files.push(file_info);
            }
        }

        Ok(files)
    }

    /// Check if a file is a specification file for this engine.
    fn is_specification_file(&self, path: &Path) -> bool {
        if let Some(extension) = path.extension() {
            let ext = extension.to_string_lossy().to_lowercase();
            ext == self.engine_name.to_lowercase() || ext == "spec" || ext == "def"
        } else {
            false
        }
    }

    /// Get file information.
    pub fn get_file_info(&self, file_path: &Path) -> BatonResult<SpecFileInfo> {
        let content = std::fs::read_to_string(file_path).map_err(|e| {
            BatonError::FileSystemError(format!(
                "Failed to read file {}: {}",
                file_path.display(),
                e
            ))
        })?;

        let metadata = std::fs::metadata(file_path).map_err(|e| {
            BatonError::FileSystemError(format!(
                "Failed to get metadata for {}: {}",
                file_path.display(),
                e
            ))
        })?;

        let modified = metadata
            .modified()
            .map_err(|e| {
                BatonError::FileSystemError(format!(
                    "Failed to get modification time for {}: {}",
                    file_path.display(),
                    e
                ))
            })?
            .duration_since(UNIX_EPOCH)
            .map_err(|e| {
                BatonError::FileSystemError(format!(
                    "Failed to convert modification time for {}: {}",
                    file_path.display(),
                    e
                ))
            })?
            .as_secs();

        let (valid, errors, warnings) = self.validate_file_content(
            &content,
            file_path.file_name().unwrap().to_string_lossy().as_ref(),
        );

        let dependencies = self.extract_dependencies(&content)?;

        Ok(SpecFileInfo {
            path: file_path.to_string_lossy().to_string(),
            hash: self.compute_hash(&content),
            modified,
            valid,
            errors,
            warnings,
            dependencies,
            size: metadata.len(),
            file_type: self
                .determine_file_type(file_path.file_name().unwrap().to_string_lossy().as_ref()),
        })
    }

    /// Read a specification file.
    pub fn read_file(&self, file_name: &str) -> BatonResult<String> {
        let file_path = self.get_file_path(file_name);
        std::fs::read_to_string(&file_path).map_err(|e| {
            BatonError::FileSystemError(format!(
                "Failed to read file {}: {}",
                file_path.display(),
                e
            ))
        })
    }

    /// Write a specification file.
    pub fn write_file(&mut self, file_name: &str, content: &str) -> BatonResult<()> {
        let file_path = self.get_file_path(file_name);

        // Create parent directory if it doesn't exist
        if let Some(parent) = file_path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                BatonError::FileSystemError(format!(
                    "Failed to create directory {}: {}",
                    parent.display(),
                    e
                ))
            })?;
        }

        std::fs::write(&file_path, content).map_err(|e| {
            BatonError::FileSystemError(format!(
                "Failed to write file {}: {}",
                file_path.display(),
                e
            ))
        })?;

        // Update cache
        self.files_cache
            .insert(file_name.to_string(), content.to_string());
        self.modification_times.insert(
            file_name.to_string(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        );

        Ok(())
    }

    /// Check if a file exists.
    pub fn file_exists(&self, file_name: &str) -> bool {
        self.get_file_path(file_name).exists()
    }

    /// Get the full path for a file.
    pub fn get_file_path(&self, file_name: &str) -> PathBuf {
        self.spec_path.join(file_name)
    }

    /// Validate file content.
    #[allow(clippy::type_complexity)]
    pub fn validate_file_content(
        &self,
        content: &str,
        _file_name: &str,
    ) -> (bool, Vec<String>, Vec<String>) {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Basic validation - check for common issues
        if content.trim().is_empty() {
            errors.push("File is empty".to_string());
        }

        // Check for common syntax issues
        if content.contains("TODO") || content.contains("FIXME") {
            warnings.push("File may contain incomplete code".to_string());
        }

        // Engine-specific validation could be added here
        // For now, we'll assume the file is valid if it's not empty
        let valid = !content.trim().is_empty() && errors.is_empty();

        (valid, errors, warnings)
    }

    /// Build the specification.
    pub async fn build(&mut self) -> BatonResult<BuildStatus> {
        let start_time = std::time::Instant::now();

        if !self.spec_path.exists() {
            return Err(BatonError::FileSystemError(
                "Specification directory does not exist".to_string(),
            ));
        }

        // Try to run the engine's build command
        let mut command = Command::new(&self.engine_name);

        if self.build_config.verbose {
            command.arg("--verbose");
        }

        if self.build_config.parallel {
            command.arg("--parallel");
        }

        for flag in &self.build_config.build_flags {
            command.arg(flag);
        }

        for target in &self.build_config.targets {
            command.arg(target);
        }

        command.current_dir(&self.spec_path);

        let output = command
            .output()
            .await
            .map_err(|e| BatonError::BuildSystemError(format!("Build command failed: {e}")))?;

        let build_time = start_time.elapsed().as_millis() as u64;
        let success = output.status.success();

        let errors = if success {
            vec![]
        } else {
            vec![String::from_utf8_lossy(&output.stderr).to_string()]
        };

        let warnings = vec![String::from_utf8_lossy(&output.stdout).to_string()];

        let dependencies =
            self.extract_dependencies_from_build(&String::from_utf8_lossy(&output.stdout))?;
        let artifacts = self.get_build_artifacts().await?;

        Ok(BuildStatus {
            success,
            errors,
            warnings,
            build_time,
            dependencies,
            built_targets: self.build_config.targets.clone(),
            artifacts,
            build_config: self.build_config.clone(),
        })
    }

    /// Check if the specification is up to date.
    pub fn is_up_to_date(&self) -> bool {
        // Check if any files have been modified since last build
        for (file_name, cached_time) in &self.modification_times {
            if let Ok(metadata) = std::fs::metadata(self.get_file_path(file_name)) {
                if let Ok(modified) = metadata.modified() {
                    if let Ok(duration) = modified.duration_since(UNIX_EPOCH) {
                        if duration.as_secs() > *cached_time {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    /// Clean build artifacts.
    pub async fn clean(&mut self) -> BatonResult<()> {
        let mut command = Command::new(&self.engine_name);
        command.arg("--clean");
        command.current_dir(&self.spec_path);

        let output = command
            .output()
            .await
            .map_err(|e| BatonError::BuildSystemError(format!("Clean command failed: {e}")))?;

        if !output.status.success() {
            return Err(BatonError::BuildSystemError(format!(
                "Clean failed: {}",
                String::from_utf8_lossy(&output.stderr)
            )));
        }

        self.clear_caches();
        Ok(())
    }

    /// Get engine version.
    pub async fn get_version(&self) -> BatonResult<String> {
        let mut command = Command::new(&self.engine_name);
        command.arg("--version");

        let output = command
            .output()
            .await
            .map_err(|e| BatonError::InternalError(format!("Failed to get version: {e}")))?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        } else {
            Err(BatonError::InternalError(
                "Failed to get version".to_string(),
            ))
        }
    }

    /// Extract dependencies from file content.
    fn extract_dependencies(&self, content: &str) -> BatonResult<Vec<String>> {
        // This is a simplified implementation
        // In a real implementation, this would parse the file and extract actual dependencies
        let mut dependencies = Vec::new();

        // Look for import statements
        for line in content.lines() {
            let line = line.trim();
            if line.starts_with("import") || line.starts_with("require") || line.starts_with("use")
            {
                // Extract module name from import statement
                if let Some(module) = line.split_whitespace().nth(1) {
                    dependencies.push(module.to_string());
                }
            }
        }

        Ok(dependencies)
    }

    /// Extract dependencies from build output.
    fn extract_dependencies_from_build(&self, _output: &str) -> BatonResult<Vec<String>> {
        // This is a simplified implementation
        // In a real implementation, this would parse the build output
        Ok(vec![])
    }

    /// Get build artifacts.
    async fn get_build_artifacts(&self) -> BatonResult<Vec<String>> {
        // This is a simplified implementation
        // In a real implementation, this would scan for build artifacts
        Ok(vec![])
    }

    /// Determine file type based on filename.
    fn determine_file_type(&self, file_name: &str) -> SpecFileType {
        let name = file_name.to_lowercase();

        if name.contains("main") || name.contains("core") {
            SpecFileType::Main
        } else if name.contains("type") || name.contains("types") {
            SpecFileType::TypeSystem
        } else if name.contains("semantics") || name.contains("opsem") {
            SpecFileType::OperationalSemantics
        } else if name.contains("config") || name.contains("conf") {
            SpecFileType::ConfigurationLanguage
        } else if name.contains("test") || name.contains("spec") {
            SpecFileType::Test
        } else if name.contains("doc") || name.contains("readme") {
            SpecFileType::Documentation
        } else if name.contains("build") {
            SpecFileType::BuildConfig
        } else {
            SpecFileType::Other
        }
    }

    /// Compute hash of file content.
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

    /// Validate the specification.
    pub async fn validate(&self) -> BatonResult<ValidationResult> {
        let start_time = std::time::Instant::now();
        let mut errors = Vec::new();
        let mut warnings = Vec::new();
        let mut files_validated = Vec::new();

        let files = self.list_files()?;

        for file_info in &files {
            files_validated.push(file_info.path.clone());

            if !file_info.valid {
                errors.push(ValidationError {
                    error_type: ValidationErrorType::Syntax,
                    file: file_info.path.clone(),
                    line: None,
                    column: None,
                    message: "File validation failed".to_string(),
                    severity: ErrorSeverity::Error,
                });
            }

            for error in &file_info.errors {
                warnings.push(ValidationWarning {
                    warning_type: ValidationWarningType::Style,
                    file: file_info.path.clone(),
                    line: None,
                    column: None,
                    message: error.clone(),
                });
            }
        }

        // Check dependencies
        let dependency_errors = self.check_dependencies()?;
        errors.extend(dependency_errors);

        let validation_time = start_time.elapsed().as_millis() as u64;

        Ok(ValidationResult {
            success: errors.is_empty(),
            errors,
            warnings,
            validation_time,
            files_validated,
        })
    }

    /// Check dependencies for errors.
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

        Ok(errors)
    }

    /// Find circular dependencies.
    fn find_circular_dependencies(&self) -> Option<Vec<String>> {
        let mut visited = std::collections::HashSet::new();
        let mut rec_stack = std::collections::HashSet::new();
        let mut path = Vec::new();

        for node in self.dependency_graph.keys() {
            if !visited.contains(node) {
                if let Some(cycle) =
                    self.dfs_cycle_detection(node, &mut visited, &mut rec_stack, &mut path)
                {
                    return Some(cycle);
                }
            }
        }

        None
    }

    /// DFS cycle detection.
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

        if let Some(dependencies) = self.dependency_graph.get(node) {
            for dep in dependencies {
                if !visited.contains(dep) {
                    if let Some(cycle) = self.dfs_cycle_detection(dep, visited, rec_stack, path) {
                        return Some(cycle);
                    }
                } else if rec_stack.contains(dep) {
                    // Found a cycle
                    let cycle_start = path.iter().position(|x| x == dep).unwrap();
                    return Some(path[cycle_start..].to_vec());
                }
            }
        }

        rec_stack.remove(node);
        path.pop();
        None
    }

    /// Check if a dependency is external.
    #[allow(dead_code)]
    fn is_external_dependency(&self, dep: &str) -> bool {
        // This is a simplified implementation
        // In a real implementation, this would check against known external dependencies
        dep.starts_with("std") || dep.starts_with("core") || dep.starts_with("lib")
    }

    /// Check specification compilation.
    pub async fn check_specification(&self, file_name: &str) -> BatonResult<bool> {
        let file_path = self.get_file_path(file_name);

        if !file_path.exists() {
            return Ok(false);
        }

        // Try to compile/check the file
        let mut command = Command::new(&self.engine_name);
        command.arg("--check");
        command.arg(&file_path);

        let output = command
            .output()
            .await
            .map_err(|e| BatonError::BuildSystemError(format!("Check command failed: {e}")))?;

        Ok(output.status.success())
    }

    /// Get specification statistics.
    pub fn get_statistics(&self) -> BatonResult<SpecStatistics> {
        let files = self.list_files()?;

        let total_files = files.len();
        let total_size = files.iter().map(|f| f.size).sum();
        let valid_files = files.iter().filter(|f| f.valid).count();
        let error_count = files.iter().map(|f| f.errors.len()).sum();
        let warning_count = files.iter().map(|f| f.warnings.len()).sum();
        let file_types = files.iter().map(|f| f.file_type.clone()).collect();

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
