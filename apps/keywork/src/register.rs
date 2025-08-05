//! Register manifest handling and validation.

use crate::dependency::{install_dependencies, resolve_dependencies_from_manifest};
use crate::xdg_config::KeyworkXdgConfig;
use miette::{miette, IntoDiagnostic, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use tokio::fs as tokio_fs;
use walkdir::WalkDir;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Register {
    #[serde(rename = "register")]
    pub manifest: RegisterManifest,
    #[serde(default)]
    pub dependencies: HashMap<String, String>,
    #[serde(default)]
    pub exports: HashMap<String, String>,
    #[serde(default)]
    pub metadata: Option<RegisterMetadata>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegisterManifest {
    pub name: String,
    pub version: String,
    pub description: String,
    pub authors: Vec<String>,
    pub license: String,
    pub repository: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegisterMetadata {
    pub tags: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct BuildArtifact {
    pub name: String,
    pub version: String,
    pub files: Vec<PathBuf>,
    pub dependencies: HashMap<String, String>,
    pub checksum: String,
    pub build_time: std::time::SystemTime,
}

#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub valid: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
    pub dependencies_resolved: bool,
    pub modules_found: Vec<PathBuf>,
}

impl Register {
    pub fn load(path: &Path) -> Result<Self> {
        let manifest_path = path.join("register.toml");

        if !manifest_path.exists() {
            return Err(miette!("No register.toml found in {}", path.display()));
        }

        let content = fs::read_to_string(&manifest_path)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to read register.toml: {}", e))?;

        let register: Register = toml::from_str(&content)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to parse register.toml: {}", e))?;

        Ok(register)
    }

    pub fn name(&self) -> &str {
        &self.manifest.name
    }

    pub fn version(&self) -> &str {
        &self.manifest.version
    }

    pub fn description(&self) -> &str {
        &self.manifest.description
    }

    pub fn authors(&self) -> &[String] {
        &self.manifest.authors
    }

    pub fn license(&self) -> &str {
        &self.manifest.license
    }

    pub fn dependencies(&self) -> &HashMap<String, String> {
        &self.dependencies
    }

    pub fn exports(&self) -> &HashMap<String, String> {
        &self.exports
    }

    pub async fn validate(&self, path: &Path) -> Result<ValidationResult> {
        let mut result = ValidationResult {
            valid: true,
            errors: Vec::new(),
            warnings: Vec::new(),
            dependencies_resolved: false,
            modules_found: Vec::new(),
        };

        // Validate manifest fields
        if self.manifest.name.is_empty() {
            result
                .errors
                .push("Register name cannot be empty".to_string());
            result.valid = false;
        }

        if self.manifest.version.is_empty() {
            result
                .errors
                .push("Register version cannot be empty".to_string());
            result.valid = false;
        }

        if self.manifest.description.is_empty() {
            result
                .errors
                .push("Register description cannot be empty".to_string());
            result.valid = false;
        }

        if self.manifest.authors.is_empty() {
            result
                .errors
                .push("Register must have at least one author".to_string());
            result.valid = false;
        }

        if self.manifest.license.is_empty() {
            result
                .errors
                .push("Register license cannot be empty".to_string());
            result.valid = false;
        }

        // Validate version format
        if !self.is_valid_version(&self.manifest.version) {
            result
                .errors
                .push(format!("Invalid version format: {}", self.manifest.version));
            result.valid = false;
        }

        // Validate that exported modules exist
        for (name, module_path) in &self.exports {
            let full_path = path.join(module_path);
            if !full_path.exists() {
                result.errors.push(format!(
                    "Exported module '{}' not found at path: {}",
                    name, module_path
                ));
                result.valid = false;
            } else {
                result.modules_found.push(full_path);
            }
        }

        // Validate module syntax
        for module_path in &result.modules_found {
            if let Err(e) = self.validate_module_syntax(module_path).await {
                result
                    .errors
                    .push(format!("Syntax error in {}: {}", module_path.display(), e));
                result.valid = false;
            }
        }

        // Check for unused modules
        let all_modules = self.find_modules(path)?;
        let exported_modules: HashSet<_> = self.exports.values().collect();

        for module in &all_modules {
            let relative_path = module
                .strip_prefix(path)
                .map_err(|_| miette!("Failed to get relative path"))?
                .to_string_lossy();

            let relative_path_string = relative_path.to_string();
            if !exported_modules.contains(&relative_path_string) {
                result
                    .warnings
                    .push(format!("Module {} is not exported", relative_path));
            }
        }

        // Validate dependencies
        if !self.dependencies.is_empty() {
            match self.validate_dependencies().await {
                Ok(_) => {
                    result.dependencies_resolved = true;
                }
                Err(e) => {
                    result
                        .errors
                        .push(format!("Dependency validation failed: {}", e));
                    result.valid = false;
                }
            }
        }

        // Check for common issues
        if self.exports.is_empty() {
            result.warnings.push("No modules are exported".to_string());
        }

        if self.manifest.name.contains(' ') {
            result.warnings.push(
                "Register name contains spaces - consider using hyphens or underscores".to_string(),
            );
        }

        Ok(result)
    }

    async fn validate_module_syntax(&self, module_path: &Path) -> Result<()> {
        use ligature_parser::Parser;
        use ligature_types::checker::TypeChecker;

        let content = tokio_fs::read_to_string(module_path)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to read module: {}", e))?;

        // Parse the module
        let mut parser = Parser::new();
        let ast = parser
            .parse_module(&content)
            .map_err(|e| miette!("Parse error: {}", e))?;

        // Type check the module
        let mut checker = TypeChecker::new();
        checker
            .check_module(&ast)
            .map_err(|e| miette!("Type error: {}", e))?;

        Ok(())
    }

    async fn validate_dependencies(&self) -> Result<()> {
        // Create a temporary manifest file for dependency resolution
        let temp_dir = tempfile::tempdir()
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create temp directory: {}", e))?;

        let manifest_path = temp_dir.path().join("register.toml");
        let manifest_content = toml::to_string_pretty(self)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to serialize manifest: {}", e))?;

        tokio_fs::write(&manifest_path, manifest_content)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to write temp manifest: {}", e))?;

        // Resolve dependencies
        let mut graph = resolve_dependencies_from_manifest(&manifest_path).await?;
        let resolution = graph.resolve_dependencies().await?;

        if !resolution.success {
            return Err(miette!("Dependency resolution failed"));
        }

        Ok(())
    }

    pub async fn build(&self, path: &Path, output_dir: &Path) -> Result<BuildArtifact> {
        // Validate before building
        let validation = self.validate(path).await?;
        if !validation.valid {
            return Err(miette!(
                "Register validation failed:\n{}",
                validation.errors.join("\n")
            ));
        }

        // Create output directory structure
        tokio_fs::create_dir_all(output_dir)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create output directory: {}", e))?;

        let mut artifact_files = Vec::new();

        // Copy register.toml
        let output_manifest = output_dir.join("register.toml");
        let manifest_content = toml::to_string_pretty(self)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to serialize register manifest: {}", e))?;

        tokio_fs::write(&output_manifest, manifest_content)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to write register.toml: {}", e))?;

        artifact_files.push(output_manifest);

        // Copy exported modules
        for (name, module_path) in &self.exports {
            let source_path = path.join(module_path);
            let dest_path = output_dir.join(module_path);

            // Create parent directory if needed
            if let Some(parent) = dest_path.parent() {
                tokio_fs::create_dir_all(parent)
                    .await
                    .into_diagnostic()
                    .map_err(|e| miette!("Failed to create output directory: {}", e))?;
            }

            tokio_fs::copy(&source_path, &dest_path)
                .await
                .into_diagnostic()
                .map_err(|e| miette!("Failed to copy module '{}': {}", name, e))?;

            artifact_files.push(dest_path);
        }

        // Resolve and install dependencies
        let dependencies_dir = output_dir.join("dependencies");
        if !self.dependencies.is_empty() {
            let graph = resolve_dependencies_from_manifest(&path.join("register.toml")).await?;
            install_dependencies(&graph, &dependencies_dir).await?;
        }

        // Generate checksum
        let checksum = self.generate_checksum(&artifact_files).await?;

        // Create build artifact
        let artifact = BuildArtifact {
            name: self.manifest.name.clone(),
            version: self.manifest.version.clone(),
            files: artifact_files,
            dependencies: self.dependencies.clone(),
            checksum,
            build_time: std::time::SystemTime::now(),
        };

        // Write build info
        let build_info_path = output_dir.join("build-info.json");
        let build_info = serde_json::to_string_pretty(&artifact)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to serialize build info: {}", e))?;

        tokio_fs::write(build_info_path, build_info)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to write build info: {}", e))?;

        Ok(artifact)
    }

    async fn generate_checksum(&self, files: &[PathBuf]) -> Result<String> {
        use sha2::{Digest, Sha256};

        let mut hasher = Sha256::new();

        for file in files {
            let content = tokio_fs::read(file)
                .await
                .into_diagnostic()
                .map_err(|e| miette!("Failed to read file for checksum: {}", e))?;
            hasher.update(&content);
        }

        let result = hasher.finalize();
        Ok(format!("{:x}", result))
    }

    pub async fn package(&self, path: &Path, output_path: &Path) -> Result<()> {
        // Build the register first
        let temp_build_dir = tempfile::tempdir()
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create temp build directory: {}", e))?;

        let _artifact = self.build(path, temp_build_dir.path()).await?;

        // Create tar.gz archive
        self.create_archive(temp_build_dir.path(), output_path)
            .await?;

        Ok(())
    }

    async fn create_archive(&self, source_dir: &Path, output_path: &Path) -> Result<()> {
        use flate2::write::GzEncoder;
        use flate2::Compression;
        use tar::Builder;

        let file = std::fs::File::create(output_path)
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create archive file: {}", e))?;

        let gz = GzEncoder::new(file, Compression::default());
        let mut tar = Builder::new(gz);

        // Add all files from source directory to archive
        for entry in WalkDir::new(source_dir)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file())
        {
            let path = entry.path();
            let name = path
                .strip_prefix(source_dir)
                .into_diagnostic()
                .map_err(|e| miette!("Failed to get relative path: {}", e))?;

            let mut file = std::fs::File::open(path)
                .into_diagnostic()
                .map_err(|e| miette!("Failed to open file for archiving: {}", e))?;

            tar.append_file(name, &mut file)
                .into_diagnostic()
                .map_err(|e| miette!("Failed to add file to archive: {}", e))?;
        }

        tar.finish()
            .into_diagnostic()
            .map_err(|e| miette!("Failed to finish archive: {}", e))?;

        Ok(())
    }

    pub fn is_valid_version(&self, version: &str) -> bool {
        // Simple semver validation
        let parts: Vec<&str> = version.split('.').collect();
        if parts.len() != 3 {
            return false;
        }

        for part in parts {
            if part.is_empty() {
                return false;
            }
            if !part.chars().all(|c| c.is_ascii_digit()) {
                return false;
            }
        }

        true
    }

    pub fn find_modules(&self, path: &Path) -> Result<Vec<PathBuf>> {
        let mut modules = Vec::new();

        for entry in WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file())
        {
            if let Some(ext) = entry.path().extension() {
                if ext == "lig" {
                    modules.push(entry.path().to_path_buf());
                }
            }
        }

        Ok(modules)
    }

    pub async fn install(&self, path: &Path, install_path: &Path) -> Result<()> {
        // Build the register
        let temp_build_dir = tempfile::tempdir()
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create temp build directory: {}", e))?;

        let _artifact = self.build(path, temp_build_dir.path()).await?;

        // Copy to install location
        let register_install_path = install_path.join(&self.manifest.name);

        if register_install_path.exists() {
            tokio_fs::remove_dir_all(&register_install_path)
                .await
                .into_diagnostic()
                .map_err(|e| miette!("Failed to remove existing installation: {}", e))?;
        }

        // Copy all files from build directory to install directory
        self.copy_directory(temp_build_dir.path(), &register_install_path)
            .await?;

        Ok(())
    }

    /// Install the register to the XDG data directory.
    pub async fn install_to_xdg(&self, path: &Path) -> Result<()> {
        let xdg_config = KeyworkXdgConfig::new()
            .await
            .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

        let data_dir = xdg_config
            .data_dir()
            .map_err(|e| miette!("Failed to get data directory: {}", e))?;

        // Create packages subdirectory
        let packages_dir = data_dir.join("packages");
        tokio_fs::create_dir_all(&packages_dir)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create packages directory: {}", e))?;

        self.install(path, &packages_dir).await
    }

    async fn copy_directory(&self, src: &Path, dst: &Path) -> Result<()> {
        tokio_fs::create_dir_all(dst)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create destination directory: {}", e))?;

        for entry in WalkDir::new(src).into_iter().filter_map(|e| e.ok()) {
            let path = entry.path();
            let relative_path = path
                .strip_prefix(src)
                .into_diagnostic()
                .map_err(|e| miette!("Failed to get relative path: {}", e))?;
            let dest_path = dst.join(relative_path);

            if entry.file_type().is_dir() {
                tokio_fs::create_dir_all(&dest_path)
                    .await
                    .into_diagnostic()
                    .map_err(|e| miette!("Failed to create directory: {}", e))?;
            } else {
                if let Some(parent) = dest_path.parent() {
                    tokio_fs::create_dir_all(parent)
                        .await
                        .into_diagnostic()
                        .map_err(|e| miette!("Failed to create parent directory: {}", e))?;
                }

                tokio_fs::copy(path, &dest_path)
                    .await
                    .into_diagnostic()
                    .map_err(|e| miette!("Failed to copy file: {}", e))?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_register_toml() {
        let toml_content = r#"
[register]
name = "test-register"
version = "1.0.0"
description = "A test register"
authors = ["Test Author <test@example.com>"]
license = "Apache-2.0"
repository = "https://github.com/test/test-register"

[dependencies]
stdlib = "1.0.0"

[exports]
core = "src/core.lig"
utils = "src/utils.lig"

[metadata]
tags = ["test", "example"]
"#;

        let register: Register = toml::from_str(toml_content).unwrap();

        assert_eq!(register.manifest.name, "test-register");
        assert_eq!(register.manifest.version, "1.0.0");
        assert_eq!(register.manifest.description, "A test register");
        assert_eq!(
            register.manifest.authors,
            vec!["Test Author <test@example.com>"]
        );
        assert_eq!(register.manifest.license, "Apache-2.0");
        assert_eq!(
            register.manifest.repository,
            Some("https://github.com/test/test-register".to_string())
        );

        assert_eq!(
            register.dependencies.get("stdlib"),
            Some(&"1.0.0".to_string())
        );
        assert_eq!(
            register.exports.get("core"),
            Some(&"src/core.lig".to_string())
        );
        assert_eq!(
            register.exports.get("utils"),
            Some(&"src/utils.lig".to_string())
        );

        assert!(register.metadata.is_some());
        let metadata = register.metadata.unwrap();
        assert_eq!(metadata.tags, vec!["test", "example"]);
    }

    #[test]
    fn test_parse_minimal_register_toml() {
        let toml_content = r#"
[register]
name = "minimal"
version = "0.1.0"
description = "Minimal register"
authors = ["Author <author@example.com>"]
license = "Apache-2.0"
"#;

        let register: Register = toml::from_str(toml_content).unwrap();

        assert_eq!(register.manifest.name, "minimal");
        assert_eq!(register.manifest.version, "0.1.0");
        assert_eq!(register.manifest.description, "Minimal register");
        assert_eq!(
            register.manifest.authors,
            vec!["Author <author@example.com>"]
        );
        assert_eq!(register.manifest.license, "Apache-2.0");
        assert_eq!(register.manifest.repository, None);

        // Default values should be empty
        assert!(register.dependencies.is_empty());
        assert!(register.exports.is_empty());
        assert!(register.metadata.is_none());
    }

    #[test]
    fn test_parse_register_with_comments() {
        let toml_content = r#"
[register]
name = "with-comments"
version = "1.0.0"
description = "Register with comments"
authors = ["Author <author@example.com>"]
license = "Apache-2.0"

[dependencies]
# This is a comment
stdlib = "1.0.0"

[exports]
# Exported modules
core = "src/core.lig"

[metadata]
tags = []
"#;

        let register: Register = toml::from_str(toml_content).unwrap();

        assert_eq!(register.manifest.name, "with-comments");
        assert_eq!(
            register.dependencies.get("stdlib"),
            Some(&"1.0.0".to_string())
        );
        assert_eq!(
            register.exports.get("core"),
            Some(&"src/core.lig".to_string())
        );
        assert!(register.metadata.is_some());
        let metadata = register.metadata.unwrap();
        assert!(metadata.tags.is_empty());
    }
}
