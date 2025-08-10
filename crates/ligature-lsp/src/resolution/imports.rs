//! Import path resolution functionality.
//!
//! This module provides functionality for resolving import paths to module URIs,
//! including relative, absolute, and register-based imports.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use ligature_ast::{AstError, AstResult, Program, Span};
use ligature_error::StandardResult;
use tokio::sync::RwLock;
use tracing::warn;

use super::dependencies::DependencyManager;
use super::utils::UriUtils;

/// Type alias for workspace roots
type WorkspaceRoots = Arc<RwLock<Vec<PathBuf>>>;

/// Type alias for module cache
type ModuleCache = Arc<RwLock<HashMap<String, super::cache::ModuleCacheEntry>>>;

/// Import resolver for resolving import paths to module URIs.
pub struct ImportResolver {
    /// Register paths for module resolution.
    register_paths: Arc<RwLock<Vec<PathBuf>>>,
    /// URI utilities for path/URI conversion.
    uri_utils: UriUtils,
}

impl ImportResolver {
    /// Create a new import resolver.
    pub fn new() -> Self {
        Self {
            register_paths: Arc::new(RwLock::new(Vec::new())),
            uri_utils: UriUtils::new(),
        }
    }

    /// Add a register path for module resolution.
    pub async fn add_register_path(&self, path: PathBuf) {
        let mut paths = self.register_paths.write().await;
        if !paths.contains(&path) {
            paths.push(path);
        }
    }

    /// Resolve imports in a specific module.
    pub async fn resolve_imports_in_module(
        &self,
        module: &Program,
        source_uri: &str,
        workspace_roots: &WorkspaceRoots,
        dependency_manager: &DependencyManager,
    ) -> StandardResult<()> {
        let mut dependencies = Vec::new();

        for import in &module.declarations {
            if let ligature_ast::DeclarationKind::Import(import) = &import.kind {
                let resolved_uri = self
                    .resolve_import_path(&import.path, source_uri, workspace_roots)
                    .await?;

                if let Some(resolved_uri) = resolved_uri {
                    dependencies.push(resolved_uri.clone());
                }
            }
        }

        // Store dependencies for this module
        dependency_manager
            .set_module_dependencies(source_uri, dependencies)
            .await;

        Ok(())
    }

    /// Resolve an import path to a module URI.
    pub async fn resolve_import_path(
        &self,
        import_path: &str,
        source_uri: &str,
        workspace_roots: &WorkspaceRoots,
    ) -> AstResult<Option<String>> {
        // Handle relative imports
        if import_path.starts_with('.') {
            return self.resolve_relative_import(import_path, source_uri).await;
        }

        // Handle absolute imports (register-based)
        if let Some(register_uri) = self.resolve_register_import(import_path).await? {
            return Ok(Some(register_uri));
        }

        // Handle workspace imports
        if let Some(workspace_uri) = self
            .resolve_workspace_import(import_path, workspace_roots)
            .await?
        {
            return Ok(Some(workspace_uri));
        }

        warn!("Could not resolve import path: {}", import_path);
        Ok(None)
    }

    /// Resolve a relative import path.
    async fn resolve_relative_import(
        &self,
        import_path: &str,
        source_uri: &str,
    ) -> AstResult<Option<String>> {
        let source_path = self.uri_utils.uri_to_path(source_uri)?;
        let source_dir = source_path.parent().ok_or_else(|| AstError::Parse {
            code: ligature_ast::ErrorCode::M4001,
            message: "Source file has no parent directory".to_string(),
            span: Span::default(),
            suggestions: vec![],
        })?;

        // Parse the relative path
        let relative_path = if import_path.starts_with("./") {
            source_dir.join(import_path.strip_prefix("./").unwrap())
        } else if import_path.starts_with("../") {
            // Handle parent directory traversal
            let mut current_dir = source_dir;
            let mut path = import_path;

            while path.starts_with("../") {
                current_dir = current_dir.parent().ok_or_else(|| AstError::Parse {
                    code: ligature_ast::ErrorCode::M4001,
                    message: "Cannot traverse beyond root directory".to_string(),
                    span: Span::default(),
                    suggestions: vec![],
                })?;
                path = &path[3..];
            }

            current_dir.join(path)
        } else {
            source_dir.join(import_path)
        };

        // Try different file extensions
        let possible_paths = [
            relative_path.with_extension("lig"),
            relative_path.join("mod.lig"),
            relative_path,
        ];

        for path in &possible_paths {
            if path.exists() && path.is_file() {
                return Ok(Some(self.uri_utils.path_to_uri(path)?));
            }
        }

        Ok(None)
    }

    /// Resolve a register-based import.
    async fn resolve_register_import(&self, import_path: &str) -> AstResult<Option<String>> {
        let register_paths = self.register_paths.read().await;

        // Parse the import path to extract register and module names
        let parts: Vec<&str> = import_path.split('.').collect();
        if parts.len() >= 2 {
            let register_name = parts[0];
            let module_name = parts[1..].join(".");

            // Search in register paths
            for register_path in &*register_paths {
                let potential_paths = [
                    register_path
                        .join(register_name)
                        .join(format!("{module_name}.lig")),
                    register_path
                        .join(register_name)
                        .join(&module_name)
                        .join("mod.lig"),
                ];

                for path in &potential_paths {
                    if path.exists() && path.is_file() {
                        return Ok(Some(self.uri_utils.path_to_uri(path)?));
                    }
                }
            }
        }

        Ok(None)
    }

    /// Resolve a workspace import.
    async fn resolve_workspace_import(
        &self,
        import_path: &str,
        workspace_roots: &WorkspaceRoots,
    ) -> AstResult<Option<String>> {
        let workspace_roots = workspace_roots.read().await;

        for root in &*workspace_roots {
            let potential_paths = [
                root.join(format!("{import_path}.lig")),
                root.join(import_path).join("mod.lig"),
                root.join("src").join(format!("{import_path}.lig")),
                root.join("lib").join(format!("{import_path}.lig")),
                root.join("modules").join(format!("{import_path}.lig")),
            ];

            for path in &potential_paths {
                if path.exists() && path.is_file() {
                    return Ok(Some(self.uri_utils.path_to_uri(path)?));
                }
            }
        }

        Ok(None)
    }

    /// Check if a module is already loaded.
    pub async fn is_module_loaded(&self, uri: &str, modules: &ModuleCache) -> bool {
        let modules = modules.read().await;
        modules.contains_key(uri)
    }

    /// Get all register paths.
    pub async fn get_register_paths(&self) -> Vec<PathBuf> {
        let paths = self.register_paths.read().await;
        paths.clone()
    }

    /// Clear all register paths.
    pub async fn clear_register_paths(&self) {
        let mut paths = self.register_paths.write().await;
        paths.clear();
    }
}

impl Default for ImportResolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use tempfile::TempDir;

    use super::*;

    #[tokio::test]
    async fn test_import_resolver_creation() {
        let resolver = ImportResolver::new();
        let paths = resolver.get_register_paths().await;
        assert!(paths.is_empty());
    }

    #[tokio::test]
    async fn test_add_register_path() {
        let resolver = ImportResolver::new();
        let temp_dir = TempDir::new().unwrap();
        let path = temp_dir.path().to_path_buf();

        resolver.add_register_path(path.clone()).await;
        let paths = resolver.get_register_paths().await;
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], path);
    }

    #[tokio::test]
    async fn test_duplicate_register_path() {
        let resolver = ImportResolver::new();
        let temp_dir = TempDir::new().unwrap();
        let path = temp_dir.path().to_path_buf();

        resolver.add_register_path(path.clone()).await;
        resolver.add_register_path(path.clone()).await;

        let paths = resolver.get_register_paths().await;
        assert_eq!(paths.len(), 1); // Should not add duplicate
    }

    #[tokio::test]
    async fn test_clear_register_paths() {
        let resolver = ImportResolver::new();
        let temp_dir = TempDir::new().unwrap();
        let path = temp_dir.path().to_path_buf();

        resolver.add_register_path(path).await;
        resolver.clear_register_paths().await;

        let paths = resolver.get_register_paths().await;
        assert!(paths.is_empty());
    }

    #[tokio::test]
    async fn test_relative_import_resolution() {
        let resolver = ImportResolver::new();
        let temp_dir = TempDir::new().unwrap();

        // Create test files
        let source_file = temp_dir.path().join("source.lig");
        let target_file = temp_dir.path().join("target.lig");
        std::fs::write(&source_file, "").unwrap();
        std::fs::write(&target_file, "").unwrap();

        let source_uri = format!("file://{}", source_file.display());

        // Test relative import
        let result = resolver
            .resolve_relative_import("./target", &source_uri)
            .await
            .unwrap();

        assert!(result.is_some());
        assert!(result.unwrap().contains("target.lig"));
    }

    #[tokio::test]
    async fn test_workspace_import_resolution() {
        let resolver = ImportResolver::new();
        let temp_dir = TempDir::new().unwrap();
        let workspace_roots = Arc::new(RwLock::new(vec![temp_dir.path().to_path_buf()]));

        // Create test module
        let module_file = temp_dir.path().join("test_module.lig");
        std::fs::write(&module_file, "").unwrap();

        let result = resolver
            .resolve_workspace_import("test_module", &workspace_roots)
            .await
            .unwrap();

        assert!(result.is_some());
        assert!(result.unwrap().contains("test_module.lig"));
    }
}
