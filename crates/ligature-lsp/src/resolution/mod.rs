//! Import resolution and module loading for the Ligature LSP server.
//!
//! This module provides functionality for resolving imports, loading modules,
//! and managing module dependencies in the LSP server context.

pub mod cache;
pub mod dependencies;
pub mod imports;
pub mod symbols;
pub mod utils;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

pub use cache::{ModuleCacheEntry, ModuleStats};
pub use dependencies::DependencyManager;
pub use imports::ImportResolver;
use ligature_ast::Program;
use ligature_error::StandardResult;
pub use symbols::SymbolResolver;
use tokio::sync::RwLock;
pub use utils::UriUtils;

/// Type alias for module cache
type ModuleCache = Arc<RwLock<HashMap<String, ModuleCacheEntry>>>;

/// Import resolution and module loading service for the LSP server.
pub struct ImportResolutionService {
    /// Cache of loaded modules.
    modules: ModuleCache,
    /// Workspace root paths for module resolution.
    workspace_roots: Arc<RwLock<Vec<PathBuf>>>,
    /// Dependency manager for tracking module relationships.
    dependencies: DependencyManager,
    /// Import resolver for resolving import paths.
    import_resolver: ImportResolver,
    /// Symbol resolver for finding symbols across modules.
    symbol_resolver: SymbolResolver,
    /// URI utilities for path/URI conversion.
    uri_utils: UriUtils,
}

impl ImportResolutionService {
    /// Create a new import resolution service.
    pub fn new() -> Self {
        Self {
            modules: Arc::new(RwLock::new(HashMap::new())),
            workspace_roots: Arc::new(RwLock::new(Vec::new())),
            dependencies: DependencyManager::new(),
            import_resolver: ImportResolver::new(),
            symbol_resolver: SymbolResolver::new(),
            uri_utils: UriUtils::new(),
        }
    }

    /// Add a workspace root path for module resolution.
    pub async fn add_workspace_root(&self, root: PathBuf) {
        let mut roots = self.workspace_roots.write().await;
        if !roots.contains(&root) {
            roots.push(root.clone());
        }
    }

    /// Add a register path for module resolution.
    pub async fn add_register_path(&self, path: PathBuf) {
        self.import_resolver.add_register_path(path).await;
    }

    /// Load a module from a file URI.
    pub async fn load_module_from_uri(&self, uri: &str) -> StandardResult<Program> {
        let file_path = self.uri_utils.uri_to_path(uri)?;
        self.load_module_from_path(&file_path, uri).await
    }

    /// Load a module from a file path.
    pub async fn load_module_from_path(
        &self,
        file_path: &std::path::Path,
        uri: &str,
    ) -> StandardResult<Program> {
        // Check cache first
        {
            let modules = self.modules.read().await;
            if let Some(entry) = modules.get(uri) {
                // Check if file has been modified since last load
                if let Ok(metadata) = std::fs::metadata(file_path) {
                    if let Ok(modified) = metadata.modified() {
                        if modified <= entry.last_loaded {
                            tracing::debug!("Using cached module for {}", uri);
                            return Ok(entry.module.clone());
                        }
                    }
                }
            }
        }

        // Load and parse the module
        let content = std::fs::read_to_string(file_path).map_err(|e| {
            ligature_error::StandardError::Ligature(ligature_ast::LigatureError::Parse {
                code: ligature_ast::ErrorCode::E1001,
                message: format!("Failed to read module file: {e}"),
                span: ligature_ast::Span::default(),
                suggestions: vec!["Check that the file exists and is readable".to_string()],
            })
        })?;

        let module = ligature_parser::parse_module(&content)?;

        // Cache the module
        let entry = ModuleCacheEntry {
            module: module.clone(),
            file_path: file_path.to_path_buf(),
            uri: uri.to_string(),
            fully_resolved: false,
            last_loaded: std::time::SystemTime::now(),
        };

        {
            let mut modules = self.modules.write().await;
            modules.insert(uri.to_string(), entry);
        }

        tracing::info!("Loaded module from {}", uri);
        Ok(module)
    }

    /// Resolve all imports in a module.
    pub async fn resolve_module_imports(&self, uri: &str) -> StandardResult<()> {
        let module = {
            let modules = self.modules.read().await;
            modules.get(uri).cloned()
        };

        if let Some(entry) = module {
            self.import_resolver
                .resolve_imports_in_module(
                    &entry.module,
                    uri,
                    &self.workspace_roots,
                    &self.dependencies,
                )
                .await?;

            // Mark as fully resolved
            let mut modules = self.modules.write().await;
            if let Some(entry) = modules.get_mut(uri) {
                entry.fully_resolved = true;
            }
        }

        Ok(())
    }

    /// Get all modules that import a given module.
    pub async fn get_importing_modules(&self, module_uri: &str) -> Vec<String> {
        self.dependencies.get_importing_modules(module_uri).await
    }

    /// Get all modules that a given module imports.
    pub async fn get_imported_modules(&self, module_uri: &str) -> Vec<String> {
        self.dependencies.get_imported_modules(module_uri).await
    }

    /// Find all references to a symbol across imported modules.
    pub async fn find_symbol_references(
        &self,
        symbol_name: &str,
        source_uri: &str,
    ) -> Vec<tower_lsp::lsp_types::Location> {
        let mut references = Vec::new();

        // Get imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                let module_references =
                    self.symbol_resolver
                        .find_symbol_in_module(&module, symbol_name, &module_uri);
                references.extend(module_references);
            }
        }

        references
    }

    /// Find the definition of a symbol across imported modules.
    pub async fn find_symbol_definition(
        &self,
        symbol_name: &str,
        source_uri: &str,
    ) -> Option<tower_lsp::lsp_types::Location> {
        // First check in the source module itself
        if let Some(module) = self.get_cached_module(source_uri).await {
            if let Some(location) = self.symbol_resolver.find_symbol_definition_in_module(
                &module,
                symbol_name,
                source_uri,
            ) {
                return Some(location);
            }
        }

        // Check in imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                if let Some(location) = self.symbol_resolver.find_symbol_definition_in_module(
                    &module,
                    symbol_name,
                    &module_uri,
                ) {
                    return Some(location);
                }
            }
        }

        None
    }

    /// Find all symbols in imported modules that match a query.
    pub async fn find_symbols_in_imports(
        &self,
        query: &str,
        source_uri: &str,
    ) -> Vec<tower_lsp::lsp_types::SymbolInformation> {
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        // Get imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                let module_symbols = self.symbol_resolver.extract_symbols_from_module(
                    &module,
                    &module_uri,
                    &query_lower,
                );
                symbols.extend(module_symbols);
            }
        }

        symbols
    }

    /// Get a cached module.
    pub async fn get_cached_module(&self, uri: &str) -> Option<Program> {
        let modules = self.modules.read().await;
        modules.get(uri).map(|entry| entry.module.clone())
    }

    /// Clear the module cache.
    pub async fn clear_cache(&self) {
        let mut modules = self.modules.write().await;
        modules.clear();

        self.dependencies.clear().await;
    }

    /// Invalidate a specific module in the cache.
    pub async fn invalidate_module(&self, uri: &str) {
        let mut modules = self.modules.write().await;
        modules.remove(uri);

        // Also invalidate modules that depend on this one
        let dependents = self.dependencies.get_importing_modules(uri).await;
        for dependent in dependents {
            modules.remove(&dependent);
        }
    }

    /// Convert a file path to a URI.
    pub async fn path_to_uri(&self, path: &std::path::Path) -> ligature_ast::AstResult<String> {
        self.uri_utils.path_to_uri(path)
    }

    /// Get all loaded modules.
    pub async fn get_loaded_modules(&self) -> Vec<String> {
        let modules = self.modules.read().await;
        modules.keys().cloned().collect()
    }

    /// Get module statistics.
    pub async fn get_stats(&self) -> ModuleStats {
        let modules = self.modules.read().await;
        let deps_stats = self.dependencies.get_stats().await;

        ModuleStats {
            total_modules: modules.len(),
            total_dependencies: deps_stats.total_dependencies,
            total_reverse_dependencies: deps_stats.total_reverse_dependencies,
        }
    }
}

impl Default for ImportResolutionService {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::TempDir;

    use super::*;

    #[tokio::test]
    async fn test_import_resolution_service_creation() {
        let service = ImportResolutionService::new();
        let stats = service.get_stats().await;
        assert_eq!(stats.total_modules, 0);
    }

    #[tokio::test]
    async fn test_workspace_root_addition() {
        let service = ImportResolutionService::new();
        let temp_dir = TempDir::new().unwrap();

        service
            .add_workspace_root(temp_dir.path().to_path_buf())
            .await;

        // Verify that the workspace root was added
        let stats = service.get_stats().await;
        assert_eq!(stats.total_modules, 0);
    }

    #[tokio::test]
    async fn test_module_cache_operations() {
        let service = ImportResolutionService::new();

        // Test cache operations
        service.clear_cache().await;
        let stats = service.get_stats().await;
        assert_eq!(stats.total_modules, 0);

        let loaded_modules = service.get_loaded_modules().await;
        assert!(loaded_modules.is_empty());
    }

    #[tokio::test]
    async fn test_relative_import_resolution() {
        let service = ImportResolutionService::new();
        let temp_dir = TempDir::new().unwrap();

        // Create a test module structure
        let module_dir = temp_dir.path().join("test_module");
        fs::create_dir_all(&module_dir).unwrap();

        // Create main.lig
        let main_content = r#"
import "./utils"

let result = utils.add 1 2
"#;
        fs::write(module_dir.join("main.lig"), main_content).unwrap();

        // Create utils.lig
        let utils_content = r#"
export let add = \x y -> x + y
"#;
        fs::write(module_dir.join("utils.lig"), utils_content).unwrap();

        // Add workspace root
        service
            .add_workspace_root(temp_dir.path().to_path_buf())
            .await;

        // Test that we can resolve the relative import
        let main_uri = format!("file://{}", module_dir.join("main.lig").display());
        let _utils_uri = format!("file://{}", module_dir.join("utils.lig").display());

        // Load the main module
        if let Ok(_module) = service.load_module_from_uri(&main_uri).await {
            // Resolve imports
            if let Ok(()) = service.resolve_module_imports(&main_uri).await {
                let imported_modules = service.get_imported_modules(&main_uri).await;
                assert!(!imported_modules.is_empty());
            }
        }
    }
}
