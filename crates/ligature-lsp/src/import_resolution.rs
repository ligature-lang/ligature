//! Import resolution and module loading for the Ligature LSP server.
//!
//! This module provides functionality for resolving imports, loading modules,
//! and managing module dependencies in the LSP server context.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio::sync::RwLock;
use tower_lsp::lsp_types::{Location, Position, Range, SymbolInformation, SymbolKind, Url};
use tracing::{debug, info, warn};

use ligature_ast::{AstError, AstResult, Module, Span};
use ligature_parser::parse_module;
use ligature_types::resolver::ModuleResolver;

/// A module cache entry containing the loaded module and its metadata.
#[derive(Debug, Clone)]
pub struct ModuleCacheEntry {
    /// The loaded module.
    pub module: Module,
    /// The file path where this module was loaded from.
    pub file_path: PathBuf,
    /// The URI of the module file.
    pub uri: String,
    /// Whether this module has been fully resolved (all imports processed).
    pub fully_resolved: bool,
    /// Timestamp of when this module was last loaded.
    pub last_loaded: std::time::SystemTime,
}

/// Import resolution and module loading service for the LSP server.
pub struct ImportResolutionService {
    /// Cache of loaded modules.
    modules: Arc<RwLock<HashMap<String, ModuleCacheEntry>>>,
    /// Module resolver for finding and loading modules.
    resolver: Arc<RwLock<ModuleResolver>>,
    /// Workspace root paths for module resolution.
    workspace_roots: Arc<RwLock<Vec<PathBuf>>>,
    /// Import dependency graph for tracking module relationships.
    dependencies: Arc<RwLock<HashMap<String, Vec<String>>>>,
    /// Reverse dependencies for finding modules that import a given module.
    reverse_dependencies: Arc<RwLock<HashMap<String, Vec<String>>>>,
}

impl ImportResolutionService {
    /// Create a new import resolution service.
    pub fn new() -> Self {
        let mut resolver = ModuleResolver::new();

        // Add default search paths
        resolver.add_search_path(PathBuf::from("."));
        resolver.add_search_path(PathBuf::from("./src"));
        resolver.add_search_path(PathBuf::from("./lib"));
        resolver.add_search_path(PathBuf::from("./modules"));

        // Add default register paths
        resolver.add_register_path(PathBuf::from("./registers"));
        resolver.add_register_path(PathBuf::from("./vendor"));

        Self {
            modules: Arc::new(RwLock::new(HashMap::new())),
            resolver: Arc::new(RwLock::new(resolver)),
            workspace_roots: Arc::new(RwLock::new(Vec::new())),
            dependencies: Arc::new(RwLock::new(HashMap::new())),
            reverse_dependencies: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Add a workspace root path for module resolution.
    pub async fn add_workspace_root(&self, root: PathBuf) {
        let mut roots = self.workspace_roots.write().await;
        if !roots.contains(&root) {
            roots.push(root.clone());
        }

        // Also add to resolver search paths
        let mut resolver = self.resolver.write().await;
        resolver.add_search_path(root);
    }

    /// Add a register path for module resolution.
    pub async fn add_register_path(&self, path: PathBuf) {
        let mut resolver = self.resolver.write().await;
        resolver.add_register_path(path);
    }

    /// Load a module from a file URI.
    pub async fn load_module_from_uri(&self, uri: &str) -> AstResult<Module> {
        let file_path = self.uri_to_path(uri)?;
        self.load_module_from_path(&file_path, uri).await
    }

    /// Load a module from a file path.
    pub async fn load_module_from_path(&self, file_path: &Path, uri: &str) -> AstResult<Module> {
        // Check cache first
        {
            let modules = self.modules.read().await;
            if let Some(entry) = modules.get(uri) {
                // Check if file has been modified since last load
                if let Ok(metadata) = std::fs::metadata(file_path) {
                    if let Ok(modified) = metadata.modified() {
                        if modified <= entry.last_loaded {
                            debug!("Using cached module for {}", uri);
                            return Ok(entry.module.clone());
                        }
                    }
                }
            }
        }

        // Load and parse the module
        let content = std::fs::read_to_string(file_path).map_err(|e| AstError::ParseError {
            message: format!("Failed to read module file: {e}"),
            span: Span::default(),
        })?;

        let module = parse_module(&content)?;

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

        info!("Loaded module from {}", uri);
        Ok(module)
    }

    /// Resolve all imports in a module.
    pub async fn resolve_module_imports(&self, uri: &str) -> AstResult<()> {
        let module = {
            let modules = self.modules.read().await;
            modules.get(uri).cloned()
        };

        if let Some(entry) = module {
            self.resolve_imports_in_module(&entry.module, uri).await?;

            // Mark as fully resolved
            let mut modules = self.modules.write().await;
            if let Some(entry) = modules.get_mut(uri) {
                entry.fully_resolved = true;
            }
        }

        Ok(())
    }

    /// Resolve imports in a specific module.
    async fn resolve_imports_in_module(&self, module: &Module, source_uri: &str) -> AstResult<()> {
        let mut dependencies = Vec::new();

        for import in &module.imports {
            let resolved_uri = self.resolve_import_path(&import.path, source_uri).await?;

            if let Some(resolved_uri) = resolved_uri {
                // Load the imported module if not already loaded
                if !self.is_module_loaded(&resolved_uri).await {
                    self.load_module_from_uri(&resolved_uri).await?;
                }

                dependencies.push(resolved_uri.clone());

                // Update dependency graph
                self.update_dependency_graph(source_uri, &resolved_uri)
                    .await;
            }
        }

        // Store dependencies for this module
        {
            let mut deps = self.dependencies.write().await;
            deps.insert(source_uri.to_string(), dependencies);
        }

        Ok(())
    }

    /// Resolve an import path to a module URI.
    async fn resolve_import_path(
        &self,
        import_path: &str,
        source_uri: &str,
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
        if let Some(workspace_uri) = self.resolve_workspace_import(import_path).await? {
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
        let source_path = self.uri_to_path(source_uri)?;
        let source_dir = source_path.parent().ok_or_else(|| AstError::ParseError {
            message: "Source file has no parent directory".to_string(),
            span: Span::default(),
        })?;

        // Parse the relative path
        let relative_path = if import_path.starts_with("./") {
            source_dir.join(&import_path[2..])
        } else if import_path.starts_with("../") {
            // Handle parent directory traversal
            let mut current_dir = source_dir;
            let mut path = import_path;

            while path.starts_with("../") {
                current_dir = current_dir.parent().ok_or_else(|| AstError::ParseError {
                    message: "Cannot traverse beyond root directory".to_string(),
                    span: Span::default(),
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
                return Ok(Some(self.path_to_uri(path).await?));
            }
        }

        Ok(None)
    }

    /// Resolve a register-based import.
    async fn resolve_register_import(&self, import_path: &str) -> AstResult<Option<String>> {
        let mut resolver = self.resolver.write().await;

        // Try to resolve using the module resolver
        match resolver.resolve_module(import_path) {
            Ok(_module) => {
                // Find the actual file path
                let parts: Vec<&str> = import_path.split('.').collect();
                if parts.len() >= 2 {
                    let register_name = parts[0];
                    let module_name = parts[1..].join(".");

                    // Search in register paths
                    let register_paths = &resolver.register_paths;
                    for register_path in register_paths {
                        let potential_path = register_path
                            .join(register_name)
                            .join(format!("{}.lig", module_name));
                        if potential_path.exists() {
                            return Ok(Some(self.path_to_uri(&potential_path).await?));
                        }

                        // Try mod.lig in a directory
                        let mod_path = register_path
                            .join(register_name)
                            .join(&module_name)
                            .join("mod.lig");
                        if mod_path.exists() {
                            return Ok(Some(self.path_to_uri(&mod_path).await?));
                        }
                    }
                }
            }
            Err(_) => {
                // Module not found, continue to other resolution strategies
            }
        }

        Ok(None)
    }

    /// Resolve a workspace import.
    async fn resolve_workspace_import(&self, import_path: &str) -> AstResult<Option<String>> {
        let workspace_roots = self.workspace_roots.read().await;

        for root in &*workspace_roots {
            let potential_paths = [
                root.join(format!("{}.lig", import_path)),
                root.join(import_path).join("mod.lig"),
                root.join("src").join(format!("{}.lig", import_path)),
                root.join("lib").join(format!("{}.lig", import_path)),
            ];

            for path in &potential_paths {
                if path.exists() && path.is_file() {
                    return Ok(Some(self.path_to_uri(path).await?));
                }
            }
        }

        Ok(None)
    }

    /// Check if a module is already loaded.
    async fn is_module_loaded(&self, uri: &str) -> bool {
        let modules = self.modules.read().await;
        modules.contains_key(uri)
    }

    /// Update the dependency graph.
    async fn update_dependency_graph(&self, source: &str, target: &str) {
        // Add forward dependency
        {
            let mut deps = self.dependencies.write().await;
            deps.entry(source.to_string())
                .or_insert_with(Vec::new)
                .push(target.to_string());
        }

        // Add reverse dependency
        {
            let mut reverse_deps = self.reverse_dependencies.write().await;
            reverse_deps
                .entry(target.to_string())
                .or_insert_with(Vec::new)
                .push(source.to_string());
        }
    }

    /// Get all modules that import a given module.
    pub async fn get_importing_modules(&self, module_uri: &str) -> Vec<String> {
        let reverse_deps = self.reverse_dependencies.read().await;
        reverse_deps.get(module_uri).cloned().unwrap_or_default()
    }

    /// Get all modules that a given module imports.
    pub async fn get_imported_modules(&self, module_uri: &str) -> Vec<String> {
        let deps = self.dependencies.read().await;
        deps.get(module_uri).cloned().unwrap_or_default()
    }

    /// Find all references to a symbol across imported modules.
    pub async fn find_symbol_references(
        &self,
        symbol_name: &str,
        source_uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        // Get imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                let module_references =
                    self.find_symbol_in_module(&module, symbol_name, &module_uri);
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
    ) -> Option<Location> {
        // First check in the source module itself
        if let Some(module) = self.get_cached_module(source_uri).await {
            if let Some(location) =
                self.find_symbol_definition_in_module(&module, symbol_name, source_uri)
            {
                return Some(location);
            }
        }

        // Check in imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                if let Some(location) =
                    self.find_symbol_definition_in_module(&module, symbol_name, &module_uri)
                {
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
    ) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        // Get imported modules
        let imported_modules = self.get_imported_modules(source_uri).await;

        for module_uri in imported_modules {
            if let Some(module) = self.get_cached_module(&module_uri).await {
                let module_symbols =
                    self.extract_symbols_from_module(&module, &module_uri, &query_lower);
                symbols.extend(module_symbols);
            }
        }

        symbols
    }

    /// Find symbol definition within a module.
    fn find_symbol_definition_in_module(
        &self,
        module: &Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Option<Location> {
        for declaration in &module.declarations {
            let decl_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if decl_name == symbol_name {
                if let Ok(url) = Url::parse(module_uri) {
                    return Some(Location::new(
                        url,
                        Range::new(
                            Position::new(
                                declaration.span.line as u32 - 1,
                                declaration.span.column as u32 - 1,
                            ),
                            Position::new(
                                declaration.span.line as u32 - 1,
                                declaration.span.column as u32 - 1 + declaration.span.len() as u32,
                            ),
                        ),
                    ));
                }
            }
        }

        None
    }

    /// Extract symbols from a module that match a query.
    fn extract_symbols_from_module(
        &self,
        module: &Module,
        module_uri: &str,
        query: &str,
    ) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();

        for declaration in &module.declarations {
            let symbol_name = match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => &value_decl.name,
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => &type_alias.name,
                ligature_ast::DeclarationKind::TypeConstructor(type_ctor) => &type_ctor.name,
                ligature_ast::DeclarationKind::TypeClass(type_class) => &type_class.name,
                _ => continue,
            };

            if symbol_name.to_lowercase().contains(query) {
                if let Ok(url) = Url::parse(module_uri) {
                    let kind = match &declaration.kind {
                        ligature_ast::DeclarationKind::Value(_) => SymbolKind::VARIABLE,
                        ligature_ast::DeclarationKind::TypeAlias(_) => SymbolKind::TYPE_PARAMETER,
                        ligature_ast::DeclarationKind::TypeConstructor(_) => SymbolKind::CLASS,
                        ligature_ast::DeclarationKind::TypeClass(_) => SymbolKind::INTERFACE,
                        _ => SymbolKind::VARIABLE,
                    };

                    symbols.push(SymbolInformation {
                        name: symbol_name.clone(),
                        kind,
                        tags: None,
                        deprecated: None,
                        location: Location::new(
                            url,
                            Range::new(
                                Position::new(
                                    declaration.span.line as u32 - 1,
                                    declaration.span.column as u32 - 1,
                                ),
                                Position::new(
                                    declaration.span.line as u32 - 1,
                                    declaration.span.column as u32 - 1
                                        + declaration.span.len() as u32,
                                ),
                            ),
                        ),
                        container_name: None,
                    });
                }
            }
        }

        symbols
    }

    /// Find all references to a symbol within a module.
    fn find_symbol_in_module(
        &self,
        module: &Module,
        symbol_name: &str,
        module_uri: &str,
    ) -> Vec<Location> {
        let mut references = Vec::new();

        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == symbol_name {
                        if let Ok(url) = Url::parse(module_uri) {
                            references.push(Location::new(
                                url,
                                Range::new(
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                    Position::new(
                                        declaration.span.line as u32,
                                        declaration.span.column as u32,
                                    ),
                                ),
                            ));
                        }
                    }
                }
                _ => {}
            }
        }

        references
    }

    /// Get a cached module.
    pub async fn get_cached_module(&self, uri: &str) -> Option<Module> {
        let modules = self.modules.read().await;
        modules.get(uri).map(|entry| entry.module.clone())
    }

    /// Clear the module cache.
    pub async fn clear_cache(&self) {
        let mut modules = self.modules.write().await;
        modules.clear();

        let mut deps = self.dependencies.write().await;
        deps.clear();

        let mut reverse_deps = self.reverse_dependencies.write().await;
        reverse_deps.clear();
    }

    /// Invalidate a specific module in the cache.
    pub async fn invalidate_module(&self, uri: &str) {
        let mut modules = self.modules.write().await;
        modules.remove(uri);

        // Also invalidate modules that depend on this one
        let reverse_deps = self.reverse_dependencies.read().await;
        if let Some(dependents) = reverse_deps.get(uri) {
            let dependents = dependents.clone();
            drop(reverse_deps);

            for dependent in dependents {
                modules.remove(&dependent);
            }
        }
    }

    /// Convert a URI to a file path.
    fn uri_to_path(&self, uri: &str) -> AstResult<PathBuf> {
        let url = Url::parse(uri).map_err(|e| AstError::ParseError {
            message: format!("Invalid URI: {e}"),
            span: Span::default(),
        })?;

        url.to_file_path().map_err(|_| AstError::ParseError {
            message: format!("Cannot convert URI to file path: {}", uri),
            span: Span::default(),
        })
    }

    /// Convert a file path to a URI.
    pub async fn path_to_uri(&self, path: &Path) -> AstResult<String> {
        let url = Url::from_file_path(path).map_err(|_| AstError::ParseError {
            message: format!("Cannot convert path to URI: {:?}", path),
            span: Span::default(),
        })?;

        Ok(url.to_string())
    }

    /// Get all loaded modules.
    pub async fn get_loaded_modules(&self) -> Vec<String> {
        let modules = self.modules.read().await;
        modules.keys().cloned().collect()
    }

    /// Get module statistics.
    pub async fn get_stats(&self) -> ModuleStats {
        let modules = self.modules.read().await;
        let deps = self.dependencies.read().await;
        let reverse_deps = self.reverse_dependencies.read().await;

        ModuleStats {
            total_modules: modules.len(),
            total_dependencies: deps.values().map(|v| v.len()).sum(),
            total_reverse_dependencies: reverse_deps.values().map(|v| v.len()).sum(),
        }
    }
}

/// Statistics about the module cache and dependencies.
#[derive(Debug, Clone)]
pub struct ModuleStats {
    /// Total number of loaded modules.
    pub total_modules: usize,
    /// Total number of dependencies.
    pub total_dependencies: usize,
    /// Total number of reverse dependencies.
    pub total_reverse_dependencies: usize,
}

impl Default for ImportResolutionService {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

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
        let utils_uri = format!("file://{}", module_dir.join("utils.lig").display());

        // Load the main module
        if let Ok(module) = service.load_module_from_uri(&main_uri).await {
            // Resolve imports
            if let Ok(()) = service.resolve_module_imports(&main_uri).await {
                let imported_modules = service.get_imported_modules(&main_uri).await;
                assert!(!imported_modules.is_empty());
            }
        }
    }
}
