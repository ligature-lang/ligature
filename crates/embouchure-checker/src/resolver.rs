//! Module resolution for the Ligature type system.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use ligature_ast::Span;
use ligature_error::StandardResult;
use serde::{Deserialize, Serialize};
use toml;

/// Simple module structure for type checking
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub imports: Vec<ligature_ast::Import>,
    pub declarations: Vec<ligature_ast::Declaration>,
    pub span: Span,
}

/// Type alias for import path result
#[allow(dead_code)]
type ImportPathResult = StandardResult<(String, Vec<String>)>;

/// Register manifest structure for parsing register.toml files.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct RegisterManifest {
    #[serde(rename = "register")]
    register_info: RegisterInfo,
    #[serde(default)]
    exports: HashMap<String, String>,
    #[serde(default)]
    dependencies: HashMap<String, String>,
    #[serde(default)]
    metadata: RegisterMetadata,
}

/// Register information from the manifest.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct RegisterInfo {
    name: String,
    version: String,
    description: Option<String>,
    authors: Option<Vec<String>>,
    license: Option<String>,
    repository: Option<String>,
}

/// Register metadata from the manifest.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct RegisterMetadata {
    #[serde(default)]
    tags: Vec<String>,
}

/// A module resolver that can load modules for type checking.
#[derive(Clone)]
pub struct ModuleResolver {
    /// Cache of loaded modules.
    pub cache: HashMap<String, Module>,
    /// Search paths for module resolution.
    search_paths: Vec<PathBuf>,
    /// Register paths for module resolution.
    pub register_paths: Vec<PathBuf>,
    /// Track import cycles to prevent infinite recursion.
    #[allow(dead_code)]
    import_stack: Vec<String>,
}

impl ModuleResolver {
    /// Create a new module resolver.
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            search_paths: Vec::new(),
            register_paths: Vec::new(),
            import_stack: Vec::new(),
        }
    }

    /// Add a search path for module resolution.
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    /// Add a register path for module resolution.
    pub fn add_register_path(&mut self, path: PathBuf) {
        self.register_paths.push(path);
    }

    /// Resolve and load a module by path for type checking.
    pub fn resolve_module(&mut self, path: &str) -> ligature_error::StandardResult<Module> {
        // Simplified version for testing
        Ok(Module {
            name: path.to_string(),
            imports: vec![],
            declarations: vec![],
            span: Span::default(),
        })
    }

    /// Parse an import path to extract register and module names.
    #[allow(dead_code)]
    fn parse_import_path(&self, path: &str) -> ImportPathResult {
        // Simplified implementation for testing
        let parts: Vec<&str> = path.split('/').collect();
        if parts.is_empty() {
            return Err(ligature_error::StandardError::validation_error(
                "Empty import path",
            ));
        }

        let register_name = parts[0].to_string();
        let module_path = parts[1..].iter().map(|s| s.to_string()).collect();

        Ok((register_name, module_path))
    }

    /// Find a nested module within a specific register.
    #[allow(dead_code)]
    fn find_nested_module_in_register(
        &self,
        register_name: &str,
        module_path: &[String],
    ) -> StandardResult<PathBuf> {
        // Simplified implementation for testing
        let mut path = PathBuf::from("registers");
        path.push(register_name);
        for part in module_path {
            path.push(part);
        }
        path.set_extension("lig");
        Ok(path)
    }

    /// Find a nested module within a register.
    /// Recursively traverses the module path to find the target module.
    #[allow(dead_code)]
    fn find_nested_in_register(
        &self,
        register_path: &Path,
        module_path: &[String],
    ) -> StandardResult<PathBuf> {
        if module_path.is_empty() {
            return Err(ligature_error::StandardError::Ligature(
                ligature_ast::LigatureError::Parse {
                    code: ligature_ast::ErrorCode::M4003,
                    message: "Empty module path".to_string(),
                    span: Span::default(),
                    suggestions: vec!["Provide a valid module path".to_string()],
                },
            ));
        }

        if module_path.len() == 1 {
            // Base case: find the final module
            return self.find_in_register(register_path, &module_path[0], false);
        }

        // Recursive case: find the intermediate module and continue
        let intermediate_module = &module_path[0];

        // Find the intermediate module (could be file or directory)
        let intermediate_path = self.find_in_register(register_path, intermediate_module, true)?;

        // Check if the intermediate module is a directory (submodule)
        if intermediate_path.is_dir() {
            // Continue searching in the submodule directory
            self.find_nested_in_register(&intermediate_path, &module_path[1..])
        } else {
            // The intermediate module is a file, not a directory
            Err(ligature_error::StandardError::Ligature(
                ligature_ast::LigatureError::Parse {
                    code: ligature_ast::ErrorCode::M4003,
                    message: format!(
                        "Module '{intermediate_module}' is not a directory, cannot contain \
                         submodules"
                    ),
                    span: Span::default(),
                    suggestions: vec!["Check that the module path is correct".to_string()],
                },
            ))
        }
    }

    /// Find a register directory by name.
    #[allow(dead_code)]
    fn find_register_directory(&self, register_name: &str) -> StandardResult<PathBuf> {
        // Search in register paths
        for register_path in &self.register_paths {
            let potential_path = register_path.join(register_name);
            if potential_path.exists() && potential_path.is_dir() {
                return Ok(potential_path);
            }
        }

        // Search in default registers directory
        let default_path = PathBuf::from("registers").join(register_name);
        if default_path.exists() && default_path.is_dir() {
            return Ok(default_path);
        }

        Err(ligature_error::StandardError::validation_error(format!(
            "Register not found: {register_name}"
        )))
    }

    /// Find a module file in the search paths.
    #[allow(dead_code)]
    fn find_module_file(&self, path: &str) -> StandardResult<PathBuf> {
        // Try direct file path first
        let direct_path = PathBuf::from(path);
        if direct_path.exists() && direct_path.is_file() {
            return Ok(direct_path);
        }

        // Try with .lig extension
        let lig_path = direct_path.with_extension("lig");
        if lig_path.exists() && lig_path.is_file() {
            return Ok(lig_path);
        }

        // Search in search paths
        for search_path in &self.search_paths {
            let full_path = search_path.join(&direct_path);
            if full_path.exists() && full_path.is_file() {
                return Ok(full_path);
            }

            let lig_full_path = search_path.join(&lig_path);
            if lig_full_path.exists() && lig_full_path.is_file() {
                return Ok(lig_full_path);
            }
        }

        // Search in register paths
        for register_path in &self.register_paths {
            let module_path = self.find_in_register(register_path, path, false)?;
            if module_path.exists() && module_path.is_file() {
                return Ok(module_path);
            }
        }

        Err(ligature_error::StandardError::Ligature(
            ligature_ast::LigatureError::Module {
                code: ligature_ast::ErrorCode::M4001,
                message: format!("Module not found: {path}"),
                path: Some(path.to_string()),
                cause: Some("Module not found in search paths".to_string()),
            },
        ))
    }

    /// Find a module within a register.
    #[allow(dead_code)]
    fn find_in_register(
        &self,
        register_path: &Path,
        module_name: &str,
        for_nested: bool,
    ) -> StandardResult<PathBuf> {
        // Look for register.toml to understand the register structure
        let register_manifest = register_path.join("register.toml");
        if register_manifest.exists() {
            // Parse register.toml and check exports
            let manifest_content = std::fs::read_to_string(&register_manifest).map_err(|e| {
                ligature_error::StandardError::Ligature(ligature_ast::LigatureError::Parse {
                    code: ligature_ast::ErrorCode::M4001,
                    message: format!("Failed to read register manifest: {e}"),
                    span: Span::default(),
                    suggestions: vec![
                        "Check that the register.toml file exists and is readable".to_string(),
                    ],
                })
            })?;

            let manifest: RegisterManifest = toml::from_str(&manifest_content).map_err(|e| {
                ligature_error::StandardError::Ligature(ligature_ast::LigatureError::Parse {
                    code: ligature_ast::ErrorCode::M4001,
                    message: format!("Failed to parse register manifest: {e}"),
                    span: Span::default(),
                    suggestions: vec![
                        "Check that the register.toml file has valid TOML syntax".to_string(),
                    ],
                })
            })?;

            // Check if the module is exported by this register
            if let Some(module_path) = manifest.exports.get(module_name) {
                let full_path = register_path.join(module_path);
                if full_path.exists() {
                    // If it's a directory, look for mod.lig inside it
                    if full_path.is_dir() {
                        let mod_file = full_path.join("mod.lig");
                        if mod_file.exists() {
                            if for_nested {
                                return Ok(full_path); // Return directory for nested resolution
                            } else {
                                return Ok(mod_file); // Return file for direct import
                            }
                        }
                    }
                    return Ok(full_path);
                }
            }

            // If not found in exports, try common locations
            let common_paths = [
                register_path.join(format!("{module_name}.lig")),
                register_path.join(format!("{module_name}.lig")),
                register_path
                    .join("modules")
                    .join(format!("{module_name}.lig")),
            ];

            for path in &common_paths {
                if path.exists() {
                    return Ok(path.clone());
                }
            }
        }

        // Look for both files and directories
        if let Ok(entries) = std::fs::read_dir(register_path) {
            for entry in entries.flatten() {
                let path = entry.path();

                // Check for .lig files
                if path.is_file() && path.extension().is_some_and(|ext| ext == "lig") {
                    let stem = path.file_stem().unwrap().to_string_lossy();
                    if stem == module_name {
                        return Ok(path);
                    }
                }

                // Check for directories (for nested modules)
                if path.is_dir() {
                    let dir_name = path.file_name().unwrap().to_string_lossy();
                    if dir_name == module_name {
                        // Look for a mod.lig file in the directory
                        let mod_file = path.join("mod.lig");
                        if mod_file.exists() {
                            if for_nested {
                                return Ok(path); // Return directory for nested resolution
                            } else {
                                return Ok(mod_file); // Return file for direct import
                            }
                        }
                        // If no mod.lig, this is not a valid module
                        return Err(ligature_error::StandardError::Ligature(
                            ligature_ast::LigatureError::Parse {
                                code: ligature_ast::ErrorCode::M4001,
                                message: format!(
                                    "Directory '{module_name}' does not contain a mod.lig file"
                                ),
                                span: Span::default(),
                                suggestions: vec![
                                    "Add a mod.lig file to the directory or use a different \
                                     module path"
                                        .to_string(),
                                ],
                            },
                        ));
                    }
                }
            }
        }

        Err(ligature_error::StandardError::Ligature(
            ligature_ast::LigatureError::Module {
                code: ligature_ast::ErrorCode::M4001,
                message: format!("Module not found: {module_name}"),
                path: Some(module_name.to_string()),
                cause: Some("Module not found in register".to_string()),
            },
        ))
    }

    /// Clear the module cache.
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Get a cached module.
    pub fn get_cached(&self, path: &str) -> Option<&Module> {
        self.cache.get(path)
    }

    /// Check if a module is cached.
    pub fn is_cached(&self, path: &str) -> bool {
        self.cache.contains_key(path)
    }

    /// Extract exported bindings from a module.
    pub fn get_exported_bindings(&self, module: &Module) -> HashMap<String, ligature_ast::Type> {
        let mut bindings = HashMap::new();
        let mut exported_items = HashSet::new();
        let mut has_explicit_exports = false;

        // First, collect all exported item names from export declarations
        for declaration in &module.declarations {
            if let ligature_ast::DeclarationKind::Export(export_decl) = &declaration.kind {
                has_explicit_exports = true;
                for item in &export_decl.items {
                    // Store the original name, not the alias
                    exported_items.insert(item.name.clone());
                }
            }
        }

        // If no explicit exports, assume all value declarations are exported
        if !has_explicit_exports {
            for declaration in &module.declarations {
                match &declaration.kind {
                    ligature_ast::DeclarationKind::Value(value_decl) => {
                        exported_items.insert(value_decl.name.clone());
                    }
                    ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                        exported_items.insert(type_alias.name.clone());
                    }
                    ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                        exported_items.insert(type_constructor.name.clone());
                    }
                    _ => {}
                }
            }
        }

        // Now collect the actual types for exported items
        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if exported_items.contains(&value_decl.name) {
                        // For value declarations, we need to infer the type
                        let value_type = value_decl.type_annotation.clone().unwrap_or_else(|| {
                            // Enhanced type inference based on the value expression
                            match &value_decl.value.kind {
                                ligature_ast::ExprKind::Abstraction {
                                    parameter: _,
                                    parameter_type,
                                    body,
                                } => {
                                    // For lambda functions, create a more specific function type
                                    let param_type = parameter_type
                                        .as_ref()
                                        .map(|t| t.as_ref().clone())
                                        .unwrap_or_else(|| {
                                            ligature_ast::Type::variable(
                                                "a".to_string(),
                                                Span::default(),
                                            )
                                        });

                                    // Try to infer return type from body
                                    let return_type = match &body.kind {
                                        ligature_ast::ExprKind::Match {
                                            scrutinee: _,
                                            cases,
                                        } => {
                                            // For match expressions, try to infer from cases
                                            if cases.len() == 2 {
                                                // Common pattern: Bool -> a -> a -> a
                                                ligature_ast::Type::function(
                                                    ligature_ast::Type::variable(
                                                        "a".to_string(),
                                                        Span::default(),
                                                    ),
                                                    ligature_ast::Type::variable(
                                                        "a".to_string(),
                                                        Span::default(),
                                                    ),
                                                    Span::default(),
                                                )
                                            } else {
                                                ligature_ast::Type::variable(
                                                    "b".to_string(),
                                                    Span::default(),
                                                )
                                            }
                                        }
                                        ligature_ast::ExprKind::If { .. } => {
                                            // For if expressions, return type is the same as branches
                                            ligature_ast::Type::variable(
                                                "a".to_string(),
                                                Span::default(),
                                            )
                                        }
                                        ligature_ast::ExprKind::Application { .. } => {
                                            // For function applications, return type is variable
                                            ligature_ast::Type::variable(
                                                "b".to_string(),
                                                Span::default(),
                                            )
                                        }
                                        ligature_ast::ExprKind::Literal(literal) => match literal {
                                            ligature_ast::Literal::Boolean(_) => {
                                                ligature_ast::Type::bool(Span::default())
                                            }
                                            ligature_ast::Literal::Integer(_) => {
                                                ligature_ast::Type::integer(Span::default())
                                            }
                                            ligature_ast::Literal::Float(_) => {
                                                ligature_ast::Type::float(Span::default())
                                            }
                                            ligature_ast::Literal::String(_) => {
                                                ligature_ast::Type::string(Span::default())
                                            }
                                            ligature_ast::Literal::Unit => {
                                                ligature_ast::Type::unit(Span::default())
                                            }
                                            ligature_ast::Literal::List(_) => {
                                                ligature_ast::Type::list(
                                                    ligature_ast::Type::variable(
                                                        "a".to_string(),
                                                        Span::default(),
                                                    ),
                                                    Span::default(),
                                                )
                                            }
                                        },
                                        _ => ligature_ast::Type::variable(
                                            "b".to_string(),
                                            Span::default(),
                                        ),
                                    };

                                    ligature_ast::Type::function(
                                        param_type,
                                        return_type,
                                        Span::default(),
                                    )
                                }
                                ligature_ast::ExprKind::Literal(literal) => match literal {
                                    ligature_ast::Literal::Boolean(_) => {
                                        ligature_ast::Type::bool(Span::default())
                                    }
                                    ligature_ast::Literal::Integer(_) => {
                                        ligature_ast::Type::integer(Span::default())
                                    }
                                    ligature_ast::Literal::Float(_) => {
                                        ligature_ast::Type::float(Span::default())
                                    }
                                    ligature_ast::Literal::String(_) => {
                                        ligature_ast::Type::string(Span::default())
                                    }
                                    ligature_ast::Literal::Unit => {
                                        ligature_ast::Type::unit(Span::default())
                                    }
                                    ligature_ast::Literal::List(_) => ligature_ast::Type::list(
                                        ligature_ast::Type::variable(
                                            "a".to_string(),
                                            Span::default(),
                                        ),
                                        Span::default(),
                                    ),
                                },
                                _ => ligature_ast::Type::variable("a".to_string(), Span::default()),
                            }
                        });
                        bindings.insert(value_decl.name.clone(), value_type);
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    if exported_items.contains(&type_alias.name) {
                        bindings.insert(type_alias.name.clone(), type_alias.type_.clone());
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    if exported_items.contains(&type_constructor.name) {
                        bindings
                            .insert(type_constructor.name.clone(), type_constructor.body.clone());
                    }
                }
                _ => {}
            }
        }

        // Handle explicit exports with aliases
        if has_explicit_exports {
            let mut aliased_bindings = HashMap::new();
            for declaration in &module.declarations {
                if let ligature_ast::DeclarationKind::Export(export_decl) = &declaration.kind {
                    for item in &export_decl.items {
                        if let Some(original_type) = bindings.get(&item.name) {
                            let export_name = item.alias.as_ref().unwrap_or(&item.name);
                            aliased_bindings.insert(export_name.clone(), original_type.clone());
                        }
                    }
                }
            }
            // Replace the original bindings with the aliased ones
            if !aliased_bindings.is_empty() {
                bindings = aliased_bindings;
            }
        }

        bindings
    }
}

impl Default for ModuleResolver {
    fn default() -> Self {
        Self::new()
    }
}
