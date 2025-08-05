//! Module resolution for the Ligature evaluation engine.

use crate::Value;
use ligature_ast::{AstError, AstResult};
use ligature_parser::parse_module;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use toml;

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

/// A module resolver that can load modules from various sources.
#[derive(Clone)]
pub struct ModuleResolver {
    /// Cache of loaded modules.
    cache: HashMap<String, Value>,
    /// Search paths for module resolution.
    search_paths: Vec<PathBuf>,
    /// Register paths for module resolution.
    pub register_paths: Vec<PathBuf>,
}

impl ModuleResolver {
    /// Create a new module resolver.
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            search_paths: Vec::new(),
            register_paths: Vec::new(),
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

    /// Resolve and load a module by path.
    pub fn resolve_module(&mut self, path: &str) -> AstResult<Value> {
        // Check cache first
        if let Some(module) = self.cache.get(path) {
            return Ok(module.clone());
        }

        // Parse the import path to extract register and module names
        let (register_name, module_path) = self.parse_import_path(path)?;

        // Try to find the module file
        let module_path = self.find_nested_module_in_register(&register_name, &module_path)?;

        // Load and parse the module
        let module_content =
            std::fs::read_to_string(&module_path).map_err(|e| AstError::ParseError {
                message: format!("Failed to read module file: {}", e),
                span: ligature_ast::Span::default(),
            })?;

        let module_ast = parse_module(&module_content)?;

        // Evaluate the module
        let mut evaluator = crate::Evaluator::new();
        let module_value = evaluator.evaluate_module(&module_ast)?;

        // Cache the module
        self.cache.insert(path.to_string(), module_value.clone());

        Ok(module_value)
    }

    /// Parse an import path to extract register and module names.
    /// Now supports nested module paths like "std.collections.list"
    fn parse_import_path(&self, path: &str) -> AstResult<(String, Vec<String>)> {
        let parts: Vec<&str> = path.split('.').collect();
        match parts.as_slice() {
            [register_name, module_name] => {
                Ok((register_name.to_string(), vec![module_name.to_string()]))
            }
            [register_name, module_parts @ ..] => {
                // Support nested module paths like "std.collections.list"
                let module_path: Vec<String> = module_parts.iter().map(|s| s.to_string()).collect();
                Ok((register_name.to_string(), module_path))
            }
            _ => Err(AstError::ParseError {
                message: format!("Invalid import path format: {}", path),
                span: ligature_ast::Span::default(),
            }),
        }
    }

    /// Find a nested module within a specific register.
    /// Supports paths like ["collections", "list"] for "std.collections.list"
    fn find_nested_module_in_register(
        &self,
        register_name: &str,
        module_path: &[String],
    ) -> AstResult<PathBuf> {
        // First, find the register directory
        let register_path = self.find_register_directory(register_name)?;

        // Then find the nested module within that register
        self.find_nested_in_register(&register_path, module_path)
    }

    /// Find a nested module within a register.
    /// Recursively traverses the module path to find the target module.
    fn find_nested_in_register(&self, register_path: &Path, module_path: &[String]) -> AstResult<PathBuf> {
        if module_path.is_empty() {
            return Err(AstError::ParseError {
                message: "Empty module path".to_string(),
                span: ligature_ast::Span::default(),
            });
        }

        if module_path.len() == 1 {
            // Base case: find the final module
            return self.find_in_register(register_path, &module_path[0], false);
        }

        // Recursive case: find the intermediate module and continue
        let intermediate_module = &module_path[0];
        let intermediate_path = self.find_in_register(register_path, intermediate_module, true)?;
        
        // Check if the intermediate module is a directory (submodule)
        if intermediate_path.is_dir() {
            // Continue searching in the submodule directory
            self.find_nested_in_register(&intermediate_path, &module_path[1..])
        } else {
            // The intermediate module is a file, not a directory
            Err(AstError::ParseError {
                message: format!("Module '{}' is not a directory, cannot contain submodules", intermediate_module),
                span: ligature_ast::Span::default(),
            })
        }
    }

    /// Find a module within a specific register.
    fn find_module_in_register(
        &self,
        register_name: &str,
        module_name: &str,
    ) -> AstResult<PathBuf> {
        // First, find the register directory
        let register_path = self.find_register_directory(register_name)?;

        // Then find the module within that register
        self.find_in_register(&register_path, module_name, false)
    }

    /// Find a register directory by name.
    fn find_register_directory(&self, register_name: &str) -> AstResult<PathBuf> {
        // Search in register paths
        for register_path in &self.register_paths {
            let potential_register = register_path.join(register_name);
            if potential_register.exists() && potential_register.is_dir() {
                return Ok(potential_register);
            }
        }

        Err(AstError::ModuleNotFound {
            module: register_name.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Find a module file in the search paths.
    #[allow(dead_code)]
    fn find_module_file(&self, path: &str) -> AstResult<PathBuf> {
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

        Err(AstError::ModuleNotFound {
            module: path.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Find a module within a register.
    fn find_in_register(&self, register_path: &Path, module_name: &str, for_nested: bool) -> AstResult<PathBuf> {
        // Look for register.toml to understand the register structure
        let register_manifest = register_path.join("register.toml");
        if register_manifest.exists() {
            // Parse register.toml and check exports
            let manifest_content =
                std::fs::read_to_string(&register_manifest).map_err(|e| AstError::ParseError {
                    message: format!("Failed to read register manifest: {}", e),
                    span: ligature_ast::Span::default(),
                })?;

            let manifest: RegisterManifest =
                toml::from_str(&manifest_content).map_err(|e| AstError::ParseError {
                    message: format!("Failed to parse register manifest: {}", e),
                    span: ligature_ast::Span::default(),
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
                register_path
                    .join("src")
                    .join(format!("{}.lig", module_name)),
                register_path.join(format!("{}.lig", module_name)),
                register_path
                    .join("modules")
                    .join(format!("{}.lig", module_name)),
            ];

            for path in &common_paths {
                if path.exists() {
                    return Ok(path.clone());
                }
            }
        }

        // Fallback: look for .lig files in the register directory
        if let Ok(entries) = std::fs::read_dir(register_path) {
            for entry in entries {
                if let Ok(entry) = entry {
                    let path = entry.path();
                    if path.is_file() && path.extension().map_or(false, |ext| ext == "lig") {
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
                            return Err(AstError::ParseError {
                                message: format!("Directory '{}' does not contain a mod.lig file", module_name),
                                span: ligature_ast::Span::default(),
                            });
                        }
                    }
                }
            }
        }

        Err(AstError::ModuleNotFound {
            module: module_name.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Clear the module cache.
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Get a cached module.
    pub fn get_cached(&self, path: &str) -> Option<&Value> {
        self.cache.get(path)
    }

    /// Check if a module is cached.
    pub fn is_cached(&self, path: &str) -> bool {
        self.cache.contains_key(path)
    }
}

impl Default for ModuleResolver {
    fn default() -> Self {
        Self::new()
    }
}
