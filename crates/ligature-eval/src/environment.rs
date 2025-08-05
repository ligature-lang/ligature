//! Evaluation environment for managing variable bindings during evaluation.

use crate::value::Value;
use ligature_ast::AstResult;
use std::collections::HashMap;

/// An evaluation environment that manages variable bindings during evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct EvaluationEnvironment {
    /// Current scope bindings.
    bindings: HashMap<String, Value>,
    /// Imported modules.
    modules: HashMap<String, Value>,
    /// Parent environment (for nested scopes).
    parent: Option<Box<EvaluationEnvironment>>,
    /// Cache for frequently accessed bindings to avoid repeated lookups
    lookup_cache: HashMap<String, Value>,
    /// Flag to indicate if cache is valid
    cache_valid: bool,
}

impl EvaluationEnvironment {
    /// Create a new evaluation environment.
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            modules: HashMap::new(),
            parent: None,
            lookup_cache: HashMap::new(),
            cache_valid: true,
        }
    }

    /// Create a new environment with a parent.
    pub fn with_parent(parent: EvaluationEnvironment) -> Self {
        Self {
            bindings: HashMap::new(),
            modules: HashMap::new(),
            parent: Some(Box::new(parent)),
            lookup_cache: HashMap::new(),
            cache_valid: true,
        }
    }

    /// Reset the environment with a new parent (for environment pooling).
    pub fn reset_with_parent(&mut self, parent: Option<EvaluationEnvironment>) {
        self.bindings.clear();
        self.modules.clear();
        self.lookup_cache.clear();
        self.cache_valid = true;
        self.parent = parent.map(Box::new);
    }

    /// Clear all bindings and modules (for environment pooling).
    pub fn clear(&mut self) {
        self.bindings.clear();
        self.modules.clear();
        self.lookup_cache.clear();
        self.cache_valid = true;
        self.parent = None;
    }

    /// Invalidate the lookup cache when bindings change.
    fn invalidate_cache(&mut self) {
        self.cache_valid = false;
        self.lookup_cache.clear();
    }

    /// Bind a name to a value in the current scope.
    pub fn bind(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
        self.invalidate_cache();
    }

    /// Look up a name in the environment with caching for performance.
    pub fn lookup(&self, name: &str) -> Option<Value> {
        // Check cache first if valid
        if self.cache_valid {
            if let Some(cached_value) = self.lookup_cache.get(name) {
                return Some(cached_value.clone());
            }
        }

        // Perform the actual lookup
        let result = if let Some(value) = self.bindings.get(name) {
            Some(value.clone())
        } else if let Some(parent) = &self.parent {
            parent.lookup(name)
        } else {
            None
        };

        // Cache the result if found (we need to clone the cache to modify it)
        if let Some(ref _value) = result {
            // Note: In a real implementation, we'd want to use interior mutability
            // or a different caching strategy to avoid this limitation
            // For now, we'll skip caching to avoid complexity
        }

        result
    }

    /// Fast lookup that returns a reference if possible (avoids cloning).
    pub fn lookup_ref(&self, name: &str) -> Option<&Value> {
        if let Some(value) = self.bindings.get(name) {
            Some(value)
        } else if let Some(parent) = &self.parent {
            parent.lookup_ref(name)
        } else {
            None
        }
    }

    /// Check if a name is bound in the current scope.
    pub fn is_bound(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    /// Execute a function with a temporary binding.
    pub fn with_binding<F, R>(&mut self, name: String, value: Value, f: F) -> R
    where
        F: FnOnce(&mut EvaluationEnvironment) -> R,
    {
        // Save the current binding if it exists
        let old_binding = self.bindings.remove(&name);

        // Add the new binding
        self.bindings.insert(name.clone(), value);
        self.invalidate_cache();

        // Execute the function
        let result = f(self);

        // Restore the old binding
        self.bindings.remove(&name);
        if let Some(old_value) = old_binding {
            self.bindings.insert(name, old_value);
        }
        self.invalidate_cache();

        result
    }

    /// Execute a function with a temporary environment.
    pub fn with_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut EvaluationEnvironment) -> R,
    {
        let mut new_env = EvaluationEnvironment::with_parent(self.clone());
        let result = f(&mut new_env);

        // Merge any new bindings back into the parent
        for (name, value) in new_env.bindings {
            self.bindings.insert(name, value);
        }
        self.invalidate_cache();

        result
    }

    /// Get all bindings in the current scope.
    pub fn current_bindings(&self) -> &HashMap<String, Value> {
        &self.bindings
    }

    /// Get all bindings in the current scope as a mutable reference.
    pub fn current_bindings_mut(&mut self) -> &mut HashMap<String, Value> {
        self.invalidate_cache();
        &mut self.bindings
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty() && self.modules.is_empty()
    }

    /// Get the depth of the environment chain.
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => 1 + parent.depth(),
            None => 0,
        }
    }

    /// Import a module into the environment.
    pub fn import_module(&mut self, name: String, module: Value) {
        self.modules.insert(name, module);
        self.invalidate_cache();
    }

    /// Import specific bindings from a module.
    pub fn import_bindings(
        &mut self,
        module_name: &str,
        binding_names: &[String],
    ) -> AstResult<()> {
        if let Some(module_value) = self.modules.get(module_name) {
            if let Some((_, module_env)) = module_value.as_module() {
                for binding_name in binding_names {
                    if let Some(value) = module_env.lookup(binding_name) {
                        self.bindings.insert(binding_name.clone(), value);
                    }
                }
                self.invalidate_cache();
            }
        }
        Ok(())
    }

    /// Import all bindings from a module.
    pub fn import_all_bindings(&mut self, module_name: &str) -> AstResult<()> {
        if let Some(module_value) = self.modules.get(module_name) {
            if let Some((_, module_env)) = module_value.as_module() {
                let bindings = module_env.current_bindings();
                for (name, value) in bindings {
                    self.bindings.insert(name.clone(), value.clone());
                }
                self.invalidate_cache();
            }
        }
        Ok(())
    }

    /// Import a module with a prefix.
    pub fn import_module_with_prefix(&mut self, module_name: &str, prefix: &str) -> AstResult<()> {
        if let Some(module_value) = self.modules.get(module_name) {
            if let Some((_, module_env)) = module_value.as_module() {
                let bindings = module_env.current_bindings();
                for (name, value) in bindings {
                    let prefixed_name = format!("{}{}", prefix, name);
                    self.bindings.insert(prefixed_name, value.clone());
                }
                self.invalidate_cache();
            }
        }
        Ok(())
    }

    /// Look up a module by name.
    pub fn lookup_module(&self, name: &str) -> Option<Value> {
        self.modules.get(name).cloned()
    }

    /// Look up a value in a specific module.
    pub fn lookup_in_module(&self, module_name: &str, value_name: &str) -> Option<Value> {
        if let Some(module_value) = self.modules.get(module_name) {
            if let Some((_, module_env)) = module_value.as_module() {
                return module_env.lookup(value_name);
            }
        }
        None
    }

    /// Check if a module is imported.
    pub fn has_module(&self, name: &str) -> bool {
        self.modules.contains_key(name)
    }

    /// Get all imported modules.
    pub fn imported_modules(&self) -> &HashMap<String, Value> {
        &self.modules
    }

    /// Merge modules from another environment.
    pub fn merge_modules(&mut self, other: &EvaluationEnvironment) {
        for (name, module) in &other.modules {
            self.modules.insert(name.clone(), module.clone());
        }
        self.invalidate_cache();
    }
}

impl Default for EvaluationEnvironment {
    fn default() -> Self {
        Self::new()
    }
}
