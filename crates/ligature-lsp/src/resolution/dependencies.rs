//! Dependency management for module relationships.
//!
//! This module provides functionality for tracking dependencies between modules,
//! including forward and reverse dependency graphs.

use std::collections::HashMap;
use std::sync::Arc;

use tokio::sync::RwLock;

/// Manager for tracking module dependencies and relationships.
pub struct DependencyManager {
    /// Import dependency graph for tracking module relationships.
    #[allow(clippy::type_complexity)]
    dependencies: Arc<RwLock<HashMap<String, Vec<String>>>>,
    /// Reverse dependencies for finding modules that import a given module.
    #[allow(clippy::type_complexity)]
    reverse_dependencies: Arc<RwLock<HashMap<String, Vec<String>>>>,
}

impl DependencyManager {
    /// Create a new dependency manager.
    pub fn new() -> Self {
        Self {
            dependencies: Arc::new(RwLock::new(HashMap::new())),
            reverse_dependencies: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Update the dependency graph by adding a dependency relationship.
    pub async fn add_dependency(&self, source: &str, target: &str) {
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

    /// Set the dependencies for a specific module.
    pub async fn set_module_dependencies(&self, module_uri: &str, dependencies: Vec<String>) {
        // Update forward dependencies
        {
            let mut deps = self.dependencies.write().await;
            deps.insert(module_uri.to_string(), dependencies.clone());
        }

        // Update reverse dependencies
        {
            let mut reverse_deps = self.reverse_dependencies.write().await;

            // Remove old reverse dependencies for this module
            for (_target, sources) in reverse_deps.iter_mut() {
                sources.retain(|source| source != module_uri);
            }

            // Add new reverse dependencies
            for dependency in dependencies {
                reverse_deps
                    .entry(dependency)
                    .or_insert_with(Vec::new)
                    .push(module_uri.to_string());
            }
        }
    }

    /// Remove a module and all its dependencies.
    pub async fn remove_module(&self, module_uri: &str) {
        // Remove from forward dependencies
        {
            let mut deps = self.dependencies.write().await;
            deps.remove(module_uri);
        }

        // Remove from reverse dependencies
        {
            let mut reverse_deps = self.reverse_dependencies.write().await;

            // Remove this module from all reverse dependency lists
            for sources in reverse_deps.values_mut() {
                sources.retain(|source| source != module_uri);
            }

            // Remove the module's own reverse dependency entry
            reverse_deps.remove(module_uri);
        }
    }

    /// Check if there are any circular dependencies.
    pub async fn has_circular_dependencies(&self) -> bool {
        let deps = self.dependencies.read().await;

        for module in deps.keys() {
            if self.has_circular_dependency_from(module, &deps).await {
                return true;
            }
        }

        false
    }

    /// Check for circular dependencies starting from a specific module.
    async fn has_circular_dependency_from(
        &self,
        start_module: &str,
        deps: &HashMap<String, Vec<String>>,
    ) -> bool {
        let mut visited = std::collections::HashSet::new();
        let mut recursion_stack = std::collections::HashSet::new();

        self.dfs_for_cycles(start_module, &mut visited, &mut recursion_stack, deps)
    }

    /// Depth-first search to detect cycles in the dependency graph.
    #[allow(clippy::only_used_in_recursion)]
    fn dfs_for_cycles(
        &self,
        module: &str,
        visited: &mut std::collections::HashSet<String>,
        recursion_stack: &mut std::collections::HashSet<String>,
        deps: &HashMap<String, Vec<String>>,
    ) -> bool {
        if recursion_stack.contains(module) {
            return true; // Found a cycle
        }

        if visited.contains(module) {
            return false; // Already processed this module
        }

        visited.insert(module.to_string());
        recursion_stack.insert(module.to_string());

        if let Some(dependencies) = deps.get(module) {
            for dependency in dependencies {
                if self.dfs_for_cycles(dependency, visited, recursion_stack, deps) {
                    return true;
                }
            }
        }

        recursion_stack.remove(module);
        false
    }

    /// Get all modules in dependency order (topological sort).
    pub async fn get_modules_in_dependency_order(&self) -> Vec<String> {
        let deps = self.dependencies.read().await;
        let mut visited = std::collections::HashSet::new();
        let mut result = Vec::new();

        for module in deps.keys() {
            if !visited.contains(module) {
                self.topological_sort_visit(module, &mut visited, &mut result, &deps);
            }
        }

        result.reverse(); // Reverse to get dependency order
        result
    }

    /// Helper function for topological sort.
    #[allow(clippy::only_used_in_recursion)]
    fn topological_sort_visit(
        &self,
        module: &str,
        visited: &mut std::collections::HashSet<String>,
        result: &mut Vec<String>,
        deps: &HashMap<String, Vec<String>>,
    ) {
        visited.insert(module.to_string());

        if let Some(dependencies) = deps.get(module) {
            for dependency in dependencies {
                if !visited.contains(dependency) {
                    self.topological_sort_visit(dependency, visited, result, deps);
                }
            }
        }

        result.push(module.to_string());
    }

    /// Clear all dependencies.
    pub async fn clear(&self) {
        let mut deps = self.dependencies.write().await;
        deps.clear();

        let mut reverse_deps = self.reverse_dependencies.write().await;
        reverse_deps.clear();
    }

    /// Get statistics about the dependency graph.
    pub async fn get_stats(&self) -> super::cache::ModuleStats {
        let deps = self.dependencies.read().await;
        let reverse_deps = self.reverse_dependencies.read().await;

        super::cache::ModuleStats {
            total_modules: 0, // This will be set by the main service
            total_dependencies: deps.values().map(|v| v.len()).sum(),
            total_reverse_dependencies: reverse_deps.values().map(|v| v.len()).sum(),
        }
    }

    /// Get all modules that would be affected by changes to a given module.
    pub async fn get_affected_modules(&self, module_uri: &str) -> Vec<String> {
        let mut affected = std::collections::HashSet::new();
        let mut to_process = vec![module_uri.to_string()];

        while let Some(current) = to_process.pop() {
            if affected.insert(current.clone()) {
                // Add all modules that import this one
                let importing = self.get_importing_modules(&current).await;
                to_process.extend(importing);
            }
        }

        affected.into_iter().collect()
    }
}

impl Default for DependencyManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_dependency_manager_creation() {
        let manager = DependencyManager::new();
        let stats = manager.get_stats().await;
        assert_eq!(stats.total_dependencies, 0);
        assert_eq!(stats.total_reverse_dependencies, 0);
    }

    #[tokio::test]
    async fn test_add_dependency() {
        let manager = DependencyManager::new();

        manager.add_dependency("module_a", "module_b").await;

        let imported = manager.get_imported_modules("module_a").await;
        assert_eq!(imported, vec!["module_b"]);

        let importing = manager.get_importing_modules("module_b").await;
        assert_eq!(importing, vec!["module_a"]);
    }

    #[tokio::test]
    async fn test_set_module_dependencies() {
        let manager = DependencyManager::new();

        let dependencies = vec!["module_b".to_string(), "module_c".to_string()];
        manager
            .set_module_dependencies("module_a", dependencies)
            .await;

        let imported = manager.get_imported_modules("module_a").await;
        assert_eq!(imported.len(), 2);
        assert!(imported.contains(&"module_b".to_string()));
        assert!(imported.contains(&"module_c".to_string()));
    }

    #[tokio::test]
    async fn test_remove_module() {
        let manager = DependencyManager::new();

        manager.add_dependency("module_a", "module_b").await;
        manager.add_dependency("module_c", "module_b").await;

        manager.remove_module("module_a").await;

        let importing = manager.get_importing_modules("module_b").await;
        assert_eq!(importing, vec!["module_c"]);

        let imported = manager.get_imported_modules("module_a").await;
        assert!(imported.is_empty());
    }

    #[tokio::test]
    async fn test_circular_dependency_detection() {
        let manager = DependencyManager::new();

        // No circular dependencies initially
        assert!(!manager.has_circular_dependencies().await);

        // Add circular dependency
        manager.add_dependency("module_a", "module_b").await;
        manager.add_dependency("module_b", "module_c").await;
        manager.add_dependency("module_c", "module_a").await;

        // Should detect circular dependency
        assert!(manager.has_circular_dependencies().await);
    }

    #[tokio::test]
    async fn test_affected_modules() {
        let manager = DependencyManager::new();

        // Create dependency chain: a -> b -> c
        manager.add_dependency("module_a", "module_b").await;
        manager.add_dependency("module_b", "module_c").await;

        // Also: d -> b
        manager.add_dependency("module_d", "module_b").await;

        let affected = manager.get_affected_modules("module_c").await;
        assert_eq!(affected.len(), 4); // c, b, a, d
        assert!(affected.contains(&"module_a".to_string()));
        assert!(affected.contains(&"module_b".to_string()));
        assert!(affected.contains(&"module_c".to_string()));
        assert!(affected.contains(&"module_d".to_string()));
    }

    #[tokio::test]
    async fn test_clear_dependencies() {
        let manager = DependencyManager::new();

        manager.add_dependency("module_a", "module_b").await;
        manager.clear().await;

        let stats = manager.get_stats().await;
        assert_eq!(stats.total_dependencies, 0);
        assert_eq!(stats.total_reverse_dependencies, 0);
    }
}
