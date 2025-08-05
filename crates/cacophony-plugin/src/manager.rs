use serde_json::Value;
use std::collections::HashMap;

use cacophony_core::{CacophonyError, Operation, Plugin, Result};

type PluginBox = Box<dyn Plugin>;

/// Manages the registration and lifecycle of plugins
pub struct PluginManager {
    plugins: HashMap<String, PluginBox>,
}

impl PluginManager {
    /// Create a new plugin manager with built-in plugins
    pub fn new() -> Self {
        let mut manager = Self {
            plugins: HashMap::new(),
        };

        // Register built-in plugins
        manager.register_plugin(Box::new(crate::terraform::TerraformPlugin::new()));

        manager
    }

    /// Register a new plugin
    pub fn register_plugin(&mut self, plugin: PluginBox) {
        self.plugins.insert(plugin.name().to_string(), plugin);
    }

    /// Get a plugin by name
    pub fn get_plugin(&self, name: &str) -> Option<&dyn Plugin> {
        self.plugins.get(name).map(|b| b.as_ref())
    }

    /// Get a mutable reference to a plugin by name
    pub fn get_plugin_mut(&mut self, name: &str) -> Option<&mut (dyn Plugin + '_)> {
        if let Some(plugin) = self.plugins.get_mut(name) {
            Some(plugin.as_mut())
        } else {
            None
        }
    }

    /// List all registered plugin names
    pub fn list_plugins(&self) -> Vec<&str> {
        self.plugins.keys().map(|s| s.as_str()).collect()
    }

    /// Get all operations from all registered plugins
    pub fn get_operations(&self) -> Vec<Box<dyn Operation>> {
        let mut operations = Vec::new();

        for plugin in self.plugins.values() {
            operations.extend(plugin.operations());
        }

        operations
    }

    /// Configure a plugin with the given configuration
    pub fn configure_plugin(&mut self, name: &str, config: &Value) -> Result<()> {
        let plugin = self
            .get_plugin_mut(name)
            .ok_or_else(|| CacophonyError::NotFound(format!("Plugin '{name}' not found")))?;

        plugin.configure(config)
    }

    /// Check if a plugin is registered
    pub fn has_plugin(&self, name: &str) -> bool {
        self.plugins.contains_key(name)
    }

    /// Remove a plugin by name
    pub fn remove_plugin(&mut self, name: &str) -> Option<PluginBox> {
        self.plugins.remove(name)
    }

    /// Get the number of registered plugins
    pub fn plugin_count(&self) -> usize {
        self.plugins.len()
    }
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::terraform::TerraformPlugin;

    #[test]
    fn test_plugin_manager_creation() {
        let manager = PluginManager::new();
        assert!(manager.has_plugin("terraform"));
        assert_eq!(manager.plugin_count(), 1);
    }

    #[test]
    fn test_plugin_registration() {
        let manager = PluginManager::new();

        // Clear existing plugins for test
        let _ = manager;
        let mut manager = PluginManager {
            plugins: HashMap::new(),
        };

        let plugin = TerraformPlugin::new();
        manager.register_plugin(Box::new(plugin));

        assert!(manager.has_plugin("terraform"));
        assert_eq!(manager.plugin_count(), 1);
    }

    #[test]
    fn test_plugin_retrieval() {
        let manager = PluginManager::new();

        let plugin = manager.get_plugin("terraform");
        assert!(plugin.is_some());
        assert_eq!(plugin.unwrap().name(), "terraform");
    }

    #[test]
    fn test_plugin_listing() {
        let manager = PluginManager::new();
        let plugins = manager.list_plugins();

        assert!(plugins.contains(&"terraform"));
        assert_eq!(plugins.len(), 1);
    }

    #[test]
    fn test_operations_retrieval() {
        let manager = PluginManager::new();
        let operations = manager.get_operations();

        assert!(!operations.is_empty());

        let operation_names: Vec<&str> = operations.iter().map(|op| op.name()).collect();
        assert!(operation_names.contains(&"terraform-plan"));
        assert!(operation_names.contains(&"terraform-apply"));
        assert!(operation_names.contains(&"terraform-destroy"));
    }

    #[test]
    fn test_plugin_removal() {
        let mut manager = PluginManager::new();

        assert!(manager.has_plugin("terraform"));

        let removed = manager.remove_plugin("terraform");
        assert!(removed.is_some());
        assert!(!manager.has_plugin("terraform"));
        assert_eq!(manager.plugin_count(), 0);
    }
}
