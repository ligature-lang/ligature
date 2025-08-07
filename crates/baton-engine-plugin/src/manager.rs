//! Plugin manager for Baton verification engines.

use crate::traits::{EnginePlugin, VerificationEngine};
use crate::engine::{EngineCapabilities, EngineInfo, EngineStatus};
use baton_error::prelude::*;
use serde_json::Value;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type PluginBox = Box<dyn EnginePlugin>;

/// Manages the registration and lifecycle of verification engine plugins.
pub struct EnginePluginManager {
    /// Registered plugins
    #[allow(clippy::type_complexity)]
    plugins: Arc<Mutex<HashMap<String, PluginBox>>>,
    /// Active engines
    #[allow(clippy::type_complexity)]
    active_engines: Arc<Mutex<HashMap<String, Box<dyn VerificationEngine>>>>,
    /// Plugin configurations
    #[allow(clippy::type_complexity)]
    configurations: Arc<Mutex<HashMap<String, Value>>>,
    /// Default engine name
    default_engine: Arc<Mutex<Option<String>>>,
}

impl EnginePluginManager {
    /// Create a new plugin manager.
    pub fn new() -> Self {
        Self {
            plugins: Arc::new(Mutex::new(HashMap::new())),
            active_engines: Arc::new(Mutex::new(HashMap::new())),
            configurations: Arc::new(Mutex::new(HashMap::new())),
            default_engine: Arc::new(Mutex::new(None)),
        }
    }

    /// Register a new engine plugin.
    pub async fn register_plugin(&self, plugin: PluginBox) -> BatonResult<()> {
        let plugin_name = plugin.name().to_string();
        let mut plugins = self.plugins.lock().await;
        
        if plugins.contains_key(&plugin_name) {
            return Err(BatonError::ConfigurationError(
                format!("Plugin '{plugin_name}' is already registered")
            ));
        }

        plugins.insert(plugin_name.clone(), plugin);
        
        // Set as default if it's the first plugin
        let mut default_engine = self.default_engine.lock().await;
        if default_engine.is_none() {
            *default_engine = Some(plugin_name);
        }

        Ok(())
    }

    /// Unregister a plugin.
    pub async fn unregister_plugin(&self, name: &str) -> BatonResult<()> {
        let mut plugins = self.plugins.lock().await;
        let mut active_engines = self.active_engines.lock().await;
        let mut configurations = self.configurations.lock().await;

        // Shutdown the plugin if it's active
        if let Some(plugin) = plugins.get_mut(name) {
            plugin.shutdown().await?;
        }

        // Remove from all collections
        plugins.remove(name);
        active_engines.remove(name);
        configurations.remove(name);

        // Update default engine if necessary
        let mut default_engine = self.default_engine.lock().await;
        if default_engine.as_ref() == Some(&name.to_string()) {
            *default_engine = plugins.keys().next().cloned();
        }

        Ok(())
    }

    /// Initialize a plugin with configuration.
    pub async fn initialize_plugin(&self, name: &str, config: &Value) -> BatonResult<()> {
        let mut plugins = self.plugins.lock().await;
        let mut configurations = self.configurations.lock().await;

        let plugin = plugins.get_mut(name)
            .ok_or_else(|| BatonError::ConfigurationError(format!("Plugin '{name}' not found")))?;

        // Initialize the plugin
        plugin.initialize(config).await?;

        // Store the configuration
        configurations.insert(name.to_string(), config.clone());

        // Get the engine instance
        let engine = plugin.get_engine()?;
        let mut active_engines = self.active_engines.lock().await;
        active_engines.insert(name.to_string(), engine);

        Ok(())
    }

    /// Get a verification engine by name.
    pub async fn get_engine(&self, name: &str) -> BatonResult<Box<dyn VerificationEngine>> {
        let active_engines = self.active_engines.lock().await;
        
        if let Some(_engine) = active_engines.get(name) {
            // Clone the engine trait object (this requires the engine to implement Clone)
            // For now, we'll return an error if the engine doesn't support cloning
            Err(BatonError::InternalError(
                "Engine cloning not yet implemented".to_string()
            ))
        } else {
            Err(BatonError::ConfigurationError(format!("Engine '{name}' not found or not initialized")))
        }
    }

    /// Get the default verification engine.
    pub async fn get_default_engine(&self) -> BatonResult<Box<dyn VerificationEngine>> {
        let default_engine = self.default_engine.lock().await;
        
        if let Some(ref name) = *default_engine {
            self.get_engine(name).await
        } else {
            Err(BatonError::ConfigurationError("No default engine set".to_string()))
        }
    }

    /// Set the default engine.
    pub async fn set_default_engine(&self, name: &str) -> BatonResult<()> {
        let plugins = self.plugins.lock().await;
        
        if !plugins.contains_key(name) {
            return Err(BatonError::ConfigurationError(format!("Plugin '{name}' not found")));
        }

        let mut default_engine = self.default_engine.lock().await;
        *default_engine = Some(name.to_string());

        Ok(())
    }

    /// Get plugin information.
    pub async fn get_plugin_info(&self, name: &str) -> BatonResult<EngineInfo> {
        let plugins = self.plugins.lock().await;
        
        let plugin = plugins.get(name)
            .ok_or_else(|| BatonError::ConfigurationError(format!("Plugin '{name}' not found")))?;

        Ok(plugin.engine_info())
    }

    /// Get plugin capabilities.
    pub async fn get_plugin_capabilities(&self, name: &str) -> BatonResult<EngineCapabilities> {
        let plugins = self.plugins.lock().await;
        
        let plugin = plugins.get(name)
            .ok_or_else(|| BatonError::ConfigurationError(format!("Plugin '{name}' not found")))?;

        Ok(plugin.capabilities())
    }

    /// Get plugin status.
    pub async fn get_plugin_status(&self, name: &str) -> BatonResult<EngineStatus> {
        let plugins = self.plugins.lock().await;
        
        let plugin = plugins.get(name)
            .ok_or_else(|| BatonError::ConfigurationError(format!("Plugin '{name}' not found")))?;

        plugin.status().await
    }

    /// List all registered plugins.
    pub async fn list_plugins(&self) -> Vec<String> {
        let plugins = self.plugins.lock().await;
        plugins.keys().cloned().collect()
    }

    /// List all active engines.
    pub async fn list_active_engines(&self) -> Vec<String> {
        let active_engines = self.active_engines.lock().await;
        active_engines.keys().cloned().collect()
    }

    /// Check if a plugin is registered.
    pub async fn has_plugin(&self, name: &str) -> bool {
        let plugins = self.plugins.lock().await;
        plugins.contains_key(name)
    }

    /// Check if an engine is active.
    pub async fn is_engine_active(&self, name: &str) -> bool {
        let active_engines = self.active_engines.lock().await;
        active_engines.contains_key(name)
    }

    /// Get the number of registered plugins.
    pub async fn plugin_count(&self) -> usize {
        let plugins = self.plugins.lock().await;
        plugins.len()
    }

    /// Get the number of active engines.
    pub async fn active_engine_count(&self) -> usize {
        let active_engines = self.active_engines.lock().await;
        active_engines.len()
    }

    /// Configure a plugin.
    pub async fn configure_plugin(&self, name: &str, config: &Value) -> BatonResult<()> {
        let mut plugins = self.plugins.lock().await;
        
        let plugin = plugins.get_mut(name)
            .ok_or_else(|| BatonError::ConfigurationError(format!("Plugin '{name}' not found")))?;

        plugin.configure(config).await?;

        // Update stored configuration
        let mut configurations = self.configurations.lock().await;
        configurations.insert(name.to_string(), config.clone());

        Ok(())
    }

    /// Get plugin configuration.
    pub async fn get_plugin_config(&self, name: &str) -> BatonResult<Value> {
        let configurations = self.configurations.lock().await;
        
        configurations.get(name)
            .cloned()
            .ok_or_else(|| BatonError::ConfigurationError(format!("Configuration for plugin '{name}' not found")))
    }

    /// Shutdown all plugins.
    pub async fn shutdown_all(&self) -> BatonResult<()> {
        let mut plugins = self.plugins.lock().await;
        let mut active_engines = self.active_engines.lock().await;

        // Shutdown all plugins
        for plugin in plugins.values_mut() {
            if let Err(e) = plugin.shutdown().await {
                eprintln!("Error shutting down plugin {}: {:?}", plugin.name(), e);
            }
        }

        // Clear active engines
        active_engines.clear();

        Ok(())
    }

    /// Get manager statistics.
    pub async fn get_stats(&self) -> ManagerStats {
        let plugins = self.plugins.lock().await;
        let active_engines = self.active_engines.lock().await;
        let default_engine = self.default_engine.lock().await;

        ManagerStats {
            total_plugins: plugins.len(),
            active_engines: active_engines.len(),
            default_engine: default_engine.clone(),
            plugin_names: plugins.keys().cloned().collect(),
            active_engine_names: active_engines.keys().cloned().collect(),
        }
    }

    /// Health check for all active engines.
    pub async fn health_check(&self) -> HashMap<String, bool> {
        let mut health_status = HashMap::new();
        let active_engines = self.active_engines.lock().await;

        for (name, engine) in active_engines.iter() {
            let health = engine.ping().await.unwrap_or(false);
            health_status.insert(name.clone(), health);
        }

        health_status
    }
}

impl Default for EnginePluginManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for the plugin manager.
#[derive(Debug, Clone)]
pub struct ManagerStats {
    /// Total number of registered plugins
    pub total_plugins: usize,
    /// Number of active engines
    pub active_engines: usize,
    /// Name of the default engine
    pub default_engine: Option<String>,
    /// Names of all registered plugins
    pub plugin_names: Vec<String>,
    /// Names of all active engines
    pub active_engine_names: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::{EnginePlugin, VerificationEngine};
    use crate::engine::{EngineCapabilities, EngineInfo, EngineStatus};
    use baton_protocol::prelude::*;
    use async_trait::async_trait;

    // Mock plugin for testing
    struct MockPlugin {
        name: String,
        initialized: bool,
    }

    impl MockPlugin {
        fn new(name: &str) -> Self {
            Self {
                name: name.to_string(),
                initialized: false,
            }
        }
    }

    #[async_trait]
    impl EnginePlugin for MockPlugin {
        fn name(&self) -> &str {
            &self.name
        }

        fn version(&self) -> &str {
            "1.0.0"
        }

        fn description(&self) -> &str {
            "Mock plugin for testing"
        }

        fn engine_info(&self) -> EngineInfo {
            EngineInfo {
                name: self.name.clone(),
                version: "1.0.0".to_string(),
                description: "Mock engine".to_string(),
                vendor: "Test".to_string(),
                homepage: None,
                documentation: None,
                license: None,
                supported_languages: vec!["rust".to_string()],
                supported_features: vec!["evaluation".to_string()],
                config_schema: None,
            }
        }

        fn capabilities(&self) -> EngineCapabilities {
            EngineCapabilities::default()
        }

        async fn initialize(&mut self, _config: &Value) -> BatonResult<()> {
            self.initialized = true;
            Ok(())
        }

        async fn shutdown(&mut self) -> BatonResult<()> {
            self.initialized = false;
            Ok(())
        }

        async fn status(&self) -> BatonResult<EngineStatus> {
            if self.initialized {
                Ok(EngineStatus::Ready)
            } else {
                Ok(EngineStatus::Uninitialized)
            }
        }

        async fn configure(&mut self, _config: &Value) -> BatonResult<()> {
            Ok(())
        }

        fn get_engine(&self) -> BatonResult<Box<dyn VerificationEngine>> {
            Err(BatonError::InternalError("Mock engine not implemented".to_string()))
        }
    }

    #[tokio::test]
    async fn test_plugin_registration() {
        let manager = EnginePluginManager::new();
        let plugin = MockPlugin::new("test");

        // Register plugin
        assert!(manager.register_plugin(Box::new(plugin)).await.is_ok());
        assert!(manager.has_plugin("test").await);
        assert_eq!(manager.plugin_count().await, 1);

        // Try to register duplicate
        let plugin2 = MockPlugin::new("test");
        assert!(manager.register_plugin(Box::new(plugin2)).await.is_err());
    }

    #[tokio::test]
    async fn test_plugin_unregistration() {
        let manager = EnginePluginManager::new();
        let plugin = MockPlugin::new("test");

        // Register and then unregister
        assert!(manager.register_plugin(Box::new(plugin)).await.is_ok());
        assert!(manager.has_plugin("test").await);
        
        assert!(manager.unregister_plugin("test").await.is_ok());
        assert!(!manager.has_plugin("test").await);
        assert_eq!(manager.plugin_count().await, 0);
    }

    #[tokio::test]
    async fn test_default_engine_setting() {
        let manager = EnginePluginManager::new();
        let plugin = MockPlugin::new("test");

        // Register plugin
        assert!(manager.register_plugin(Box::new(plugin)).await.is_ok());
        
        // Should be set as default automatically
        let stats = manager.get_stats().await;
        assert_eq!(stats.default_engine, Some("test".to_string()));

        // Set different default
        assert!(manager.set_default_engine("test").await.is_ok());
        
        // Try to set non-existent default
        assert!(manager.set_default_engine("nonexistent").await.is_err());
    }
} 