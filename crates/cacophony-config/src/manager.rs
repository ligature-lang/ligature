use std::collections::HashMap;
use std::path::PathBuf;

use cacophony_core::config::*;
use cacophony_core::error::{CacophonyError, Result};

use super::validation::ValidationResult;
use super::xdg::CacophonyXdgConfig;

pub struct ConfigManager {
    config: CacophonyConfig,
    config_path: PathBuf,
    xdg_config: Option<CacophonyXdgConfig>,
}

impl ConfigManager {
    pub fn new(config_path: PathBuf) -> Result<Self> {
        let config = if config_path.exists() {
            Self::load_config(&config_path)?
        } else {
            Self::default_config()
        };

        Ok(Self {
            config,
            config_path,
            xdg_config: None,
        })
    }

    pub fn with_xdg_config(mut self, xdg_config: CacophonyXdgConfig) -> Self {
        self.xdg_config = Some(xdg_config);
        self
    }

    pub fn load_config(path: &PathBuf) -> Result<CacophonyConfig> {
        let content = std::fs::read_to_string(path).map_err(CacophonyError::Io)?;

        if path.extension().and_then(|s| s.to_str()) == Some("toml") {
            toml::from_str(&content).map_err(CacophonyError::TomlDe)
        } else {
            serde_json::from_str(&content).map_err(CacophonyError::Json)
        }
    }

    pub fn save_config(&self) -> Result<()> {
        let content = if self.config_path.extension().and_then(|s| s.to_str()) == Some("toml") {
            toml::to_string_pretty(&self.config).map_err(CacophonyError::TomlSer)?
        } else {
            serde_json::to_string_pretty(&self.config).map_err(CacophonyError::Json)?
        };

        std::fs::write(&self.config_path, content).map_err(CacophonyError::Io)?;

        Ok(())
    }

    pub async fn save_config_async(&self) -> Result<()> {
        let content = if self.config_path.extension().and_then(|s| s.to_str()) == Some("toml") {
            toml::to_string_pretty(&self.config).map_err(CacophonyError::TomlSer)?
        } else {
            serde_json::to_string_pretty(&self.config).map_err(CacophonyError::Json)?
        };

        tokio::fs::write(&self.config_path, content)
            .await
            .map_err(CacophonyError::Io)?;

        Ok(())
    }

    pub fn get_project_config(&self) -> &ProjectConfig {
        &self.config.project
    }

    pub fn get_environment_config(&self, name: &str) -> Option<&EnvironmentConfig> {
        self.config.environments.get(name)
    }

    pub fn get_collection_config(&self, name: &str) -> Option<&CollectionConfig> {
        self.config.collections.get(name)
    }

    pub fn get_plugin_config(&self, name: &str) -> Option<&PluginConfig> {
        self.config.plugins.iter().find(|p| p.name == name)
    }

    pub fn get_operation_config(&self, name: &str) -> Option<&OperationConfig> {
        self.config.operations.get(name)
    }

    pub fn list_environments(&self) -> Vec<&str> {
        self.config
            .environments
            .keys()
            .map(|s| s.as_str())
            .collect()
    }

    pub fn list_collections(&self) -> Vec<&str> {
        self.config.collections.keys().map(|s| s.as_str()).collect()
    }

    pub fn list_plugins(&self) -> Vec<&str> {
        self.config
            .plugins
            .iter()
            .map(|p| p.name.as_str())
            .collect()
    }

    pub fn list_operations(&self) -> Vec<&str> {
        self.config.operations.keys().map(|s| s.as_str()).collect()
    }

    pub fn get_config(&self) -> &CacophonyConfig {
        &self.config
    }

    pub fn add_environment(&mut self, name: String, config: EnvironmentConfig) {
        self.config.environments.insert(name, config);
    }

    pub fn add_collection(&mut self, name: String, config: CollectionConfig) {
        self.config.collections.insert(name, config);
    }

    pub fn add_plugin(&mut self, config: PluginConfig) {
        self.config.plugins.push(config);
    }

    pub fn add_operation(&mut self, name: String, config: OperationConfig) {
        self.config.operations.insert(name, config);
    }

    pub fn validate(&self) -> ValidationResult {
        let mut result = ValidationResult::new();

        // Validate project configuration
        if self.config.project.name.is_empty() {
            result.add_error("Project name cannot be empty".to_string());
        }

        if self.config.project.version.is_empty() {
            result.add_error("Project version cannot be empty".to_string());
        }

        // Validate environments
        for (name, env_config) in &self.config.environments {
            if name.is_empty() {
                result.add_error("Environment name cannot be empty".to_string());
            }

            if env_config.name != *name {
                result.add_warning(format!(
                    "Environment config name '{}' doesn't match key '{}'",
                    env_config.name, name
                ));
            }
        }

        // Validate collections
        for (name, collection_config) in &self.config.collections {
            if name.is_empty() {
                result.add_error("Collection name cannot be empty".to_string());
            }

            if collection_config.name != *name {
                result.add_warning(format!(
                    "Collection config name '{}' doesn't match key '{}'",
                    collection_config.name, name
                ));
            }
        }

        // Validate plugins
        for plugin_config in &self.config.plugins {
            if plugin_config.name.is_empty() {
                result.add_error("Plugin name cannot be empty".to_string());
            }
        }

        result
    }

    pub fn xdg_config(&self) -> Option<&CacophonyXdgConfig> {
        self.xdg_config.as_ref()
    }

    pub fn xdg_projects_dir(&self) -> Result<Option<PathBuf>> {
        if let Some(ref xdg_config) = self.xdg_config {
            Ok(Some(xdg_config.data_dir()?.join("projects")))
        } else {
            Ok(None)
        }
    }

    pub fn xdg_plugins_dir(&self) -> Result<Option<PathBuf>> {
        if let Some(ref xdg_config) = self.xdg_config {
            Ok(Some(xdg_config.plugins_dir()?))
        } else {
            Ok(None)
        }
    }

    pub fn xdg_artifacts_cache_dir(&self) -> Result<Option<PathBuf>> {
        if let Some(ref xdg_config) = self.xdg_config {
            Ok(Some(xdg_config.artifacts_cache_dir()?))
        } else {
            Ok(None)
        }
    }

    pub fn xdg_runtime_state_dir(&self) -> Result<Option<PathBuf>> {
        if let Some(ref xdg_config) = self.xdg_config {
            Ok(Some(xdg_config.runtime_state_dir()?))
        } else {
            Ok(None)
        }
    }

    fn default_config() -> CacophonyConfig {
        CacophonyConfig {
            project: ProjectConfig {
                name: "default".to_string(),
                version: "0.1.0".to_string(),
                description: None,
                authors: vec!["Ligature Team".to_string()],
                repository: None,
                license: None,
            },
            environments: HashMap::new(),
            collections: HashMap::new(),
            plugins: Vec::new(),
            operations: HashMap::new(),
        }
    }
}
