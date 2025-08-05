use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::error::{CacophonyError, Result};
use crate::ligature_loader::LigatureLoader;
use crate::xdg_config::CacophonyXdgConfig;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacophonyConfig {
    pub project: ProjectConfig,
    pub environments: HashMap<String, EnvironmentConfig>,
    pub collections: HashMap<String, CollectionConfig>,
    pub plugins: Vec<PluginConfig>,
    pub operations: HashMap<String, OperationConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectConfig {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub authors: Vec<String>,
    pub repository: Option<String>,
    pub license: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentConfig {
    pub name: String,
    pub description: Option<String>,
    pub variables: HashMap<String, String>,
    pub plugins: Vec<String>,
    pub overrides: Option<HashMap<String, serde_json::Value>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectionConfig {
    pub name: String,
    pub description: Option<String>,
    pub dependencies: Vec<String>,
    pub operations: Vec<String>,
    pub environments: Vec<String>,
    pub config: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginConfig {
    pub name: String,
    pub version: Option<String>,
    pub config: Option<serde_json::Value>,
    pub enabled: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OperationConfig {
    pub name: String,
    pub description: Option<String>,
    pub script: Option<String>,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
    pub timeout: Option<u64>,
    pub retries: Option<u32>,
}

pub struct ConfigManager {
    config: CacophonyConfig,
    config_path: PathBuf,
    xdg_config: Option<CacophonyXdgConfig>,
}

impl ConfigManager {
    pub fn new(config_path: PathBuf) -> Result<Self> {
        if !config_path.exists() {
            return Err(CacophonyError::NotFound(format!(
                "Configuration file not found: {}",
                config_path.display()
            )));
        }

        let content = std::fs::read_to_string(&config_path).map_err(|e| CacophonyError::Io(e))?;

        // Try to parse as TOML first, then JSON
        let config: CacophonyConfig =
            if config_path.extension().and_then(|s| s.to_str()) == Some("toml") {
                toml::from_str(&content).map_err(|e| CacophonyError::Toml(e))?
            } else {
                serde_json::from_str(&content).map_err(|e| CacophonyError::Json(e))?
            };

        Ok(Self {
            config,
            config_path,
            xdg_config: None,
        })
    }

    /// Create a new config manager with XDG support
    pub async fn with_xdg() -> Result<Self> {
        let xdg_config = CacophonyXdgConfig::new().await?;
        let config_path = xdg_config.default_config_path()?;

        println!(
            "DEBUG: Current directory: {}",
            std::env::current_dir().unwrap().display()
        );
        let mut ligature_loader = LigatureLoader::new()?;
        let current_dir = std::env::current_dir().map_err(|e| {
            CacophonyError::Config(format!("Failed to get current directory: {}", e))
        })?;

        let config = match ligature_loader.find_and_load_config(&current_dir) {
            Ok(local_config) => {
                println!("DEBUG: Successfully loaded local cacophony.lig configuration");
                match serde_json::to_string_pretty(&local_config) {
                    Ok(json) => println!("DEBUG: Parsed config from Ligature: {}", json),
                    Err(e) => println!("DEBUG: Failed to serialize config: {}", e),
                }
                local_config
            }
            Err(e) => {
                println!("DEBUG: LigatureLoader failed: {}", e);
                println!("DEBUG: No local cacophony.lig found, trying XDG config");
                if let Some(xdg_config_data) = xdg_config.load_config().await? {
                    println!("DEBUG: Successfully loaded XDG configuration");
                    xdg_config_data
                } else {
                    println!("DEBUG: No XDG config found, using default configuration");
                    // Create default configuration
                    CacophonyConfig {
                        project: ProjectConfig {
                            name: "default".to_string(),
                            version: "0.1.0".to_string(),
                            description: Some("Default Cacophony project".to_string()),
                            authors: vec!["Cacophony User".to_string()],
                            repository: None,
                            license: Some("Apache-2.0".to_string()),
                        },
                        environments: HashMap::new(),
                        collections: HashMap::new(),
                        plugins: Vec::new(),
                        operations: HashMap::new(),
                    }
                }
            }
        };

        Ok(Self {
            config,
            config_path,
            xdg_config: Some(xdg_config),
        })
    }

    pub fn load_config(path: &PathBuf) -> Result<CacophonyConfig> {
        if !path.exists() {
            return Err(CacophonyError::NotFound(format!(
                "Configuration file not found: {}",
                path.display()
            )));
        }

        let content = std::fs::read_to_string(path).map_err(|e| CacophonyError::Io(e))?;

        // Try to parse as TOML first, then JSON
        let config: CacophonyConfig = if path.extension().and_then(|s| s.to_str()) == Some("toml") {
            toml::from_str(&content).map_err(|e| CacophonyError::Toml(e))?
        } else {
            serde_json::from_str(&content).map_err(|e| CacophonyError::Json(e))?
        };

        Ok(config)
    }

    pub fn save_config(&self) -> Result<()> {
        // If we have XDG config, use it
        if let Some(ref xdg_config) = self.xdg_config {
            // This is async, but we're in a sync context
            // We'll need to handle this differently or make this method async
            return Err(CacophonyError::Internal(
                "XDG save_config requires async context. Use save_config_async() instead."
                    .to_string(),
            ));
        }

        let content = if self.config_path.extension().and_then(|s| s.to_str()) == Some("toml") {
            toml::to_string_pretty(&self.config)
                .map_err(|e| CacophonyError::Internal(format!("TOML serialization error: {}", e)))?
        } else {
            serde_json::to_string_pretty(&self.config).map_err(|e| CacophonyError::Json(e))?
        };

        std::fs::write(&self.config_path, content).map_err(|e| CacophonyError::Io(e))?;

        Ok(())
    }

    /// Save configuration asynchronously (for XDG support)
    pub async fn save_config_async(&self) -> Result<()> {
        if let Some(ref xdg_config) = self.xdg_config {
            xdg_config.save_config(&self.config).await?;
            Ok(())
        } else {
            // Fall back to sync version
            self.save_config()
        }
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

    /// Get the full configuration
    pub fn get_config(&self) -> &CacophonyConfig {
        &self.config
    }

    /// Get XDG configuration if available
    pub fn xdg_config(&self) -> Option<&CacophonyXdgConfig> {
        self.xdg_config.as_ref()
    }

    /// Get XDG paths for various directories
    pub fn xdg_projects_dir(&self) -> Result<Option<PathBuf>> {
        if let Some(ref xdg_config) = self.xdg_config {
            Ok(Some(xdg_config.projects_dir()?))
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

    pub fn validate(&self) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate project configuration
        if self.config.project.name.is_empty() {
            errors.push("Project name cannot be empty".to_string());
        }

        if self.config.project.version.is_empty() {
            errors.push("Project version cannot be empty".to_string());
        }

        // Validate environments
        for (name, env_config) in &self.config.environments {
            if env_config.name.is_empty() {
                errors.push(format!("Environment '{}' name cannot be empty", name));
            }
        }

        // Validate collections
        for (name, coll_config) in &self.config.collections {
            if coll_config.name.is_empty() {
                errors.push(format!("Collection '{}' name cannot be empty", name));
            }

            // Check for missing dependencies
            for dep in &coll_config.dependencies {
                if !self.config.collections.contains_key(dep) {
                    warnings.push(format!(
                        "Collection '{}' depends on '{}' which is not defined",
                        name, dep
                    ));
                }
            }

            // Check for missing environments
            for env in &coll_config.environments {
                if !self.config.environments.contains_key(env) {
                    warnings.push(format!(
                        "Collection '{}' references environment '{}' which is not defined",
                        name, env
                    ));
                }
            }
        }

        // Validate plugins
        for plugin in &self.config.plugins {
            if plugin.name.is_empty() {
                errors.push("Plugin name cannot be empty".to_string());
            }
        }

        // Validate operations
        for (name, op_config) in &self.config.operations {
            if op_config.name.is_empty() {
                errors.push(format!("Operation '{}' name cannot be empty", name));
            }
        }

        Ok(ValidationResult { errors, warnings })
    }
}

#[derive(Debug)]
pub struct ValidationResult {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}
