//! Configuration file management using XDG base directories.

use std::path::{Path, PathBuf};

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::error::{Result, XdgError};
use crate::paths::XdgPaths;

/// Configuration manager for a Ligature component.
///
/// This struct provides a unified interface for loading and saving configuration
/// files using XDG base directories with fallback support.
#[derive(Debug, Clone)]
pub struct XdgConfig {
    /// XDG paths for this component
    paths: XdgPaths,
    /// Default configuration filename
    default_filename: String,
}

impl XdgConfig {
    /// Create a new configuration manager for a component.
    ///
    /// # Arguments
    ///
    /// * `component` - The component name (e.g., "keywork", "krox", "cli", "lsp")
    /// * `default_filename` - The default configuration filename (e.g., "config.json")
    ///
    /// # Returns
    ///
    /// Returns an error if the component name is invalid or XDG directories cannot be determined.
    pub fn new(component: &str, default_filename: &str) -> Result<Self> {
        let paths = XdgPaths::new(component)?;

        Ok(Self {
            paths,
            default_filename: default_filename.to_string(),
        })
    }

    /// Load configuration from the default location.
    ///
    /// Searches for the configuration file in the following order:
    /// 1. User-specific config directory
    /// 2. System-wide config directories
    ///
    /// # Returns
    ///
    /// Returns the loaded configuration, or None if no configuration file is found.
    pub async fn load<T>(&self) -> Result<Option<T>>
    where
        T: DeserializeOwned,
    {
        self.load_from(&self.default_filename).await
    }

    /// Load configuration from a specific filename.
    ///
    /// # Arguments
    ///
    /// * `filename` - The configuration filename
    ///
    /// # Returns
    ///
    /// Returns the loaded configuration, or None if no configuration file is found.
    pub async fn load_from<T>(&self, filename: &str) -> Result<Option<T>>
    where
        T: DeserializeOwned,
    {
        if let Some(config_path) = self.paths.find_config_file(filename)? {
            let content = tokio::fs::read_to_string(&config_path).await.map_err(|e| {
                XdgError::ReadFileError {
                    path: config_path.display().to_string(),
                    source: e,
                }
            })?;

            // Skip empty files
            if content.trim().is_empty() {
                return Ok(None);
            }

            let config: T = self.deserialize_content(&content, &config_path)?;
            Ok(Some(config))
        } else {
            Ok(None)
        }
    }

    /// Save configuration to the default location.
    ///
    /// Creates the configuration directory if it doesn't exist.
    ///
    /// # Arguments
    ///
    /// * `config` - The configuration to save
    ///
    /// # Returns
    ///
    /// Returns the path where the configuration was saved.
    pub async fn save<T>(&self, config: &T) -> Result<PathBuf>
    where
        T: Serialize,
    {
        self.save_to(&self.default_filename, config).await
    }

    /// Save configuration to a specific filename.
    ///
    /// # Arguments
    ///
    /// * `filename` - The configuration filename
    /// * `config` - The configuration to save
    ///
    /// # Returns
    ///
    /// Returns the path where the configuration was saved.
    pub async fn save_to<T>(&self, filename: &str, config: &T) -> Result<PathBuf>
    where
        T: Serialize,
    {
        // Ensure the config directory exists
        self.paths.ensure_directories().await?;

        let config_path = self.paths.config_file(filename)?;
        let content = self.serialize_content(config, &config_path)?;

        tokio::fs::write(&config_path, content)
            .await
            .map_err(|e| XdgError::WriteFileError {
                path: config_path.display().to_string(),
                source: e,
            })?;

        Ok(config_path)
    }

    /// Get the default configuration file path.
    pub fn default_config_path(&self) -> Result<PathBuf> {
        self.paths.config_file(&self.default_filename)
    }

    /// Get the XDG paths for this component.
    pub fn paths(&self) -> &XdgPaths {
        &self.paths
    }

    /// Get the component name.
    pub fn component(&self) -> &str {
        self.paths.component()
    }

    /// Get the default filename.
    pub fn default_filename(&self) -> &str {
        &self.default_filename
    }

    /// Deserialize content based on file extension.
    ///
    /// Supports JSON and YAML formats.
    fn deserialize_content<T>(&self, content: &str, path: &Path) -> Result<T>
    where
        T: DeserializeOwned,
    {
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or("json");

        match extension {
            "json" => serde_json::from_str(content).map_err(XdgError::DeserializationError),
            "yaml" | "yml" => serde_yaml::from_str(content)
                .map_err(|e| XdgError::InvalidConfig(format!("YAML deserialization error: {e}"))),
            "toml" => toml::from_str(content)
                .map_err(|e| XdgError::InvalidConfig(format!("TOML deserialization error: {e}"))),
            _ => Err(XdgError::InvalidConfig(format!(
                "Unsupported file extension: {extension}",
            ))),
        }
    }

    /// Serialize content based on file extension.
    ///
    /// Supports JSON and YAML formats.
    fn serialize_content<T>(&self, config: &T, path: &Path) -> Result<String>
    where
        T: Serialize,
    {
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or("json");

        match extension {
            "json" => serde_json::to_string_pretty(config).map_err(XdgError::SerializationError),
            "yaml" | "yml" => serde_yaml::to_string(config)
                .map_err(|e| XdgError::InvalidConfig(format!("YAML serialization error: {e}"))),
            "toml" => toml::to_string_pretty(config)
                .map_err(|e| XdgError::InvalidConfig(format!("TOML serialization error: {e}"))),
            _ => Err(XdgError::InvalidConfig(format!(
                "Unsupported file extension: {extension}",
            ))),
        }
    }
}

/// Convenience function to create a configuration manager for common components.
///
/// # Arguments
///
/// * `component` - The component name
///
/// # Returns
///
/// Returns a configuration manager with a default JSON configuration file.
pub fn config_for_component(component: &str) -> Result<XdgConfig> {
    XdgConfig::new(component, "config.json")
}

/// Convenience function to create a configuration manager for common components with YAML.
///
/// # Arguments
///
/// * `component` - The component name
///
/// # Returns
///
/// Returns a configuration manager with a default YAML configuration file.
pub fn yaml_config_for_component(component: &str) -> Result<XdgConfig> {
    XdgConfig::new(component, "config.yaml")
}

/// Convenience function to create a configuration manager for common components with TOML.
///
/// # Arguments
///
/// * `component` - The component name
///
/// # Returns
///
/// Returns a configuration manager with a default TOML configuration file.
pub fn toml_config_for_component(component: &str) -> Result<XdgConfig> {
    XdgConfig::new(component, "config.toml")
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};

    use super::*;

    #[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
    struct TestConfig {
        name: String,
        value: i32,
        enabled: bool,
    }

    #[tokio::test]
    async fn test_config_creation() {
        let config = XdgConfig::new("test", "config.json").unwrap();
        assert_eq!(config.component(), "test");
        assert_eq!(config.default_filename(), "config.json");
    }

    #[tokio::test]
    async fn test_config_save_and_load() {
        let config_manager = XdgConfig::new("test", "config.json").unwrap();
        let test_config = TestConfig {
            name: "test".to_string(),
            value: 42,
            enabled: true,
        };

        // Save configuration
        let saved_path = config_manager.save(&test_config).await.unwrap();
        assert!(saved_path.exists());

        // Load configuration
        let loaded_config = config_manager.load::<TestConfig>().await.unwrap().unwrap();
        assert_eq!(loaded_config, test_config);

        // Clean up
        let _ = tokio::fs::remove_file(saved_path).await;
    }

    #[tokio::test]
    async fn test_config_load_nonexistent() {
        let config_manager = XdgConfig::new("test", "nonexistent.json").unwrap();
        let loaded_config = config_manager.load::<TestConfig>().await.unwrap();
        assert!(loaded_config.is_none());
    }

    #[tokio::test]
    async fn test_config_load_empty_file() {
        let config_manager = XdgConfig::new("test", "empty.json").unwrap();

        // Create an empty config file
        let config_path = config_manager.default_config_path().unwrap();
        tokio::fs::create_dir_all(config_path.parent().unwrap())
            .await
            .unwrap();
        tokio::fs::write(&config_path, "").await.unwrap();

        // Load configuration - should return None for empty files
        let loaded_config = config_manager.load::<TestConfig>().await.unwrap();
        assert!(loaded_config.is_none());

        // Clean up
        let _ = tokio::fs::remove_file(config_path).await;
    }

    #[test]
    fn test_convenience_functions() {
        let json_config = config_for_component("test").unwrap();
        assert_eq!(json_config.default_filename(), "config.json");

        let yaml_config = yaml_config_for_component("test").unwrap();
        assert_eq!(yaml_config.default_filename(), "config.yaml");

        let toml_config = toml_config_for_component("test").unwrap();
        assert_eq!(toml_config.default_filename(), "config.toml");
    }
}
