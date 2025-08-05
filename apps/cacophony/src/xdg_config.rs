use crate::config::CacophonyConfig;
use crate::error::{CacophonyError, Result};
use ligature_xdg::{XdgConfig, XdgPaths};
use std::path::PathBuf;

/// XDG-based configuration manager for Cacophony
pub struct CacophonyXdgConfig {
    xdg_config: XdgConfig,
    xdg_paths: XdgPaths,
}

impl CacophonyXdgConfig {
    /// Create a new XDG configuration manager for Cacophony
    pub async fn new() -> Result<Self> {
        let xdg_config = XdgConfig::new("cacophony", "config.toml")
            .map_err(|e| CacophonyError::Internal(format!("Failed to create XDG config: {}", e)))?;

        let xdg_paths = XdgPaths::new("cacophony")
            .map_err(|e| CacophonyError::Internal(format!("Failed to create XDG paths: {}", e)))?;

        Ok(Self {
            xdg_config,
            xdg_paths,
        })
    }

    /// Load the Cacophony configuration from XDG config directory
    pub async fn load_config(&self) -> Result<Option<CacophonyConfig>> {
        self.xdg_config
            .load()
            .await
            .map_err(|e| CacophonyError::Internal(format!("Failed to load XDG config: {}", e)))
    }

    /// Save the Cacophony configuration to XDG config directory
    pub async fn save_config(&self, config: &CacophonyConfig) -> Result<PathBuf> {
        self.xdg_config
            .save(config)
            .await
            .map_err(|e| CacophonyError::Internal(format!("Failed to save XDG config: {}", e)))
    }

    /// Get the XDG config directory path
    pub fn config_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .config_dir()
            .map_err(|e| CacophonyError::Internal(format!("Failed to get config directory: {}", e)))
    }

    /// Get the XDG data directory path
    pub fn data_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .data_dir()
            .map_err(|e| CacophonyError::Internal(format!("Failed to get data directory: {}", e)))
    }

    /// Get the XDG cache directory path
    pub fn cache_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .cache_dir()
            .map_err(|e| CacophonyError::Internal(format!("Failed to get cache directory: {}", e)))
    }

    /// Get the XDG state directory path
    pub fn state_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .state_dir()
            .map_err(|e| CacophonyError::Internal(format!("Failed to get state directory: {}", e)))
    }

    /// Ensure all XDG directories exist
    pub async fn ensure_directories(&self) -> Result<()> {
        self.xdg_paths
            .ensure_directories()
            .await
            .map_err(|e| CacophonyError::Internal(format!("Failed to ensure directories: {}", e)))
    }

    /// Find a configuration file in the XDG config directory
    pub fn find_config_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_config_file(filename)
            .map_err(|e| CacophonyError::Internal(format!("Failed to find config file: {}", e)))
    }

    /// Find a data file in the XDG data directory
    pub fn find_data_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_data_file(filename)
            .map_err(|e| CacophonyError::Internal(format!("Failed to find data file: {}", e)))
    }

    /// Get the default configuration file path
    pub fn default_config_path(&self) -> Result<PathBuf> {
        Ok(self.config_dir()?.join("config.toml"))
    }

    /// Get the projects directory path (for storing project configurations)
    pub fn projects_dir(&self) -> Result<PathBuf> {
        Ok(self.data_dir()?.join("projects"))
    }

    /// Get the plugins directory path
    pub fn plugins_dir(&self) -> Result<PathBuf> {
        Ok(self.data_dir()?.join("plugins"))
    }

    /// Get the cache directory for compiled artifacts
    pub fn artifacts_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("artifacts"))
    }

    /// Get the state directory for runtime state
    pub fn runtime_state_dir(&self) -> Result<PathBuf> {
        Ok(self.state_dir()?.join("runtime"))
    }
}

/// Convenience function to get XDG configuration for Cacophony
pub async fn xdg_config_for_cacophony() -> Result<CacophonyXdgConfig> {
    CacophonyXdgConfig::new().await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{CacophonyConfig, ProjectConfig};
    use std::collections::HashMap;

    #[tokio::test]
    async fn test_xdg_config_integration() {
        // Create XDG configuration manager
        let xdg_config = CacophonyXdgConfig::new().await.unwrap();

        // Ensure XDG directories exist
        xdg_config.ensure_directories().await.unwrap();

        // Verify directories exist
        assert!(xdg_config.config_dir().unwrap().exists());
        assert!(xdg_config.data_dir().unwrap().exists());
        assert!(xdg_config.cache_dir().unwrap().exists());
        assert!(xdg_config.state_dir().unwrap().exists());

        // Create a sample configuration
        let config = CacophonyConfig {
            project: ProjectConfig {
                name: "test-project".to_string(),
                version: "1.0.0".to_string(),
                description: Some("Test project for XDG integration".to_string()),
                authors: vec!["Test User".to_string()],
                repository: Some("https://github.com/test/project".to_string()),
                license: Some("MIT".to_string()),
            },
            environments: HashMap::new(),
            collections: HashMap::new(),
            plugins: Vec::new(),
            operations: HashMap::new(),
        };

        // Save configuration to XDG config directory
        let config_path = xdg_config.save_config(&config).await.unwrap();
        assert!(config_path.exists());

        // Load configuration back
        let loaded_config = xdg_config.load_config().await.unwrap();
        assert!(loaded_config.is_some());

        let loaded = loaded_config.unwrap();
        assert_eq!(loaded.project.name, "test-project");
        assert_eq!(loaded.project.version, "1.0.0");

        // Create and verify project-specific directories
        let projects_dir = xdg_config.projects_dir().unwrap();
        tokio::fs::create_dir_all(&projects_dir).await.unwrap();
        assert!(projects_dir.exists());

        let plugins_dir = xdg_config.plugins_dir().unwrap();
        tokio::fs::create_dir_all(&plugins_dir).await.unwrap();
        assert!(plugins_dir.exists());

        let artifacts_cache_dir = xdg_config.artifacts_cache_dir().unwrap();
        tokio::fs::create_dir_all(&artifacts_cache_dir)
            .await
            .unwrap();
        assert!(artifacts_cache_dir.exists());

        let runtime_state_dir = xdg_config.runtime_state_dir().unwrap();
        tokio::fs::create_dir_all(&runtime_state_dir).await.unwrap();
        assert!(runtime_state_dir.exists());
    }
}
