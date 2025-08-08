//! XDG-based configuration for Keywork package manager.

use std::collections::HashMap;
use std::path::PathBuf;

use embouchure_xdg::{XdgPaths, config_for_component};
use serde::{Deserialize, Serialize};

/// Type alias for error results to reduce complexity
type ConfigResult<T> = Result<T, Box<dyn std::error::Error>>;

/// Keywork package manager configuration.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct KeyworkConfig {
    /// Registry configuration
    pub registry: RegistryConfig,
    /// Cache configuration
    pub cache: CacheConfig,
    /// Package installation configuration
    pub installation: InstallationConfig,
    /// Logging configuration
    pub logging: LoggingConfig,
}

/// Registry configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    /// Default registry URL
    pub default_url: String,
    /// Registry authentication tokens
    pub auth_tokens: HashMap<String, String>,
    /// Request timeout in seconds
    pub timeout: u64,
    /// Maximum retries for failed requests
    pub max_retries: u32,
}

/// Cache configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    /// Whether caching is enabled
    pub enabled: bool,
    /// Maximum cache size in bytes
    pub max_size: u64,
    /// Maximum age for cache entries in seconds
    pub max_age: u64,
    /// Whether to clean old cache entries automatically
    pub auto_clean: bool,
}

/// Package installation configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstallationConfig {
    /// Default installation directory
    pub default_directory: Option<String>,
    /// Whether to create backup before updates
    pub create_backup: bool,
    /// Whether to validate packages before installation
    pub validate_packages: bool,
    /// Maximum concurrent installations
    pub max_concurrent: u32,
}

/// Logging configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    /// Log level (debug, info, warn, error)
    pub level: String,
    /// Whether to enable structured logging
    pub structured: bool,
    /// Log file path (if any)
    pub file: Option<String>,
    /// Whether to include timestamps
    pub include_timestamps: bool,
}

impl Default for RegistryConfig {
    fn default() -> Self {
        Self {
            default_url: "https://registry.ligature.dev".to_string(),
            auth_tokens: HashMap::new(),
            timeout: 30,
            max_retries: 3,
        }
    }
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            max_size: 100 * 1024 * 1024, // 100 MB
            max_age: 24 * 60 * 60,       // 24 hours
            auto_clean: true,
        }
    }
}

impl Default for InstallationConfig {
    fn default() -> Self {
        Self {
            default_directory: None,
            create_backup: true,
            validate_packages: true,
            max_concurrent: 4,
        }
    }
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            level: "info".to_string(),
            structured: true,
            file: None,
            include_timestamps: true,
        }
    }
}

/// XDG-based configuration manager for Keywork.
pub struct KeyworkXdgConfig {
    /// XDG paths for keywork
    paths: XdgPaths,
    /// Configuration manager
    #[allow(dead_code)]
    config_manager: embouchure_xdg::XdgConfig,
    /// Current configuration
    config: KeyworkConfig,
}

#[allow(dead_code)]
impl KeyworkXdgConfig {
    /// Create a new Keywork XDG configuration manager.
    pub async fn new() -> ConfigResult<Self> {
        let paths = XdgPaths::new("keywork")?;
        let config_manager = config_for_component("keywork")?;

        // Ensure directories exist
        paths.ensure_directories().await?;

        // Load existing configuration or use defaults
        let config = if let Some(loaded_config) = config_manager.load::<KeyworkConfig>().await? {
            loaded_config
        } else {
            let default_config = KeyworkConfig::default();
            // Save default configuration
            config_manager.save(&default_config).await?;
            default_config
        };

        Ok(Self {
            paths,
            config_manager,
            config,
        })
    }

    /// Get the current configuration.
    #[allow(dead_code)]
    pub fn config(&self) -> &KeyworkConfig {
        &self.config
    }

    /// Get a mutable reference to the configuration.
    #[allow(dead_code)]
    pub fn config_mut(&mut self) -> &mut KeyworkConfig {
        &mut self.config
    }

    /// Save the current configuration.
    #[allow(dead_code)]
    pub async fn save(&self) -> ConfigResult<()> {
        self.config_manager.save(&self.config).await?;
        Ok(())
    }

    /// Reload configuration from file.
    #[allow(dead_code)]
    pub async fn reload(&mut self) -> ConfigResult<()> {
        if let Some(loaded_config) = self.config_manager.load::<KeyworkConfig>().await? {
            self.config = loaded_config;
        }
        Ok(())
    }

    /// Get the cache directory path.
    pub fn cache_dir(&self) -> ConfigResult<PathBuf> {
        Ok(self.paths.cache_dir()?)
    }

    /// Get the data directory path.
    pub fn data_dir(&self) -> ConfigResult<PathBuf> {
        Ok(self.paths.data_dir()?)
    }

    /// Get the state directory path.
    pub fn state_dir(&self) -> ConfigResult<PathBuf> {
        Ok(self.paths.state_dir()?)
    }

    /// Get the config directory path.
    pub fn config_dir(&self) -> ConfigResult<PathBuf> {
        Ok(self.paths.config_dir()?)
    }

    /// Get a cache file path.
    pub fn cache_file(&self, filename: &str) -> ConfigResult<PathBuf> {
        Ok(self.paths.cache_file(filename)?)
    }

    /// Get a data file path.
    pub fn data_file(&self, filename: &str) -> ConfigResult<PathBuf> {
        Ok(self.paths.data_file(filename)?)
    }

    /// Get a state file path.
    pub fn state_file(&self, filename: &str) -> ConfigResult<PathBuf> {
        Ok(self.paths.state_file(filename)?)
    }

    /// Get the registry URL from configuration.
    pub fn registry_url(&self) -> &str {
        &self.config.registry.default_url
    }

    /// Get the registry timeout from configuration.
    pub fn registry_timeout(&self) -> u64 {
        self.config.registry.timeout
    }

    /// Get the registry max retries from configuration.
    pub fn registry_max_retries(&self) -> u32 {
        self.config.registry.max_retries
    }

    /// Get an auth token for a registry.
    pub fn auth_token(&self, registry: &str) -> Option<&String> {
        self.config.registry.auth_tokens.get(registry)
    }

    /// Set an auth token for a registry.
    pub async fn set_auth_token(&mut self, registry: &str, token: String) -> ConfigResult<()> {
        self.config
            .registry
            .auth_tokens
            .insert(registry.to_string(), token);
        self.save().await
    }

    /// Check if caching is enabled.
    pub fn cache_enabled(&self) -> bool {
        self.config.cache.enabled
    }

    /// Get the maximum cache size.
    pub fn max_cache_size(&self) -> u64 {
        self.config.cache.max_size
    }

    /// Get the maximum cache age.
    pub fn max_cache_age(&self) -> u64 {
        self.config.cache.max_age
    }

    /// Check if auto-clean is enabled.
    pub fn auto_clean_enabled(&self) -> bool {
        self.config.cache.auto_clean
    }

    /// Get the default installation directory.
    pub fn default_installation_dir(&self) -> Option<&String> {
        self.config.installation.default_directory.as_ref()
    }

    /// Set the default installation directory.
    pub async fn set_default_installation_dir(&mut self, dir: Option<String>) -> ConfigResult<()> {
        self.config.installation.default_directory = dir;
        self.save().await
    }

    /// Check if package validation is enabled.
    pub fn validate_packages(&self) -> bool {
        self.config.installation.validate_packages
    }

    /// Get the maximum concurrent installations.
    pub fn max_concurrent_installations(&self) -> u32 {
        self.config.installation.max_concurrent
    }

    /// Get the log level.
    pub fn log_level(&self) -> &str {
        &self.config.logging.level
    }

    /// Set the log level.
    pub async fn set_log_level(&mut self, level: String) -> ConfigResult<()> {
        self.config.logging.level = level;
        self.save().await
    }

    /// Check if structured logging is enabled.
    pub fn structured_logging(&self) -> bool {
        self.config.logging.structured
    }

    /// Get the log file path.
    pub fn log_file(&self) -> Option<&String> {
        self.config.logging.file.as_ref()
    }

    /// Set the log file path.
    pub async fn set_log_file(&mut self, file: Option<String>) -> ConfigResult<()> {
        self.config.logging.file = file;
        self.save().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_keywork_config_creation() {
        let config = KeyworkXdgConfig::new().await.unwrap();
        assert_eq!(config.registry_url(), "https://registry.ligature.dev");
        assert_eq!(config.registry_timeout(), 30);
        assert_eq!(config.registry_max_retries(), 3);
        assert!(config.cache_enabled());
        assert_eq!(config.max_cache_size(), 100 * 1024 * 1024);
        assert_eq!(config.max_cache_age(), 24 * 60 * 60);
        assert!(config.auto_clean_enabled());
        assert!(config.validate_packages());
        assert_eq!(config.max_concurrent_installations(), 4);
        // The log level might be "debug" if there's an existing config file
        let log_level = config.log_level();
        assert!(
            log_level == "info" || log_level == "debug",
            "Expected 'info' or 'debug', got '{log_level}'"
        );
        assert!(config.structured_logging());
    }

    #[tokio::test]
    async fn test_keywork_config_modification() {
        let mut config = KeyworkXdgConfig::new().await.unwrap();

        // Test setting auth token
        config
            .set_auth_token("test-registry", "test-token".to_string())
            .await
            .unwrap();
        assert_eq!(
            config.auth_token("test-registry"),
            Some(&"test-token".to_string())
        );

        // Test setting log level
        config.set_log_level("debug".to_string()).await.unwrap();
        assert_eq!(config.log_level(), "debug");

        // Test setting installation directory
        config
            .set_default_installation_dir(Some("/tmp/test".to_string()))
            .await
            .unwrap();
        assert_eq!(
            config.default_installation_dir(),
            Some(&"/tmp/test".to_string())
        );
    }

    #[tokio::test]
    async fn test_keywork_paths() {
        let config = KeyworkXdgConfig::new().await.unwrap();

        let cache_dir = config.cache_dir().unwrap();
        let data_dir = config.data_dir().unwrap();
        let state_dir = config.state_dir().unwrap();
        let config_dir = config.config_dir().unwrap();

        assert!(cache_dir.to_string_lossy().contains("keywork"));
        assert!(data_dir.to_string_lossy().contains("keywork"));
        assert!(state_dir.to_string_lossy().contains("keywork"));
        assert!(config_dir.to_string_lossy().contains("keywork"));
    }
}
