//! Configuration management for Krox.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::{Error, Result};

/// Global configuration for Krox.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalConfig {
    /// Default execution mode.
    pub default_execution_mode: crate::ExecutionMode,
    /// Default cache settings.
    pub cache: CacheConfig,
    /// HTTP client settings.
    pub http: HttpConfig,
    /// Native execution settings.
    pub native: NativeConfig,
    /// Logging settings.
    pub logging: LoggingConfig,
    /// Environment-specific overrides.
    pub environments: HashMap<String, EnvironmentConfig>,
}

/// Cache configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    /// Whether caching is enabled by default.
    pub enabled: bool,
    /// Default cache directory.
    pub directory: Option<String>,
    /// Maximum age for cache entries (in seconds).
    pub max_age: u64,
    /// Maximum cache size (in bytes).
    pub max_size: u64,
}

/// HTTP client configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpConfig {
    /// Default timeout for HTTP requests (in seconds).
    pub timeout: u64,
    /// Default HTTP endpoint.
    pub endpoint: Option<String>,
    /// HTTP headers to include in requests.
    pub headers: HashMap<String, String>,
    /// Retry configuration.
    pub retry: RetryConfig,
}

/// Retry configuration for HTTP requests.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// Maximum number of retries.
    pub max_retries: u32,
    /// Base delay between retries (in milliseconds).
    pub base_delay: u64,
    /// Maximum delay between retries (in milliseconds).
    pub max_delay: u64,
}

/// Native execution configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NativeConfig {
    /// Path to ligature-cli binary.
    pub cli_path: Option<String>,
    /// Default timeout for CLI execution (in seconds).
    pub timeout: u64,
    /// Environment variables to pass to CLI.
    pub env_vars: HashMap<String, String>,
}

/// Logging configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    /// Log level.
    pub level: String,
    /// Whether to enable structured logging.
    pub structured: bool,
    /// Log file path (if any).
    pub file: Option<String>,
}

/// Environment-specific configuration.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct EnvironmentConfig {
    /// Execution mode override.
    pub execution_mode: Option<crate::ExecutionMode>,
    /// HTTP endpoint override.
    pub http_endpoint: Option<String>,
    /// Cache directory override.
    pub cache_directory: Option<String>,
    /// Additional environment variables.
    pub env_vars: HashMap<String, String>,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            default_execution_mode: crate::ExecutionMode::Native,
            cache: CacheConfig::default(),
            http: HttpConfig::default(),
            native: NativeConfig::default(),
            logging: LoggingConfig::default(),
            environments: HashMap::new(),
        }
    }
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            directory: None,
            max_age: 3600,               // 1 hour
            max_size: 100 * 1024 * 1024, // 100 MB
        }
    }
}

impl Default for HttpConfig {
    fn default() -> Self {
        Self {
            timeout: 30,
            endpoint: None,
            headers: HashMap::new(),
            retry: RetryConfig::default(),
        }
    }
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            base_delay: 1000, // 1 second
            max_delay: 10000, // 10 seconds
        }
    }
}

impl Default for NativeConfig {
    fn default() -> Self {
        Self {
            cli_path: None,
            timeout: 30,
            env_vars: HashMap::new(),
        }
    }
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            level: "info".to_string(),
            structured: true,
            file: None,
        }
    }
}

impl GlobalConfig {
    /// Load configuration from a file.
    pub async fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        let content = tokio::fs::read_to_string(path).await.map_err(|e| {
            Error::file_system(
                format!("Failed to read config file: {e}"),
                Some(path.to_string_lossy().to_string()),
            )
        })?;

        let config: GlobalConfig = if path.extension().and_then(|s| s.to_str()) == Some("json") {
            serde_json::from_str(&content).map_err(Error::JsonSerialization)?
        } else {
            serde_yaml::from_str(&content).map_err(Error::YamlSerialization)?
        };

        Ok(config)
    }

    /// Save configuration to a file.
    pub async fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let content = if path.extension().and_then(|s| s.to_str()) == Some("json") {
            serde_json::to_string_pretty(self).map_err(Error::JsonSerialization)?
        } else {
            serde_yaml::to_string(self).map_err(Error::YamlSerialization)?
        };

        tokio::fs::write(path, content).await.map_err(|e| {
            Error::file_system(
                format!("Failed to write config file: {e}"),
                Some(path.to_string_lossy().to_string()),
            )
        })?;

        Ok(())
    }

    /// Get configuration for a specific environment.
    pub fn for_environment(&self, env: &str) -> EnvironmentConfig {
        self.environments.get(env).cloned().unwrap_or_default()
    }

    /// Merge with another configuration.
    pub fn merge(&mut self, other: &GlobalConfig) {
        // Merge cache config
        if other.cache.enabled != self.cache.enabled {
            self.cache.enabled = other.cache.enabled;
        }
        if other.cache.directory.is_some() {
            self.cache.directory = other.cache.directory.clone();
        }
        if other.cache.max_age != self.cache.max_age {
            self.cache.max_age = other.cache.max_age;
        }
        if other.cache.max_size != self.cache.max_size {
            self.cache.max_size = other.cache.max_size;
        }

        // Merge HTTP config
        if other.http.timeout != self.http.timeout {
            self.http.timeout = other.http.timeout;
        }
        if other.http.endpoint.is_some() {
            self.http.endpoint = other.http.endpoint.clone();
        }
        for (key, value) in &other.http.headers {
            self.http.headers.insert(key.clone(), value.clone());
        }

        // Merge native config
        if other.native.cli_path.is_some() {
            self.native.cli_path = other.native.cli_path.clone();
        }
        if other.native.timeout != self.native.timeout {
            self.native.timeout = other.native.timeout;
        }
        for (key, value) in &other.native.env_vars {
            self.native.env_vars.insert(key.clone(), value.clone());
        }

        // Merge logging config
        if other.logging.level != self.logging.level {
            self.logging.level = other.logging.level.clone();
        }
        if other.logging.structured != self.logging.structured {
            self.logging.structured = other.logging.structured;
        }
        if other.logging.file.is_some() {
            self.logging.file = other.logging.file.clone();
        }

        // Merge environments
        for (env, config) in &other.environments {
            self.environments.insert(env.clone(), config.clone());
        }
    }
}

/// Configuration manager for Krox.
pub struct ConfigManager {
    config: GlobalConfig,
    config_path: Option<PathBuf>,
}

impl ConfigManager {
    /// Create a new configuration manager.
    pub fn new() -> Self {
        Self {
            config: GlobalConfig::default(),
            config_path: None,
        }
    }

    /// Create a configuration manager with a config file.
    pub async fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        let config = GlobalConfig::from_file(path).await?;

        Ok(Self {
            config,
            config_path: Some(path.to_path_buf()),
        })
    }

    /// Get the current configuration.
    pub fn config(&self) -> &GlobalConfig {
        &self.config
    }

    /// Get a mutable reference to the configuration.
    pub fn config_mut(&mut self) -> &mut GlobalConfig {
        &mut self.config
    }

    /// Save the current configuration.
    pub async fn save(&self) -> Result<()> {
        if let Some(ref path) = self.config_path {
            self.config.save_to_file(path).await?;
        }
        Ok(())
    }

    /// Save configuration to a specific file.
    pub async fn save_to<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.config.save_to_file(path).await
    }

    /// Reload configuration from file.
    pub async fn reload(&mut self) -> Result<()> {
        if let Some(ref path) = self.config_path {
            self.config = GlobalConfig::from_file(path).await?;
        }
        Ok(())
    }
}

impl Default for ConfigManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[tokio::test]
    async fn test_config_creation() {
        let config = GlobalConfig::default();
        assert_eq!(config.default_execution_mode, crate::ExecutionMode::Native);
        assert!(config.cache.enabled);
    }

    #[tokio::test]
    async fn test_config_serialization() {
        let config = GlobalConfig::default();
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("config.yaml");

        config.save_to_file(&config_path).await.unwrap();
        let loaded_config = GlobalConfig::from_file(&config_path).await.unwrap();

        assert_eq!(
            config.default_execution_mode,
            loaded_config.default_execution_mode
        );
        assert_eq!(config.cache.enabled, loaded_config.cache.enabled);
    }

    #[tokio::test]
    async fn test_config_manager() {
        let manager = ConfigManager::new();
        assert_eq!(
            manager.config().default_execution_mode,
            crate::ExecutionMode::Native
        );
    }
}
