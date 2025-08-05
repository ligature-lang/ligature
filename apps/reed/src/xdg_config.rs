use ligature_xdg::{XdgConfig, XdgPaths};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CliXdgError {
    #[error("XDG configuration error: {0}")]
    XdgError(#[from] ligature_xdg::error::XdgError),
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    #[error("Internal error: {0}")]
    Internal(String),
}

pub type Result<T> = std::result::Result<T, CliXdgError>;

/// CLI-specific configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CliConfig {
    /// Logging configuration
    pub logging: LoggingConfig,
    /// Performance settings
    pub performance: PerformanceConfig,
    /// Default settings for operations
    pub defaults: DefaultsConfig,
    /// Cache settings
    pub cache: CacheConfig,
}

/// Logging configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    /// Log level (trace, debug, info, warn, error)
    pub level: String,
    /// Whether to log to file
    pub log_to_file: bool,
    /// Whether to log to console
    pub log_to_console: bool,
    /// Maximum log file size in bytes
    pub max_file_size: usize,
    /// Number of log files to keep
    pub max_files: usize,
    /// Whether to include timestamps
    pub include_timestamps: bool,
}

/// Performance configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Whether to enable parallel processing
    pub enable_parallel: bool,
    /// Number of worker threads for parallel operations
    pub worker_threads: usize,
    /// Whether to enable caching
    pub enable_caching: bool,
    /// Cache TTL in seconds
    pub cache_ttl_seconds: u64,
}

/// Default settings for operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefaultsConfig {
    /// Default output format (json, yaml, text)
    pub output_format: String,
    /// Whether to show verbose output by default
    pub verbose: bool,
    /// Whether to show progress bars by default
    pub show_progress: bool,
    /// Default timeout for operations in seconds
    pub timeout_seconds: u64,
}

/// Cache configuration
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

impl Default for CliConfig {
    fn default() -> Self {
        Self {
            logging: LoggingConfig {
                level: "info".to_string(),
                log_to_file: true,
                log_to_console: false,
                max_file_size: 10 * 1024 * 1024, // 10MB
                max_files: 5,
                include_timestamps: true,
            },
            performance: PerformanceConfig {
                enable_parallel: true,
                worker_threads: num_cpus::get(),
                enable_caching: true,
                cache_ttl_seconds: 3600, // 1 hour
            },
            defaults: DefaultsConfig {
                output_format: "text".to_string(),
                verbose: false,
                show_progress: true,
                timeout_seconds: 30,
            },
            cache: CacheConfig {
                enabled: true,
                max_size: 100 * 1024 * 1024, // 100MB
                max_age: 24 * 60 * 60,       // 24 hours
                auto_clean: true,
            },
        }
    }
}

/// XDG-based configuration manager for CLI
pub struct CliXdgConfig {
    xdg_config: XdgConfig,
    xdg_paths: XdgPaths,
}

#[allow(dead_code)]
impl CliXdgConfig {
    /// Create a new XDG configuration manager for CLI
    pub async fn new() -> Result<Self> {
        let xdg_config = XdgConfig::new("ligature-cli", "config.toml")
            .map_err(|e| CliXdgError::Internal(format!("Failed to create XDG config: {e}")))?;

        let xdg_paths = XdgPaths::new("ligature-cli")
            .map_err(|e| CliXdgError::Internal(format!("Failed to create XDG paths: {e}")))?;

        Ok(Self {
            xdg_config,
            xdg_paths,
        })
    }

    /// Load the CLI configuration from XDG config directory
    pub async fn load_config(&self) -> Result<Option<CliConfig>> {
        self.xdg_config
            .load()
            .await
            .map_err(|e| CliXdgError::Internal(format!("Failed to load XDG config: {e}")))
    }

    /// Save the CLI configuration to XDG config directory
    pub async fn save_config(&self, config: &CliConfig) -> Result<PathBuf> {
        self.xdg_config
            .save(config)
            .await
            .map_err(|e| CliXdgError::Internal(format!("Failed to save XDG config: {e}")))
    }

    /// Get the XDG config directory path
    pub fn config_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .config_dir()
            .map_err(|e| CliXdgError::Internal(format!("Failed to get config directory: {e}")))
    }

    /// Get the XDG data directory path
    pub fn data_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .data_dir()
            .map_err(|e| CliXdgError::Internal(format!("Failed to get data directory: {e}")))
    }

    /// Get the XDG cache directory path
    pub fn cache_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .cache_dir()
            .map_err(|e| CliXdgError::Internal(format!("Failed to get cache directory: {e}")))
    }

    /// Get the XDG state directory path
    pub fn state_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .state_dir()
            .map_err(|e| CliXdgError::Internal(format!("Failed to get state directory: {e}")))
    }

    /// Ensure all XDG directories exist
    pub async fn ensure_directories(&self) -> Result<()> {
        self.xdg_paths
            .ensure_directories()
            .await
            .map_err(|e| CliXdgError::Internal(format!("Failed to ensure directories: {e}")))
    }

    /// Get the compiled programs cache directory path
    pub fn compiled_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("compiled"))
    }

    /// Get the parsed AST cache directory path
    pub fn ast_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("ast"))
    }

    /// Get the log directory path
    pub fn log_dir(&self) -> Result<PathBuf> {
        Ok(self.data_dir()?.join("logs"))
    }

    /// Get the session state directory path
    pub fn session_state_dir(&self) -> Result<PathBuf> {
        Ok(self.state_dir()?.join("sessions"))
    }

    /// Get the temporary files directory path
    pub fn temp_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("temp"))
    }

    /// Get the default configuration file path
    pub fn default_config_path(&self) -> Result<PathBuf> {
        Ok(self.config_dir()?.join("config.toml"))
    }

    /// Find a configuration file in the XDG config directory
    pub fn find_config_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_config_file(filename)
            .map_err(|e| CliXdgError::Internal(format!("Failed to find config file: {e}")))
    }

    /// Find a data file in the XDG data directory
    pub fn find_data_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_data_file(filename)
            .map_err(|e| CliXdgError::Internal(format!("Failed to find data file: {e}")))
    }

    /// Get the log level from configuration
    pub async fn log_level(&self) -> Result<String> {
        if let Some(config) = self.load_config().await? {
            Ok(config.logging.level)
        } else {
            Ok("info".to_string())
        }
    }

    /// Get the output format from configuration
    pub async fn output_format(&self) -> Result<String> {
        if let Some(config) = self.load_config().await? {
            Ok(config.defaults.output_format)
        } else {
            Ok("text".to_string())
        }
    }

    /// Check if verbose output is enabled
    pub async fn verbose_enabled(&self) -> Result<bool> {
        if let Some(config) = self.load_config().await? {
            Ok(config.defaults.verbose)
        } else {
            Ok(false)
        }
    }

    /// Check if caching is enabled
    pub async fn cache_enabled(&self) -> Result<bool> {
        if let Some(config) = self.load_config().await? {
            Ok(config.cache.enabled)
        } else {
            Ok(true)
        }
    }

    /// Get the cache TTL from configuration
    pub async fn cache_ttl(&self) -> Result<u64> {
        if let Some(config) = self.load_config().await? {
            Ok(config.cache.max_age)
        } else {
            Ok(24 * 60 * 60) // 24 hours default
        }
    }
}

/// Convenience function to get XDG configuration for CLI
pub async fn xdg_config_for_cli() -> Result<CliXdgConfig> {
    CliXdgConfig::new().await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cli_xdg_config_integration() {
        // Create XDG configuration manager
        let xdg_config = CliXdgConfig::new().await.unwrap();

        // Ensure XDG directories exist
        xdg_config.ensure_directories().await.unwrap();

        // Verify directories exist
        assert!(xdg_config.config_dir().unwrap().exists());
        assert!(xdg_config.data_dir().unwrap().exists());
        assert!(xdg_config.cache_dir().unwrap().exists());
        assert!(xdg_config.state_dir().unwrap().exists());

        // Create a sample configuration
        let config = CliConfig::default();

        // Save configuration to XDG config directory
        let config_path = xdg_config.save_config(&config).await.unwrap();
        assert!(config_path.exists());

        // Load configuration back
        let loaded_config = xdg_config.load_config().await.unwrap();
        assert!(loaded_config.is_some());

        let loaded = loaded_config.unwrap();
        assert_eq!(loaded.logging.level, "info");
        assert_eq!(loaded.defaults.output_format, "text");
        assert!(loaded.cache.enabled);

        // Verify CLI-specific directories
        let compiled_cache_dir = xdg_config.compiled_cache_dir().unwrap();
        tokio::fs::create_dir_all(&compiled_cache_dir)
            .await
            .unwrap();
        assert!(compiled_cache_dir.exists());

        let ast_cache_dir = xdg_config.ast_cache_dir().unwrap();
        tokio::fs::create_dir_all(&ast_cache_dir).await.unwrap();
        assert!(ast_cache_dir.exists());

        let log_dir = xdg_config.log_dir().unwrap();
        tokio::fs::create_dir_all(&log_dir).await.unwrap();
        assert!(log_dir.exists());

        let session_state_dir = xdg_config.session_state_dir().unwrap();
        tokio::fs::create_dir_all(&session_state_dir).await.unwrap();
        assert!(session_state_dir.exists());

        let temp_dir = xdg_config.temp_dir().unwrap();
        tokio::fs::create_dir_all(&temp_dir).await.unwrap();
        assert!(temp_dir.exists());

        // Test configuration getters
        let log_level = xdg_config.log_level().await.unwrap();
        assert_eq!(log_level, "info");

        let output_format = xdg_config.output_format().await.unwrap();
        assert_eq!(output_format, "text");

        let verbose = xdg_config.verbose_enabled().await.unwrap();
        assert!(!verbose);

        let cache_enabled = xdg_config.cache_enabled().await.unwrap();
        assert!(cache_enabled);

        let cache_ttl = xdg_config.cache_ttl().await.unwrap();
        assert_eq!(cache_ttl, 24 * 60 * 60); // 24 hours
    }
}
