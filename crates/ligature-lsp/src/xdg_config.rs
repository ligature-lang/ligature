use ligature_xdg::{XdgConfig, XdgPaths};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LspXdgError {
    #[error("XDG configuration error: {0}")]
    XdgError(#[from] ligature_xdg::error::XdgError),
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    #[error("Internal error: {0}")]
    Internal(String),
}

pub type Result<T> = std::result::Result<T, LspXdgError>;

/// LSP-specific configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspConfig {
    /// Whether to enable workspace-wide diagnostics
    pub enable_workspace_diagnostics: bool,
    /// Whether to enable cross-file symbol resolution
    pub enable_cross_file_symbols: bool,
    /// Maximum number of files to scan for workspace symbols
    pub max_workspace_files: usize,
    /// File patterns to include in workspace operations
    pub include_patterns: Vec<String>,
    /// File patterns to exclude from workspace operations
    pub exclude_patterns: Vec<String>,
    /// Logging configuration
    pub logging: LoggingConfig,
    /// Performance settings
    pub performance: PerformanceConfig,
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
}

/// Performance configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Maximum number of cached documents
    pub max_cached_documents: usize,
    /// Cache TTL in seconds
    pub cache_ttl_seconds: u64,
    /// Whether to enable incremental parsing
    pub enable_incremental_parsing: bool,
    /// Whether to enable background indexing
    pub enable_background_indexing: bool,
}

impl Default for LspConfig {
    fn default() -> Self {
        Self {
            enable_workspace_diagnostics: true,
            enable_cross_file_symbols: true,
            max_workspace_files: 1000,
            include_patterns: vec!["**/*.lig".to_string()],
            exclude_patterns: vec![
                "**/target/**".to_string(),
                "**/node_modules/**".to_string(),
                "**/.git/**".to_string(),
            ],
            logging: LoggingConfig {
                level: "info".to_string(),
                log_to_file: true,
                log_to_console: false,
                max_file_size: 10 * 1024 * 1024, // 10MB
                max_files: 5,
            },
            performance: PerformanceConfig {
                max_cached_documents: 100,
                cache_ttl_seconds: 3600, // 1 hour
                enable_incremental_parsing: true,
                enable_background_indexing: true,
            },
        }
    }
}

/// XDG-based configuration manager for LSP
pub struct LspXdgConfig {
    xdg_config: XdgConfig,
    xdg_paths: XdgPaths,
}

impl LspXdgConfig {
    /// Create a new XDG configuration manager for LSP
    pub async fn new() -> Result<Self> {
        let xdg_config = XdgConfig::new("ligature-lsp", "config.toml")
            .map_err(|e| LspXdgError::Internal(format!("Failed to create XDG config: {e}")))?;

        let xdg_paths = XdgPaths::new("ligature-lsp")
            .map_err(|e| LspXdgError::Internal(format!("Failed to create XDG paths: {e}")))?;

        Ok(Self {
            xdg_config,
            xdg_paths,
        })
    }

    /// Load the LSP configuration from XDG config directory
    pub async fn load_config(&self) -> Result<Option<LspConfig>> {
        self.xdg_config
            .load()
            .await
            .map_err(|e| LspXdgError::Internal(format!("Failed to load XDG config: {e}")))
    }

    /// Save the LSP configuration to XDG config directory
    pub async fn save_config(&self, config: &LspConfig) -> Result<PathBuf> {
        self.xdg_config
            .save(config)
            .await
            .map_err(|e| LspXdgError::Internal(format!("Failed to save XDG config: {e}")))
    }

    /// Get the XDG config directory path
    pub fn config_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .config_dir()
            .map_err(|e| LspXdgError::Internal(format!("Failed to get config directory: {e}")))
    }

    /// Get the XDG data directory path
    pub fn data_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .data_dir()
            .map_err(|e| LspXdgError::Internal(format!("Failed to get data directory: {e}")))
    }

    /// Get the XDG cache directory path
    pub fn cache_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .cache_dir()
            .map_err(|e| LspXdgError::Internal(format!("Failed to get cache directory: {e}")))
    }

    /// Get the XDG state directory path
    pub fn state_dir(&self) -> Result<PathBuf> {
        self.xdg_paths
            .state_dir()
            .map_err(|e| LspXdgError::Internal(format!("Failed to get state directory: {e}")))
    }

    /// Ensure all XDG directories exist
    pub async fn ensure_directories(&self) -> Result<()> {
        self.xdg_paths
            .ensure_directories()
            .await
            .map_err(|e| LspXdgError::Internal(format!("Failed to ensure directories: {e}")))
    }

    /// Get the workspace cache directory path
    pub fn workspace_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("workspaces"))
    }

    /// Get the symbol cache directory path
    pub fn symbol_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("symbols"))
    }

    /// Get the module cache directory path
    pub fn module_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("modules"))
    }

    /// Get the log directory path
    pub fn log_dir(&self) -> Result<PathBuf> {
        Ok(self.data_dir()?.join("logs"))
    }

    /// Get the workspace state directory path
    pub fn workspace_state_dir(&self) -> Result<PathBuf> {
        Ok(self.state_dir()?.join("workspaces"))
    }

    /// Get the session state directory path
    pub fn session_state_dir(&self) -> Result<PathBuf> {
        Ok(self.state_dir()?.join("sessions"))
    }

    /// Get the default configuration file path
    pub fn default_config_path(&self) -> Result<PathBuf> {
        Ok(self.config_dir()?.join("config.toml"))
    }

    /// Find a configuration file in the XDG config directory
    pub fn find_config_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_config_file(filename)
            .map_err(|e| LspXdgError::Internal(format!("Failed to find config file: {e}")))
    }

    /// Find a data file in the XDG data directory
    pub fn find_data_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        self.xdg_paths
            .find_data_file(filename)
            .map_err(|e| LspXdgError::Internal(format!("Failed to find data file: {e}")))
    }
}

/// Convenience function to get XDG configuration for LSP
pub async fn xdg_config_for_lsp() -> Result<LspXdgConfig> {
    LspXdgConfig::new().await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_lsp_xdg_config_integration() {
        // Create XDG configuration manager
        let xdg_config = LspXdgConfig::new().await.unwrap();

        // Ensure XDG directories exist
        xdg_config.ensure_directories().await.unwrap();

        // Verify directories exist
        assert!(xdg_config.config_dir().unwrap().exists());
        assert!(xdg_config.data_dir().unwrap().exists());
        assert!(xdg_config.cache_dir().unwrap().exists());
        assert!(xdg_config.state_dir().unwrap().exists());

        // Create a sample configuration
        let config = LspConfig::default();

        // Save configuration to XDG config directory
        let config_path = xdg_config.save_config(&config).await.unwrap();
        assert!(config_path.exists());

        // Load configuration back
        let loaded_config = xdg_config.load_config().await.unwrap();
        assert!(loaded_config.is_some());

        let loaded = loaded_config.unwrap();
        assert_eq!(loaded.enable_workspace_diagnostics, true);
        assert_eq!(loaded.max_workspace_files, 1000);
        assert!(loaded.include_patterns.contains(&"**/*.lig".to_string()));

        // Verify LSP-specific directories
        let workspace_cache_dir = xdg_config.workspace_cache_dir().unwrap();
        tokio::fs::create_dir_all(&workspace_cache_dir)
            .await
            .unwrap();
        assert!(workspace_cache_dir.exists());

        let symbol_cache_dir = xdg_config.symbol_cache_dir().unwrap();
        tokio::fs::create_dir_all(&symbol_cache_dir).await.unwrap();
        assert!(symbol_cache_dir.exists());

        let module_cache_dir = xdg_config.module_cache_dir().unwrap();
        tokio::fs::create_dir_all(&module_cache_dir).await.unwrap();
        assert!(module_cache_dir.exists());

        let log_dir = xdg_config.log_dir().unwrap();
        tokio::fs::create_dir_all(&log_dir).await.unwrap();
        assert!(log_dir.exists());

        let workspace_state_dir = xdg_config.workspace_state_dir().unwrap();
        tokio::fs::create_dir_all(&workspace_state_dir)
            .await
            .unwrap();
        assert!(workspace_state_dir.exists());

        let session_state_dir = xdg_config.session_state_dir().unwrap();
        tokio::fs::create_dir_all(&session_state_dir).await.unwrap();
        assert!(session_state_dir.exists());
    }
}
