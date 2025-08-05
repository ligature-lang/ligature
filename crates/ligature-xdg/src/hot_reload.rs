use crate::validation::ConfigValidator;
use notify::{RecommendedWatcher, RecursiveMode, Watcher};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use thiserror::Error;
use tokio::sync::mpsc;

#[derive(Error, Debug)]
pub enum HotReloadError {
    #[error("File system error: {0}")]
    FileSystemError(#[from] notify::Error),
    #[error("Configuration validation error: {0}")]
    ValidationError(String),
    #[error("Configuration parsing error: {0}")]
    ParsingError(String),
    #[error("Timeout waiting for configuration reload")]
    Timeout,
    #[error("Configuration file not found: {path}")]
    FileNotFound { path: PathBuf },
    #[error("Watcher already running")]
    WatcherAlreadyRunning,
    #[error("Watcher not running")]
    WatcherNotRunning,
}

pub type HotReloadResult<T> = std::result::Result<T, HotReloadError>;

/// Configuration change event
#[derive(Debug, Clone)]
pub enum ConfigChangeEvent {
    /// Configuration file was created
    Created(PathBuf),
    /// Configuration file was modified
    Modified(PathBuf),
    /// Configuration file was deleted
    Deleted(PathBuf),
    /// Configuration file was renamed
    Renamed { from: PathBuf, to: PathBuf },
}

/// Configuration reload callback
pub type ConfigReloadCallback =
    Box<dyn Fn(ConfigChangeEvent, serde_json::Value) -> Result<(), String> + Send + Sync>;

/// Type alias for config reload callbacks
type ConfigReloadCallbackMap = Arc<Mutex<HashMap<String, ConfigReloadCallback>>>;

/// Type alias for config cache
type ConfigCacheMap = Arc<Mutex<HashMap<PathBuf, serde_json::Value>>>;

/// Hot reload configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HotReloadConfig {
    /// Whether hot reloading is enabled
    pub enabled: bool,
    /// Debounce time in milliseconds
    pub debounce_ms: u64,
    /// Whether to watch subdirectories recursively
    pub recursive: bool,
    /// File extensions to watch
    pub watch_extensions: Vec<String>,
    /// Directories to exclude from watching
    pub exclude_directories: Vec<String>,
    /// Maximum number of retries on validation failure
    pub max_retries: u32,
    /// Retry delay in milliseconds
    pub retry_delay_ms: u64,
}

impl Default for HotReloadConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            debounce_ms: 500,
            recursive: true,
            watch_extensions: vec![
                "toml".to_string(),
                "json".to_string(),
                "yaml".to_string(),
                "yml".to_string(),
            ],
            exclude_directories: vec![
                ".git".to_string(),
                "target".to_string(),
                "node_modules".to_string(),
                ".vscode".to_string(),
            ],
            max_retries: 3,
            retry_delay_ms: 1000,
        }
    }
}

/// Configuration hot reload manager
pub struct ConfigHotReloader {
    config: HotReloadConfig,
    validator: Arc<ConfigValidator>,
    watcher: Option<RecommendedWatcher>,
    callbacks: ConfigReloadCallbackMap,
    config_cache: ConfigCacheMap,
    event_sender: Option<mpsc::Sender<ConfigChangeEvent>>,
    event_receiver: Option<mpsc::Receiver<ConfigChangeEvent>>,
    running: Arc<Mutex<bool>>,
}

impl ConfigHotReloader {
    /// Create a new configuration hot reloader
    pub fn new(config: HotReloadConfig, validator: ConfigValidator) -> Self {
        let (event_sender, event_receiver) = mpsc::channel(100);

        Self {
            config,
            validator: Arc::new(validator),
            watcher: None,
            callbacks: Arc::new(Mutex::new(HashMap::new())),
            config_cache: Arc::new(Mutex::new(HashMap::new())),
            event_sender: Some(event_sender),
            event_receiver: Some(event_receiver),
            running: Arc::new(Mutex::new(false)),
        }
    }

    /// Start watching configuration files
    pub async fn start_watching(&mut self, config_dir: &Path) -> HotReloadResult<()> {
        if *self.running.lock().unwrap() {
            return Err(HotReloadError::WatcherAlreadyRunning);
        }

        if !config_dir.exists() {
            return Err(HotReloadError::FileNotFound {
                path: config_dir.to_path_buf(),
            });
        }

        // Create file system watcher
        let (tx, rx) = std::sync::mpsc::channel();
        let mut watcher = RecommendedWatcher::new(tx, notify::Config::default())?;

        // Store the receiver for processing events
        let event_sender = self.event_sender.clone();
        let _validator = Arc::clone(&self.validator);
        let config = self.config.clone();

        // Spawn a thread to process events
        std::thread::spawn(move || {
            for res in rx {
                match res {
                    Ok(event) => {
                        // Handle file system events
                        if let Some(sender) = &event_sender {
                            if let Ok(event) = Self::convert_notify_event_static(event, &config) {
                                let _ = sender.blocking_send(event);
                            }
                        }
                    }
                    Err(e) => eprintln!("Watch error: {e:?}"),
                }
            }
        });

        // Watch the configuration directory
        watcher.watch(config_dir, RecursiveMode::Recursive)?;

        self.watcher = Some(watcher);
        *self.running.lock().unwrap() = true;

        // Start the event processing loop
        self.start_event_loop().await;

        Ok(())
    }

    /// Stop watching configuration files
    pub fn stop_watching(&mut self) -> HotReloadResult<()> {
        if !*self.running.lock().unwrap() {
            return Err(HotReloadError::WatcherNotRunning);
        }

        self.watcher = None;
        *self.running.lock().unwrap() = false;

        Ok(())
    }

    /// Register a callback for configuration changes
    pub fn register_callback(
        &self,
        name: &str,
        callback: ConfigReloadCallback,
    ) -> HotReloadResult<()> {
        let mut callbacks = self.callbacks.lock().unwrap();
        callbacks.insert(name.to_string(), callback);
        Ok(())
    }

    /// Unregister a callback
    pub fn unregister_callback(&self, name: &str) -> HotReloadResult<()> {
        let mut callbacks = self.callbacks.lock().unwrap();
        callbacks.remove(name);
        Ok(())
    }

    /// Load and validate a configuration file
    pub async fn load_config_file(&self, path: &Path) -> HotReloadResult<serde_json::Value> {
        if !path.exists() {
            return Err(HotReloadError::FileNotFound {
                path: path.to_path_buf(),
            });
        }

        let content = tokio::fs::read_to_string(path)
            .await
            .map_err(|e| HotReloadError::FileSystemError(notify::Error::io(e)))?;

        // Parse configuration based on file extension
        let config = self.parse_config_file(&content, path)?;

        // Validate configuration
        self.validate_config(&config, path)?;

        // Cache the configuration
        let mut cache = self.config_cache.lock().unwrap();
        cache.insert(path.to_path_buf(), config.clone());

        Ok(config)
    }

    /// Get cached configuration for a file
    pub fn get_cached_config(&self, path: &Path) -> Option<serde_json::Value> {
        let cache = self.config_cache.lock().unwrap();
        cache.get(path).cloned()
    }

    /// Clear configuration cache
    pub fn clear_cache(&self) {
        let mut cache = self.config_cache.lock().unwrap();
        cache.clear();
    }

    /// Check if a file should be watched (static version)
    fn should_watch_file_static(path: &Path, config: &HotReloadConfig) -> bool {
        // Check file extension
        if let Some(extension) = path.extension() {
            if let Some(ext_str) = extension.to_str() {
                if !config.watch_extensions.contains(&ext_str.to_lowercase()) {
                    return false;
                }
            }
        }

        // Check if file is in excluded directory
        for component in path.components() {
            if let std::path::Component::Normal(name) = component {
                if let Some(name_str) = name.to_str() {
                    if config.exclude_directories.contains(&name_str.to_string()) {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Check if a file should be watched
    #[allow(dead_code)]
    fn should_watch_file(&self, path: &Path) -> bool {
        Self::should_watch_file_static(path, &self.config)
    }

    /// Convert notify event to our event type (static version)
    fn convert_notify_event_static(
        event: notify::Event,
        config: &HotReloadConfig,
    ) -> HotReloadResult<ConfigChangeEvent> {
        match event.kind {
            notify::EventKind::Create(_) => {
                if let Some(path) = event.paths.first() {
                    if Self::should_watch_file_static(path, config) {
                        Ok(ConfigChangeEvent::Created(path.clone()))
                    } else {
                        Err(HotReloadError::ValidationError(
                            "File not watched".to_string(),
                        ))
                    }
                } else {
                    Err(HotReloadError::ValidationError(
                        "No path in create event".to_string(),
                    ))
                }
            }
            notify::EventKind::Modify(_) => {
                if let Some(path) = event.paths.first() {
                    if Self::should_watch_file_static(path, config) {
                        Ok(ConfigChangeEvent::Modified(path.clone()))
                    } else {
                        Err(HotReloadError::ValidationError(
                            "File not watched".to_string(),
                        ))
                    }
                } else {
                    Err(HotReloadError::ValidationError(
                        "No path in modify event".to_string(),
                    ))
                }
            }
            notify::EventKind::Remove(_) => {
                if let Some(path) = event.paths.first() {
                    Ok(ConfigChangeEvent::Deleted(path.clone()))
                } else {
                    Err(HotReloadError::ValidationError(
                        "No path in remove event".to_string(),
                    ))
                }
            }
            notify::EventKind::Other => {
                // Handle rename events which come as Other in newer notify versions
                if event.paths.len() >= 2 {
                    Ok(ConfigChangeEvent::Renamed {
                        from: event.paths[0].clone(),
                        to: event.paths[1].clone(),
                    })
                } else {
                    Err(HotReloadError::ValidationError(
                        "Invalid rename event".to_string(),
                    ))
                }
            }
            _ => Err(HotReloadError::ValidationError(
                "Unsupported event type".to_string(),
            )),
        }
    }

    /// Convert notify event to our event type
    #[allow(dead_code)]
    fn convert_notify_event(&self, event: notify::Event) -> HotReloadResult<ConfigChangeEvent> {
        Self::convert_notify_event_static(event, &self.config)
    }

    /// Parse configuration file based on extension
    fn parse_config_file(&self, content: &str, path: &Path) -> HotReloadResult<serde_json::Value> {
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or("toml");

        match extension.to_lowercase().as_str() {
            "toml" => toml::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("TOML parsing error: {e}"))),
            "json" => serde_json::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("JSON parsing error: {e}"))),
            "yaml" | "yml" => serde_yaml::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("YAML parsing error: {e}"))),
            _ => Err(HotReloadError::ParsingError(format!(
                "Unsupported file extension: {extension}",
            ))),
        }
    }

    /// Validate configuration using the validator
    fn validate_config(&self, config: &serde_json::Value, path: &Path) -> HotReloadResult<()> {
        // Determine schema based on file name or content
        let schema_name = self.determine_schema_name(path);

        self.validator
            .validate_config(config, &schema_name)
            .map_err(|e| HotReloadError::ValidationError(format!("Validation error: {e}")))
    }

    /// Determine schema name based on file path
    fn determine_schema_name(&self, path: &Path) -> String {
        if let Some(file_name) = path.file_name() {
            if let Some(name) = file_name.to_str() {
                if name.starts_with("ligature-cli") {
                    return "cli".to_string();
                } else if name.starts_with("cacophony") {
                    return "cacophony".to_string();
                } else if name.starts_with("lsp") {
                    return "lsp".to_string();
                }
            }
        }
        "default".to_string()
    }

    /// Start the event processing loop
    async fn start_event_loop(&mut self) {
        if let Some(mut receiver) = self.event_receiver.take() {
            let callbacks = Arc::clone(&self.callbacks);
            let config_cache = Arc::clone(&self.config_cache);
            let validator = Arc::clone(&self.validator);
            let config = self.config.clone();

            tokio::spawn(async move {
                let mut debounce_timer = tokio::time::Instant::now();
                let mut pending_events = Vec::new();

                while let Some(event) = receiver.recv().await {
                    pending_events.push(event);

                    // Debounce events
                    if debounce_timer.elapsed() >= Duration::from_millis(config.debounce_ms) {
                        // Process all pending events
                        for event in pending_events.drain(..) {
                            if let Err(e) = Self::process_config_event(
                                &event,
                                &callbacks,
                                &config_cache,
                                &validator,
                                &config,
                            )
                            .await
                            {
                                eprintln!("Error processing config event: {e:?}");
                            }
                        }
                        debounce_timer = tokio::time::Instant::now();
                    }
                }
            });
        }
    }

    /// Process a configuration change event
    async fn process_config_event(
        event: &ConfigChangeEvent,
        callbacks: &ConfigReloadCallbackMap,
        config_cache: &ConfigCacheMap,
        validator: &Arc<ConfigValidator>,
        config: &HotReloadConfig,
    ) -> HotReloadResult<()> {
        match event {
            ConfigChangeEvent::Created(path) | ConfigChangeEvent::Modified(path) => {
                // Load and validate the configuration
                let config_value = Self::load_config_with_retry(path, validator, config).await?;

                // Call all registered callbacks
                let callbacks = callbacks.lock().unwrap();
                for (name, callback) in callbacks.iter() {
                    if let Err(e) = callback(event.clone(), config_value.clone()) {
                        eprintln!("Callback '{name}' failed: {e}");
                    }
                }
            }
            ConfigChangeEvent::Deleted(path) => {
                // Remove from cache
                let mut cache = config_cache.lock().unwrap();
                cache.remove(path);

                // Call callbacks with null config
                let callbacks = callbacks.lock().unwrap();
                for (name, callback) in callbacks.iter() {
                    if let Err(e) = callback(event.clone(), serde_json::Value::Null) {
                        eprintln!("Callback '{name}' failed: {e}");
                    }
                }
            }
            ConfigChangeEvent::Renamed { from, to } => {
                // Handle rename as delete + create
                let mut cache = config_cache.lock().unwrap();
                if let Some(config_value) = cache.remove(from) {
                    cache.insert(to.clone(), config_value.clone());

                    // Call callbacks
                    let callbacks = callbacks.lock().unwrap();
                    for (name, callback) in callbacks.iter() {
                        if let Err(e) = callback(event.clone(), config_value.clone()) {
                            eprintln!("Callback '{name}' failed: {e}");
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Load configuration with retry logic
    async fn load_config_with_retry(
        path: &Path,
        validator: &Arc<ConfigValidator>,
        config: &HotReloadConfig,
    ) -> HotReloadResult<serde_json::Value> {
        let mut attempts = 0;

        while attempts < config.max_retries {
            match Self::load_config_file_internal(path, validator).await {
                Ok(config_value) => return Ok(config_value),
                Err(e) => {
                    attempts += 1;
                    if attempts >= config.max_retries {
                        return Err(e);
                    }

                    // Wait before retrying
                    tokio::time::sleep(Duration::from_millis(config.retry_delay_ms)).await;
                }
            }
        }

        Err(HotReloadError::Timeout)
    }

    /// Internal method to load configuration file
    async fn load_config_file_internal(
        path: &Path,
        validator: &Arc<ConfigValidator>,
    ) -> HotReloadResult<serde_json::Value> {
        if !path.exists() {
            return Err(HotReloadError::FileNotFound {
                path: path.to_path_buf(),
            });
        }

        let content = tokio::fs::read_to_string(path)
            .await
            .map_err(|e| HotReloadError::FileSystemError(notify::Error::io(e)))?;

        // Parse configuration based on file extension
        let config = Self::parse_config_file_internal(&content, path)?;

        // Validate configuration
        let schema_name = Self::determine_schema_name_internal(path);
        validator
            .validate_config(&config, &schema_name)
            .map_err(|e| HotReloadError::ValidationError(format!("Validation error: {e}")))?;

        Ok(config)
    }

    /// Internal method to parse configuration file
    fn parse_config_file_internal(
        content: &str,
        path: &Path,
    ) -> HotReloadResult<serde_json::Value> {
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or("toml");

        match extension.to_lowercase().as_str() {
            "toml" => toml::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("TOML parsing error: {e}"))),
            "json" => serde_json::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("JSON parsing error: {e}"))),
            "yaml" | "yml" => serde_yaml::from_str(content)
                .map_err(|e| HotReloadError::ParsingError(format!("YAML parsing error: {e}"))),
            _ => Err(HotReloadError::ParsingError(format!(
                "Unsupported file extension: {extension}",
            ))),
        }
    }

    /// Internal method to determine schema name
    fn determine_schema_name_internal(path: &Path) -> String {
        if let Some(file_name) = path.file_name() {
            if let Some(name) = file_name.to_str() {
                if name.starts_with("ligature-cli") {
                    return "cli".to_string();
                } else if name.starts_with("cacophony") {
                    return "cacophony".to_string();
                } else if name.starts_with("lsp") {
                    return "lsp".to_string();
                }
            }
        }
        "default".to_string()
    }
}

impl Drop for ConfigHotReloader {
    fn drop(&mut self) {
        let _ = self.stop_watching();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_hot_reload_basic() {
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("test.toml");

        // Create a test configuration file
        fs::write(
            &config_path,
            r#"
[test]
value = "test"
"#,
        )
        .unwrap();

        let config = HotReloadConfig::default();
        let validator = ConfigValidator::new();
        let mut reloader = ConfigHotReloader::new(config, validator);

        // Register a test callback
        reloader
            .register_callback(
                "test",
                Box::new(|event, config| {
                    println!("Config changed: {event:?}, config: {config:?}");
                    Ok(())
                }),
            )
            .unwrap();

        // Start watching
        reloader.start_watching(temp_dir.path()).await.unwrap();

        // Modify the configuration file
        fs::write(
            &config_path,
            r#"
[test]
value = "updated"
"#,
        )
        .unwrap();

        // Wait a bit for the event to be processed
        tokio::time::sleep(Duration::from_millis(1000)).await;

        // Stop watching
        reloader.stop_watching().unwrap();
    }
}
