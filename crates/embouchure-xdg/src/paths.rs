//! XDG base directory path resolution with fallback support.

use std::path::PathBuf;

use xdg::BaseDirectories;

use crate::error::{Result, XdgError};

/// XDG base directory paths for a Ligature component.
#[derive(Debug, Clone)]
pub struct XdgPaths {
    /// Component name (e.g., "keywork", "krox", "cli", "lsp")
    component: String,
    /// XDG base directories instance
    xdg: BaseDirectories,
}

impl XdgPaths {
    /// Create a new XDG paths instance for a component.
    ///
    /// # Arguments
    ///
    /// * `component` - The component name (e.g., "keywork", "krox", "cli", "lsp")
    ///
    /// # Returns
    ///
    /// Returns an error if the component name is invalid or XDG directories cannot be determined.
    pub fn new(component: &str) -> Result<Self> {
        Self::validate_component_name(component)?;

        let xdg = BaseDirectories::with_prefix("ligature").map_err(XdgError::XdgBaseDirError)?;

        Ok(Self {
            component: component.to_string(),
            xdg,
        })
    }

    /// Get the configuration directory for this component.
    ///
    /// Returns `~/.config/ligature/{component}/` on XDG systems,
    /// or a fallback path on other systems.
    pub fn config_dir(&self) -> Result<PathBuf> {
        let config_dir = self.xdg.get_config_home().join(&self.component);
        Ok(config_dir)
    }

    /// Get the data directory for this component.
    ///
    /// Returns `~/.local/share/ligature/{component}/` on XDG systems,
    /// or a fallback path on other systems.
    pub fn data_dir(&self) -> Result<PathBuf> {
        let data_dir = self.xdg.get_data_home().join(&self.component);
        Ok(data_dir)
    }

    /// Get the cache directory for this component.
    ///
    /// Returns `~/.cache/ligature/{component}/` on XDG systems,
    /// or a fallback path on other systems.
    pub fn cache_dir(&self) -> Result<PathBuf> {
        let cache_dir = self.xdg.get_cache_home().join(&self.component);
        Ok(cache_dir)
    }

    /// Get the state directory for this component.
    ///
    /// Returns `~/.local/state/ligature/{component}/` on XDG systems,
    /// or a fallback path on other systems.
    pub fn state_dir(&self) -> Result<PathBuf> {
        let state_dir = self.xdg.get_state_home().join(&self.component);
        Ok(state_dir)
    }

    /// Get the runtime directory for this component.
    ///
    /// Returns `/run/user/{uid}/ligature/{component}/` on XDG systems,
    /// or a fallback path on other systems.
    pub fn runtime_dir(&self) -> Result<PathBuf> {
        let runtime_dir = self
            .xdg
            .get_runtime_directory()
            .map_err(XdgError::XdgBaseDirError)?
            .join(&self.component);
        Ok(runtime_dir)
    }

    /// Get a configuration file path for this component.
    ///
    /// # Arguments
    ///
    /// * `filename` - The configuration file name
    ///
    /// # Returns
    ///
    /// Returns the full path to the configuration file.
    pub fn config_file(&self, filename: &str) -> Result<PathBuf> {
        let config_dir = self.config_dir()?;
        Ok(config_dir.join(filename))
    }

    /// Get a data file path for this component.
    ///
    /// # Arguments
    ///
    /// * `filename` - The data file name
    ///
    /// # Returns
    ///
    /// Returns the full path to the data file.
    pub fn data_file(&self, filename: &str) -> Result<PathBuf> {
        let data_dir = self.data_dir()?;
        Ok(data_dir.join(filename))
    }

    /// Get a cache file path for this component.
    ///
    /// # Arguments
    ///
    /// * `filename` - The cache file name
    ///
    /// # Returns
    ///
    /// Returns the full path to the cache file.
    pub fn cache_file(&self, filename: &str) -> Result<PathBuf> {
        let cache_dir = self.cache_dir()?;
        Ok(cache_dir.join(filename))
    }

    /// Get a state file path for this component.
    ///
    /// # Arguments
    ///
    /// * `filename` - The state file name
    ///
    /// # Returns
    ///
    /// Returns the full path to the state file.
    pub fn state_file(&self, filename: &str) -> Result<PathBuf> {
        let state_dir = self.state_dir()?;
        Ok(state_dir.join(filename))
    }

    /// Ensure all directories exist for this component.
    ///
    /// Creates the config, data, cache, and state directories if they don't exist.
    pub async fn ensure_directories(&self) -> Result<()> {
        let dirs = [
            self.config_dir()?,
            self.data_dir()?,
            self.cache_dir()?,
            self.state_dir()?,
        ];

        for dir in dirs {
            if !dir.exists() {
                tokio::fs::create_dir_all(&dir).await.map_err(|e| {
                    XdgError::CreateDirectoryError {
                        path: dir.display().to_string(),
                        source: e,
                    }
                })?;
            }
        }

        Ok(())
    }

    /// Find a configuration file in the standard locations.
    ///
    /// Searches for the file in the following order:
    /// 1. User-specific config directory
    /// 2. System-wide config directories
    ///
    /// # Arguments
    ///
    /// * `filename` - The configuration file name
    ///
    /// # Returns
    ///
    /// Returns the path to the first found configuration file, or None if not found.
    pub fn find_config_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        // Check user-specific config first
        let user_config = self.config_file(filename)?;
        if user_config.exists() {
            return Ok(Some(user_config));
        }

        // Check system-wide config directories
        for config_dir in self.xdg.get_config_dirs() {
            let system_config = config_dir
                .join("ligature")
                .join(&self.component)
                .join(filename);
            if system_config.exists() {
                return Ok(Some(system_config));
            }
        }

        Ok(None)
    }

    /// Find a data file in the standard locations.
    ///
    /// Searches for the file in the following order:
    /// 1. User-specific data directory
    /// 2. System-wide data directories
    ///
    /// # Arguments
    ///
    /// * `filename` - The data file name
    ///
    /// # Returns
    ///
    /// Returns the path to the first found data file, or None if not found.
    pub fn find_data_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        // Check user-specific data first
        let user_data = self.data_file(filename)?;
        if user_data.exists() {
            return Ok(Some(user_data));
        }

        // Check system-wide data directories
        for data_dir in self.xdg.get_data_dirs() {
            let system_data = data_dir
                .join("ligature")
                .join(&self.component)
                .join(filename);
            if system_data.exists() {
                return Ok(Some(system_data));
            }
        }

        Ok(None)
    }

    /// Get the component name.
    pub fn component(&self) -> &str {
        &self.component
    }

    /// Validate a component name.
    ///
    /// Component names must be:
    /// - Non-empty
    /// - ASCII alphanumeric characters, hyphens, and underscores only
    /// - Not start with a hyphen or underscore
    /// - Not end with a hyphen or underscore
    /// - Not contain consecutive hyphens or underscores
    fn validate_component_name(component: &str) -> Result<()> {
        if component.is_empty() {
            return Err(XdgError::InvalidComponentName {
                name: component.to_string(),
                reason: "Component name cannot be empty".to_string(),
            });
        }

        if !component
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
        {
            return Err(XdgError::InvalidComponentName {
                name: component.to_string(),
                reason: "Component name can only contain ASCII alphanumeric characters, hyphens, \
                         and underscores"
                    .to_string(),
            });
        }

        if component.starts_with('-') || component.starts_with('_') {
            return Err(XdgError::InvalidComponentName {
                name: component.to_string(),
                reason: "Component name cannot start with a hyphen or underscore".to_string(),
            });
        }

        if component.ends_with('-') || component.ends_with('_') {
            return Err(XdgError::InvalidComponentName {
                name: component.to_string(),
                reason: "Component name cannot end with a hyphen or underscore".to_string(),
            });
        }

        if component.contains("--")
            || component.contains("__")
            || component.contains("-_")
            || component.contains("_-")
        {
            return Err(XdgError::InvalidComponentName {
                name: component.to_string(),
                reason: "Component name cannot contain consecutive hyphens or underscores"
                    .to_string(),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_component_names() {
        let valid_names = [
            "keywork",
            "krox",
            "cli",
            "lsp",
            "cacophony",
            "test-component",
            "test_component",
        ];

        for name in &valid_names {
            assert!(XdgPaths::validate_component_name(name).is_ok());
        }
    }

    #[test]
    fn test_invalid_component_names() {
        let invalid_names = [
            ("", "empty"),
            ("-invalid", "starts with hyphen"),
            ("_invalid", "starts with underscore"),
            ("invalid-", "ends with hyphen"),
            ("invalid_", "ends with underscore"),
            ("invalid--name", "consecutive hyphens"),
            ("invalid__name", "consecutive underscores"),
            ("invalid-_name", "hyphen underscore"),
            ("invalid_-name", "underscore hyphen"),
            ("invalid name", "contains space"),
            ("invalid.name", "contains dot"),
        ];

        for (name, reason) in &invalid_names {
            let result = XdgPaths::validate_component_name(name);
            assert!(
                result.is_err(),
                "Component name '{name}' should be invalid: {reason}"
            );
        }
    }

    #[test]
    fn test_xdg_paths_creation() {
        let paths = XdgPaths::new("test").unwrap();
        assert_eq!(paths.component(), "test");
    }

    #[test]
    fn test_xdg_paths_invalid_component() {
        let result = XdgPaths::new("-invalid");
        assert!(result.is_err());
    }
}
