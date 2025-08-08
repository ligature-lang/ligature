pub mod manager;
pub mod validation;
pub mod xdg;

// Re-export core config types for convenience
pub use cacophony_core::config::*;
pub use manager::ConfigManager;
pub use validation::ValidationResult;
pub use xdg::CacophonyXdgConfig;

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_config_manager_creation() {
        let config_path = PathBuf::from("test-config.toml");
        let manager = ConfigManager::new(config_path).unwrap();
        assert_eq!(manager.get_project_config().name, "default");
    }

    #[test]
    fn test_xdg_config_creation() {
        let xdg_config = CacophonyXdgConfig::new("cacophony".to_string());
        assert_eq!(xdg_config.app_name, "cacophony");
    }
}
