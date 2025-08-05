use cacophony_core::error::{CacophonyError, Result};
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct CacophonyXdgConfig {
    pub app_name: String,
}

impl CacophonyXdgConfig {
    pub fn new(app_name: String) -> Self {
        Self { app_name }
    }

    pub async fn save_config(
        &self,
        config: &cacophony_core::config::CacophonyConfig,
    ) -> Result<PathBuf> {
        let config_dir = self.config_dir()?;
        tokio::fs::create_dir_all(&config_dir)
            .await
            .map_err(CacophonyError::Io)?;

        let config_file = config_dir.join("config.toml");
        let config_content = toml::to_string_pretty(config).map_err(CacophonyError::TomlSer)?;

        tokio::fs::write(&config_file, config_content)
            .await
            .map_err(CacophonyError::Io)?;

        Ok(config_file)
    }

    pub fn config_dir(&self) -> Result<PathBuf> {
        let home = std::env::var("HOME")
            .map_err(|_| CacophonyError::Config("HOME environment variable not set".to_string()))?;

        Ok(PathBuf::from(home).join(".config").join(&self.app_name))
    }

    pub fn cache_dir(&self) -> Result<PathBuf> {
        let home = std::env::var("HOME")
            .map_err(|_| CacophonyError::Config("HOME environment variable not set".to_string()))?;

        Ok(PathBuf::from(home).join(".cache").join(&self.app_name))
    }

    pub fn state_dir(&self) -> Result<PathBuf> {
        let home = std::env::var("HOME")
            .map_err(|_| CacophonyError::Config("HOME environment variable not set".to_string()))?;

        Ok(PathBuf::from(home)
            .join(".local")
            .join("state")
            .join(&self.app_name))
    }

    pub async fn ensure_directories(&self) -> Result<()> {
        let dirs = vec![self.config_dir()?, self.cache_dir()?, self.state_dir()?];

        for dir in dirs {
            tokio::fs::create_dir_all(&dir)
                .await
                .map_err(CacophonyError::Io)?;
        }

        Ok(())
    }

    pub fn find_config_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        let config_dir = self.config_dir()?;
        let file_path = config_dir.join(filename);

        if file_path.exists() {
            Ok(Some(file_path))
        } else {
            Ok(None)
        }
    }

    pub fn find_data_file(&self, filename: &str) -> Result<Option<PathBuf>> {
        let data_dir = self.data_dir()?;
        let file_path = data_dir.join(filename);

        if file_path.exists() {
            Ok(Some(file_path))
        } else {
            Ok(None)
        }
    }

    pub fn data_dir(&self) -> Result<PathBuf> {
        let home = std::env::var("HOME")
            .map_err(|_| CacophonyError::Config("HOME environment variable not set".to_string()))?;

        Ok(PathBuf::from(home)
            .join(".local")
            .join("share")
            .join(&self.app_name))
    }

    pub fn plugins_dir(&self) -> Result<PathBuf> {
        Ok(self.data_dir()?.join("plugins"))
    }

    pub fn artifacts_cache_dir(&self) -> Result<PathBuf> {
        Ok(self.cache_dir()?.join("artifacts"))
    }

    pub fn runtime_state_dir(&self) -> Result<PathBuf> {
        Ok(self.state_dir()?.join("runtime"))
    }
}

pub async fn xdg_config_for_cacophony() -> Result<CacophonyXdgConfig> {
    let config = CacophonyXdgConfig::new("cacophony".to_string());
    config.ensure_directories().await?;
    Ok(config)
}
