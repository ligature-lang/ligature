use std::collections::HashMap;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LigatureProgram {
    pub name: String,
    pub content: String,
    pub path: PathBuf,
}

impl LigatureProgram {
    pub fn new(name: String, content: String, path: PathBuf) -> Self {
        Self {
            name,
            content,
            path,
        }
    }

    pub fn load_from_file(path: &std::path::Path) -> crate::error::Result<Self> {
        let content = std::fs::read_to_string(path).map_err(crate::error::CacophonyError::Io)?;

        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        Ok(Self::new(name, content, path.to_path_buf()))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Collection {
    pub name: String,
    pub config: crate::config::CollectionConfig,
    pub programs: Vec<LigatureProgram>,
    pub dependencies: Vec<String>, // Collection names, not full Collection objects
    pub variables: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Environment {
    pub name: String,
    pub description: Option<String>,
    pub variables: HashMap<String, String>,
    pub plugins: Vec<String>,
    pub overrides: Option<HashMap<String, serde_json::Value>>,
}

impl Environment {
    pub fn get_variable(&self, key: &str) -> Option<&String> {
        self.variables.get(key)
    }
}
