use std::collections::HashMap;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacophonyConfig {
    pub project: ProjectConfig,
    pub environments: HashMap<String, EnvironmentConfig>,
    pub collections: HashMap<String, CollectionConfig>,
    pub plugins: Vec<PluginConfig>,
    pub operations: HashMap<String, OperationConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectConfig {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub authors: Vec<String>,
    pub repository: Option<String>,
    pub license: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentConfig {
    pub name: String,
    pub description: Option<String>,
    pub variables: HashMap<String, String>,
    pub plugins: Vec<String>,
    pub overrides: Option<HashMap<String, serde_json::Value>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectionConfig {
    pub name: String,
    pub description: Option<String>,
    pub dependencies: Vec<String>,
    pub operations: Vec<String>,
    pub environments: Vec<String>,
    pub config: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginConfig {
    pub name: String,
    pub version: Option<String>,
    pub config: Option<serde_json::Value>,
    pub enabled: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OperationConfig {
    pub name: String,
    pub description: Option<String>,
    pub script: Option<String>,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
    pub timeout: Option<u64>,
    pub retries: Option<u32>,
}
