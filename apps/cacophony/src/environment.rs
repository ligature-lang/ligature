use serde_json::Value;
use std::collections::HashMap;
use std::path::Path;

use crate::config::EnvironmentConfig;
use crate::error::{CacophonyError, Result};
use crate::plugin::Plugin;

pub struct Environment {
    pub name: String,
    pub config: EnvironmentConfig,
    pub variables: HashMap<String, Value>,
    pub plugins: Vec<Box<dyn Plugin>>,
}

impl Environment {
    pub fn new(name: String, config: EnvironmentConfig) -> Self {
        Self {
            name,
            config,
            variables: HashMap::new(),
            plugins: Vec::new(),
        }
    }

    pub fn load(&mut self, path: &Path) -> Result<()> {
        if !path.exists() {
            return Err(CacophonyError::NotFound(format!(
                "Environment path not found: {}",
                path.display()
            )));
        }

        // Load environment-specific variables
        self.load_variables(path)?;

        // Load environment-specific overrides
        self.load_overrides(path)?;

        Ok(())
    }

    fn load_variables(&mut self, path: &Path) -> Result<()> {
        // Convert string variables to JSON values
        for (key, value) in &self.config.variables {
            self.variables.insert(key.clone(), Value::String(value.clone()));
        }

        // Load additional variables from environment-specific files
        let env_file = path.join(format!("{}.lig", self.name));
        if env_file.exists() {
            // TODO: Parse Ligature file and extract variables
            // For now, we'll just note that this would be implemented
            tracing::debug!("Environment file found: {}", env_file.display());
        }

        Ok(())
    }

    fn load_overrides(&mut self, path: &Path) -> Result<()> {
        if let Some(overrides) = &self.config.overrides {
            for (key, value) in overrides {
                self.variables.insert(key.clone(), value.clone());
            }
        }

        // Load overrides from environment-specific files
        let overrides_file = path.join(format!("{}.overrides.json", self.name));
        if overrides_file.exists() {
            let content = std::fs::read_to_string(&overrides_file)
                .map_err(|e| CacophonyError::Io(e))?;
            
            let overrides: HashMap<String, Value> = serde_json::from_str(&content)
                .map_err(|e| CacophonyError::Json(e))?;
            
            for (key, value) in overrides {
                self.variables.insert(key, value);
            }
        }

        Ok(())
    }

    pub fn resolve_variables(&self, template: &str) -> Result<String> {
        let mut result = template.to_string();
        
        for (key, value) in &self.variables {
            let placeholder = format!("${{{}}}", key);
            let value_str = match value {
                Value::String(s) => s.clone(),
                Value::Number(n) => n.to_string(),
                Value::Bool(b) => b.to_string(),
                Value::Null => "null".to_string(),
                _ => serde_json::to_string(value)
                    .map_err(|e| CacophonyError::Json(e))?,
            };
            
            result = result.replace(&placeholder, &value_str);
        }

        Ok(result)
    }

    pub fn get_variable(&self, key: &str) -> Option<&Value> {
        self.variables.get(key)
    }

    pub fn set_variable(&mut self, key: String, value: Value) {
        self.variables.insert(key, value);
    }

    pub fn get_plugin(&self, name: &str) -> Option<&Box<dyn Plugin>> {
        self.plugins.iter().find(|p| p.name() == name)
    }

    pub fn add_plugin(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    pub fn validate(&self) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate environment name
        if self.name.is_empty() {
            errors.push("Environment name cannot be empty".to_string());
        }

        // Validate required variables
        let required_vars = ["DATABASE_URL", "API_BASE_URL"];
        for var in &required_vars {
            if !self.variables.contains_key(*var) {
                warnings.push(format!("Required variable '{}' is not set", var));
            }
        }

        // Validate plugin configurations
        for plugin_name in &self.config.plugins {
            if self.get_plugin(plugin_name).is_none() {
                warnings.push(format!("Plugin '{}' is referenced but not loaded", plugin_name));
            }
        }

        Ok(ValidationResult { errors, warnings })
    }

    pub fn merge(&mut self, other: &Environment) {
        // Merge variables (other takes precedence)
        for (key, value) in &other.variables {
            self.variables.insert(key.clone(), value.clone());
        }

        // Merge plugins (avoid duplicates)
        for plugin in &other.plugins {
            if self.get_plugin(plugin.name()).is_none() {
                // Clone the plugin (this would need to be implemented properly)
                // For now, we'll just note that this would be implemented
                tracing::debug!("Would merge plugin: {}", plugin.name());
            }
        }
    }
}

#[derive(Debug)]
pub struct ValidationResult {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}

pub struct EnvironmentManager {
    environments: HashMap<String, Environment>,
}

impl EnvironmentManager {
    pub fn new() -> Self {
        Self {
            environments: HashMap::new(),
        }
    }

    pub fn add_environment(&mut self, name: String, config: EnvironmentConfig) -> Result<()> {
        let mut env = Environment::new(name.clone(), config);
        
        // Load environment-specific files
        let env_path = std::path::Path::new("environments");
        if env_path.exists() {
            env.load(env_path)?;
        }

        self.environments.insert(name, env);
        Ok(())
    }

    pub fn get_environment(&self, name: &str) -> Option<&Environment> {
        self.environments.get(name)
    }

    pub fn get_environment_mut(&mut self, name: &str) -> Option<&mut Environment> {
        self.environments.get_mut(name)
    }

    pub fn list_environments(&self) -> Vec<&str> {
        self.environments.keys().map(|s| s.as_str()).collect()
    }

    pub fn validate_all(&self) -> Result<HashMap<String, ValidationResult>> {
        let mut results = HashMap::new();
        
        for (name, env) in &self.environments {
            results.insert(name.clone(), env.validate()?);
        }

        Ok(results)
    }
} 