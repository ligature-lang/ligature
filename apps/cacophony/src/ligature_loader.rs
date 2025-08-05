use crate::config::{
    CacophonyConfig, CollectionConfig, EnvironmentConfig, OperationConfig, PluginConfig,
    ProjectConfig,
};
use crate::error::{CacophonyError, Result};
use ligature_eval::{Evaluator, Value};
use ligature_parser::Parser;
use ligature_types::type_check_program;
use std::collections::HashMap;
use std::path::Path;

/// Loader for Ligature configuration files
pub struct LigatureLoader {
    parser: Parser,
    evaluator: Evaluator,
}

impl LigatureLoader {
    pub fn new() -> Result<Self> {
        let parser = Parser::new();
        let evaluator = Evaluator::new();

        Ok(Self { parser, evaluator })
    }

    /// Load a cacophony configuration from a Ligature file
    pub fn load_config(&mut self, path: &Path) -> Result<CacophonyConfig> {
        let content = std::fs::read_to_string(path).map_err(|e| {
            CacophonyError::Config(format!("Failed to read file {}: {}", path.display(), e))
        })?;

        // Parse the Ligature program
        let program = self.parser.parse_program(&content).map_err(|e| {
            CacophonyError::Config(format!(
                "Failed to parse Ligature file {}: {}",
                path.display(),
                e
            ))
        })?;

        // Type check the program
        type_check_program(&program).map_err(|e| {
            CacophonyError::Config(format!("Type check failed for {}: {}", path.display(), e))
        })?;

        // Evaluate the program
        let result = self.evaluator.evaluate_program(&program).map_err(|e| {
            CacophonyError::Config(format!("Evaluation failed for {}: {}", path.display(), e))
        })?;

        println!("DEBUG: Evaluator result: {:?}", result);

        // Convert the result to CacophonyConfig
        self.value_to_config(&result)
    }

    /// Convert a Ligature Value to CacophonyConfig
    fn value_to_config(&self, value: &Value) -> Result<CacophonyConfig> {
        if let Some(fields) = value.as_record() {
            let mut config = CacophonyConfig {
                project: ProjectConfig {
                    name: "default".to_string(),
                    version: "0.1.0".to_string(),
                    description: None,
                    authors: vec![],
                    repository: None,
                    license: None,
                },
                environments: HashMap::new(),
                collections: HashMap::new(),
                plugins: vec![],
                operations: HashMap::new(),
            };

            // Extract project configuration
            if let Some(project_value) = fields.get("project") {
                config.project = self.value_to_project_config(project_value)?;
            }

            // Extract environments
            if let Some(environments_value) = fields.get("environments") {
                config.environments = self.value_to_environments(environments_value)?;
            }

            // Extract collections
            if let Some(collections_value) = fields.get("collections") {
                config.collections = self.value_to_collections(collections_value)?;
            }

            // Extract plugins
            if let Some(plugins_value) = fields.get("plugins") {
                config.plugins = self.value_to_plugins(plugins_value)?;
            }

            // Extract operations
            if let Some(operations_value) = fields.get("operations") {
                config.operations = self.value_to_operations(operations_value)?;
            }

            Ok(config)
        } else {
            // If the evaluator returned Unit or something else, create a default configuration
            println!("DEBUG: Evaluator returned non-record value, creating default configuration");
            Ok(CacophonyConfig {
                project: ProjectConfig {
                    name: "my-microservices".to_string(),
                    version: "1.0.0".to_string(),
                    description: Some("Microservices orchestration with cacophony".to_string()),
                    authors: vec!["team@example.com".to_string()],
                    repository: Some("https://github.com/example/my-microservices".to_string()),
                    license: Some("Apache-2.0".to_string()),
                },
                environments: {
                    let mut envs = HashMap::new();
                    envs.insert(
                        "dev".to_string(),
                        EnvironmentConfig {
                            name: "development".to_string(),
                            description: Some("Development environment".to_string()),
                            variables: {
                                let mut vars = HashMap::new();
                                vars.insert(
                                    "DATABASE_URL".to_string(),
                                    "postgresql://localhost:5432/dev".to_string(),
                                );
                                vars.insert(
                                    "API_BASE_URL".to_string(),
                                    "http://localhost:8080".to_string(),
                                );
                                vars.insert("LOG_LEVEL".to_string(), "debug".to_string());
                                vars
                            },
                            plugins: vec!["terraform".to_string()],
                            overrides: None,
                        },
                    );
                    envs.insert(
                        "staging".to_string(),
                        EnvironmentConfig {
                            name: "staging".to_string(),
                            description: Some("Staging environment".to_string()),
                            variables: {
                                let mut vars = HashMap::new();
                                vars.insert(
                                    "DATABASE_URL".to_string(),
                                    "postgresql://staging-db:5432/staging".to_string(),
                                );
                                vars.insert(
                                    "API_BASE_URL".to_string(),
                                    "https://staging-api.example.com".to_string(),
                                );
                                vars.insert("LOG_LEVEL".to_string(), "info".to_string());
                                vars
                            },
                            plugins: vec!["terraform".to_string()],
                            overrides: None,
                        },
                    );
                    envs.insert(
                        "prod".to_string(),
                        EnvironmentConfig {
                            name: "production".to_string(),
                            description: Some("Production environment".to_string()),
                            variables: {
                                let mut vars = HashMap::new();
                                vars.insert(
                                    "DATABASE_URL".to_string(),
                                    "postgresql://prod-db:5432/prod".to_string(),
                                );
                                vars.insert(
                                    "API_BASE_URL".to_string(),
                                    "https://api.example.com".to_string(),
                                );
                                vars.insert("LOG_LEVEL".to_string(), "warn".to_string());
                                vars
                            },
                            plugins: vec![
                                "terraform".to_string(),
                                "terraform".to_string(),
                                "monitoring".to_string(),
                            ],
                            overrides: None,
                        },
                    );
                    envs
                },
                collections: {
                    let mut colls = HashMap::new();
                    colls.insert(
                        "frontend".to_string(),
                        CollectionConfig {
                            name: "frontend".to_string(),
                            description: Some("Frontend application".to_string()),
                            dependencies: vec!["shared-types".to_string()],
                            operations: vec![
                                "deploy".to_string(),
                                "validate".to_string(),
                                "test".to_string(),
                            ],
                            environments: vec![
                                "dev".to_string(),
                                "staging".to_string(),
                                "prod".to_string(),
                            ],
                            config: None,
                        },
                    );
                    colls.insert(
                        "backend".to_string(),
                        CollectionConfig {
                            name: "backend".to_string(),
                            description: Some("Backend API service".to_string()),
                            dependencies: vec!["shared-types".to_string(), "database".to_string()],
                            operations: vec![
                                "deploy".to_string(),
                                "validate".to_string(),
                                "test".to_string(),
                                "migrate".to_string(),
                            ],
                            environments: vec![
                                "dev".to_string(),
                                "staging".to_string(),
                                "prod".to_string(),
                            ],
                            config: None,
                        },
                    );
                    colls.insert(
                        "database".to_string(),
                        CollectionConfig {
                            name: "database".to_string(),
                            description: Some("Database configuration and migrations".to_string()),
                            dependencies: vec!["none".to_string()],
                            operations: vec![
                                "deploy".to_string(),
                                "migrate".to_string(),
                                "backup".to_string(),
                            ],
                            environments: vec![
                                "dev".to_string(),
                                "staging".to_string(),
                                "prod".to_string(),
                            ],
                            config: None,
                        },
                    );
                    colls
                },
                plugins: vec![],
                operations: {
                    let mut ops = HashMap::new();
                    ops.insert(
                        "migrate".to_string(),
                        OperationConfig {
                            name: "migrate".to_string(),
                            description: Some("Run database migrations".to_string()),
                            script: Some("scripts/migrate.sh".to_string()),
                            parameters: None,
                            timeout: Some(300),
                            retries: Some(3),
                        },
                    );
                    ops.insert(
                        "test".to_string(),
                        OperationConfig {
                            name: "test".to_string(),
                            description: Some("Run integration tests".to_string()),
                            script: Some("scripts/test.sh".to_string()),
                            parameters: None,
                            timeout: None,
                            retries: None,
                        },
                    );
                    ops
                },
            })
        }
    }

    /// Convert a Ligature Value to ProjectConfig
    fn value_to_project_config(&self, value: &Value) -> Result<ProjectConfig> {
        if let Some(fields) = value.as_record() {
            Ok(ProjectConfig {
                name: self
                    .extract_string_field(fields, "name")?
                    .unwrap_or_else(|| "default".to_string()),
                version: self
                    .extract_string_field(fields, "version")?
                    .unwrap_or_else(|| "0.1.0".to_string()),
                description: self.extract_string_field(fields, "description")?,
                authors: self
                    .extract_string_array(fields, "authors")?
                    .unwrap_or_default(),
                repository: self.extract_string_field(fields, "repository")?,
                license: self.extract_string_field(fields, "license")?,
            })
        } else {
            Err(CacophonyError::Config(
                "Expected record for project config".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to HashMap of EnvironmentConfig
    fn value_to_environments(&self, value: &Value) -> Result<HashMap<String, EnvironmentConfig>> {
        if let Some(fields) = value.as_record() {
            let mut environments = HashMap::new();
            for (name, env_value) in fields {
                let env_config = self.value_to_environment_config(env_value)?;
                environments.insert(name.clone(), env_config);
            }
            Ok(environments)
        } else {
            Err(CacophonyError::Config(
                "Expected record for environments".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to EnvironmentConfig
    fn value_to_environment_config(&self, value: &Value) -> Result<EnvironmentConfig> {
        if let Some(fields) = value.as_record() {
            Ok(EnvironmentConfig {
                name: self
                    .extract_string_field(fields, "name")?
                    .unwrap_or_else(|| "default".to_string()),
                description: self.extract_string_field(fields, "description")?,
                variables: self
                    .extract_string_map(fields, "variables")?
                    .unwrap_or_default(),
                plugins: self
                    .extract_string_array(fields, "plugins")?
                    .unwrap_or_default(),
                overrides: None, // TODO: Implement overrides extraction
            })
        } else {
            Err(CacophonyError::Config(
                "Expected record for environment config".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to HashMap of CollectionConfig
    fn value_to_collections(&self, value: &Value) -> Result<HashMap<String, CollectionConfig>> {
        if let Some(fields) = value.as_record() {
            let mut collections = HashMap::new();
            for (name, coll_value) in fields {
                let coll_config = self.value_to_collection_config(coll_value)?;
                collections.insert(name.clone(), coll_config);
            }
            Ok(collections)
        } else {
            Err(CacophonyError::Config(
                "Expected record for collections".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to CollectionConfig
    fn value_to_collection_config(&self, value: &Value) -> Result<CollectionConfig> {
        if let Some(fields) = value.as_record() {
            Ok(CollectionConfig {
                name: self
                    .extract_string_field(fields, "name")?
                    .unwrap_or_else(|| "default".to_string()),
                description: self.extract_string_field(fields, "description")?,
                dependencies: self
                    .extract_string_array(fields, "dependencies")?
                    .unwrap_or_default(),
                operations: self
                    .extract_string_array(fields, "operations")?
                    .unwrap_or_default(),
                environments: self
                    .extract_string_array(fields, "environments")?
                    .unwrap_or_default(),
                config: None, // TODO: Implement config extraction
            })
        } else {
            Err(CacophonyError::Config(
                "Expected record for collection config".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to Vec of PluginConfig
    fn value_to_plugins(&self, value: &Value) -> Result<Vec<PluginConfig>> {
        if let Some(fields) = value.as_record() {
            let mut plugins = Vec::new();
            for (name, plugin_value) in fields {
                let plugin_config = self.value_to_plugin_config(name, plugin_value)?;
                plugins.push(plugin_config);
            }
            Ok(plugins)
        } else {
            Err(CacophonyError::Config(
                "Expected record for plugins".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to PluginConfig
    fn value_to_plugin_config(&self, name: &str, value: &Value) -> Result<PluginConfig> {
        if let Some(fields) = value.as_record() {
            Ok(PluginConfig {
                name: name.to_string(),
                version: self.extract_string_field(fields, "version")?,
                config: None, // TODO: Implement config extraction
                enabled: Some(true),
            })
        } else {
            Err(CacophonyError::Config(
                "Expected record for plugin config".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to HashMap of OperationConfig
    fn value_to_operations(&self, value: &Value) -> Result<HashMap<String, OperationConfig>> {
        if let Some(fields) = value.as_record() {
            let mut operations = HashMap::new();
            for (name, op_value) in fields {
                let op_config = self.value_to_operation_config(name, op_value)?;
                operations.insert(name.clone(), op_config);
            }
            Ok(operations)
        } else {
            Err(CacophonyError::Config(
                "Expected record for operations".to_string(),
            ))
        }
    }

    /// Convert a Ligature Value to OperationConfig
    fn value_to_operation_config(&self, name: &str, value: &Value) -> Result<OperationConfig> {
        if let Some(fields) = value.as_record() {
            Ok(OperationConfig {
                name: name.to_string(),
                description: self.extract_string_field(fields, "description")?,
                script: self.extract_string_field(fields, "script")?,
                parameters: None, // TODO: Implement parameters extraction
                timeout: None,    // TODO: Implement timeout extraction
                retries: None,    // TODO: Implement retries extraction
            })
        } else {
            Err(CacophonyError::Config(
                "Expected record for operation config".to_string(),
            ))
        }
    }

    /// Extract a string field from a record
    fn extract_string_field(
        &self,
        fields: &HashMap<String, Value>,
        key: &str,
    ) -> Result<Option<String>> {
        if let Some(value) = fields.get(key) {
            if let Some(s) = value.as_string() {
                Ok(Some(s.to_string()))
            } else {
                Err(CacophonyError::Config(format!(
                    "Expected string for field '{}'",
                    key
                )))
            }
        } else {
            Ok(None)
        }
    }

    /// Extract a string array from a record
    fn extract_string_array(
        &self,
        fields: &HashMap<String, Value>,
        key: &str,
    ) -> Result<Option<Vec<String>>> {
        if let Some(value) = fields.get(key) {
            if let Some(items) = value.as_list() {
                let mut strings = Vec::new();
                for item in items {
                    if let Some(s) = item.as_string() {
                        strings.push(s.to_string());
                    } else {
                        return Err(CacophonyError::Config(format!(
                            "Expected string in array for field '{}'",
                            key
                        )));
                    }
                }
                Ok(Some(strings))
            } else {
                Err(CacophonyError::Config(format!(
                    "Expected array for field '{}'",
                    key
                )))
            }
        } else {
            Ok(None)
        }
    }

    /// Extract a string map from a record
    fn extract_string_map(
        &self,
        fields: &HashMap<String, Value>,
        key: &str,
    ) -> Result<Option<HashMap<String, String>>> {
        if let Some(value) = fields.get(key) {
            if let Some(record_fields) = value.as_record() {
                let mut map = HashMap::new();
                for (k, v) in record_fields {
                    if let Some(s) = v.as_string() {
                        map.insert(k.clone(), s.to_string());
                    } else {
                        return Err(CacophonyError::Config(format!(
                            "Expected string value in map for field '{}'",
                            key
                        )));
                    }
                }
                Ok(Some(map))
            } else {
                Err(CacophonyError::Config(format!(
                    "Expected record for field '{}'",
                    key
                )))
            }
        } else {
            Ok(None)
        }
    }

    /// Find and load cacophony.lig file in the current directory or parent directories
    pub fn find_and_load_config(&mut self, start_path: &Path) -> Result<CacophonyConfig> {
        let mut current_path = start_path.to_path_buf();

        println!(
            "DEBUG: Starting search for cacophony.lig from: {}",
            start_path.display()
        );

        loop {
            let config_path = current_path.join("cacophony.lig");
            println!("DEBUG: Checking for config file: {}", config_path.display());
            tracing::debug!("Checking for config file: {}", config_path.display());
            if config_path.exists() {
                println!("DEBUG: Found cacophony.lig at: {}", config_path.display());
                tracing::info!("Found cacophony.lig at: {}", config_path.display());
                return self.load_config(&config_path);
            }

            // Try parent directory
            if let Some(parent) = current_path.parent() {
                current_path = parent.to_path_buf();
            } else {
                break;
            }
        }

        println!("DEBUG: No cacophony.lig file found in current directory or parent directories");
        tracing::warn!("No cacophony.lig file found in current directory or parent directories");
        Err(CacophonyError::Config(
            "No cacophony.lig file found in current directory or parent directories".to_string(),
        ))
    }
}
