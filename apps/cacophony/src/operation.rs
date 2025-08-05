use async_trait::async_trait;
use serde_json::Value;
use std::collections::HashMap;

use crate::collection::Collection;
use crate::environment::Environment;
use crate::error::{CacophonyError, Result};

#[async_trait]
pub trait Operation: Send + Sync {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    async fn execute(&self, collection: &Collection, environment: &Environment) -> Result<OperationResult>;
    fn validate(&self, collection: &Collection, environment: &Environment) -> Result<ValidationResult>;
}

#[derive(Debug)]
pub struct OperationResult {
    pub success: bool,
    pub message: String,
    pub details: HashMap<String, Value>,
    pub duration: std::time::Duration,
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

pub struct DeployOperation;

#[async_trait]
impl Operation for DeployOperation {
    fn name(&self) -> &str {
        "deploy"
    }

    fn description(&self) -> &str {
        "Deploy a collection to an environment"
    }

    async fn execute(&self, collection: &Collection, environment: &Environment) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();
        
        tracing::info!("Executing deploy operation for collection '{}'", collection.name);
        
        // Validate before deployment
        let validation = self.validate(collection, environment)?;
        if !validation.is_valid() {
            return Err(CacophonyError::Validation(format!(
                "Deploy validation failed: {:?}",
                validation.errors
            )));
        }

        // TODO: Implement actual deployment logic
        // This would involve:
        // 1. Resolving variables in collection programs
        // 2. Executing deployment steps
        // 3. Monitoring deployment progress
        // 4. Handling rollback on failure

        let duration = start_time.elapsed();
        
        Ok(OperationResult {
            success: true,
            message: format!("Collection '{}' deployed successfully", collection.name),
            details: HashMap::new(),
            duration,
        })
    }

    fn validate(&self, collection: &Collection, environment: &Environment) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate collection supports the environment
        if !collection.config.environments.contains(&environment.name) {
            errors.push(format!(
                "Collection '{}' does not support environment '{}'",
                collection.name, environment.name
            ));
        }

        // Validate required environment variables
        let required_vars = ["DATABASE_URL", "API_BASE_URL"];
        for var in &required_vars {
            if environment.get_variable(var).is_none() {
                warnings.push(format!("Required variable '{}' is not set", var));
            }
        }

        // Validate collection has programs
        if collection.programs.is_empty() {
            warnings.push(format!("Collection '{}' has no programs to deploy", collection.name));
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct ValidateOperation;

#[async_trait]
impl Operation for ValidateOperation {
    fn name(&self) -> &str {
        "validate"
    }

    fn description(&self) -> &str {
        "Validate a collection configuration"
    }

    async fn execute(&self, collection: &Collection, environment: &Environment) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();
        
        tracing::info!("Executing validate operation for collection '{}'", collection.name);
        
        let validation = self.validate(collection, environment)?;
        
        let duration = start_time.elapsed();
        
        let message = if validation.is_valid() {
            format!("Collection '{}' validation passed", collection.name)
        } else {
            format!("Collection '{}' validation failed", collection.name)
        };

        let mut details = HashMap::new();
        details.insert("errors".to_string(), Value::Array(
            validation.errors.iter().map(|e| Value::String(e.clone())).collect()
        ));
        details.insert("warnings".to_string(), Value::Array(
            validation.warnings.iter().map(|w| Value::String(w.clone())).collect()
        ));

        Ok(OperationResult {
            success: validation.is_valid(),
            message,
            details,
            duration,
        })
    }

    fn validate(&self, collection: &Collection, environment: &Environment) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate collection configuration
        if collection.name.is_empty() {
            errors.push("Collection name cannot be empty".to_string());
        }

        // Validate environment compatibility
        if !collection.config.environments.contains(&environment.name) {
            errors.push(format!(
                "Collection '{}' does not support environment '{}'",
                collection.name, environment.name
            ));
        }

        // Validate programs
        if collection.programs.is_empty() {
            warnings.push(format!("Collection '{}' has no programs", collection.name));
        }

        // Validate dependencies
        for dep_name in &collection.config.dependencies {
            if collection.get_dependency(dep_name).is_none() {
                warnings.push(format!(
                    "Collection '{}' depends on '{}' which is not loaded",
                    collection.name, dep_name
                ));
            }
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct DiffOperation;

#[async_trait]
impl Operation for DiffOperation {
    fn name(&self) -> &str {
        "diff"
    }

    fn description(&self) -> &str {
        "Generate differences between environments"
    }

    async fn execute(&self, collection: &Collection, _environment: &Environment) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();
        
        tracing::info!("Executing diff operation for collection '{}'", collection.name);
        
        // TODO: Implement diff generation
        // This would involve comparing configurations between environments
        
        let duration = start_time.elapsed();
        
        Ok(OperationResult {
            success: true,
            message: format!("Diff generated for collection '{}'", collection.name),
            details: HashMap::new(),
            duration,
        })
    }

    fn validate(&self, collection: &Collection, environment: &Environment) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Basic validation for diff operation
        if collection.name.is_empty() {
            errors.push("Collection name cannot be empty".to_string());
        }

        if environment.name.is_empty() {
            errors.push("Environment name cannot be empty".to_string());
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct CustomOperation {
    pub name: String,
    pub description: String,
    pub script: Option<String>,
    pub parameters: HashMap<String, Value>,
    pub timeout: Option<u64>,
    pub retries: Option<u32>,
}

#[async_trait]
impl Operation for CustomOperation {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        &self.description
    }

    async fn execute(&self, collection: &Collection, environment: &Environment) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();
        
        tracing::info!("Executing custom operation '{}' for collection '{}'", self.name, collection.name);
        
        // Validate before execution
        let validation = self.validate(collection, environment)?;
        if !validation.is_valid() {
            return Err(CacophonyError::Validation(format!(
                "Custom operation validation failed: {:?}",
                validation.errors
            )));
        }

        // Execute custom script if provided
        if let Some(script) = &self.script {
            let resolved_script = environment.resolve_variables(script)?;
            tracing::debug!("Executing script: {}", resolved_script);
            
            // TODO: Implement script execution
            // This would involve:
            // 1. Creating a temporary script file
            // 2. Setting up environment variables
            // 3. Executing the script
            // 4. Capturing output and exit code
        }

        let duration = start_time.elapsed();
        
        Ok(OperationResult {
            success: true,
            message: format!("Custom operation '{}' completed successfully", self.name),
            details: self.parameters.clone(),
            duration,
        })
    }

    fn validate(&self, _collection: &Collection, environment: &Environment) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate operation name
        if self.name.is_empty() {
            errors.push("Custom operation name cannot be empty".to_string());
        }

        // Validate script if provided
        if let Some(script) = &self.script {
            if script.is_empty() {
                errors.push("Custom operation script cannot be empty".to_string());
            }
        }

        // Validate parameters
        for (key, value) in &self.parameters {
            if key.is_empty() {
                errors.push("Parameter key cannot be empty".to_string());
            }
            
            // Validate that parameter can be resolved in environment
            if let Value::String(s) = value {
                if s.contains("${") && !environment.resolve_variables(s).is_ok() {
                    warnings.push(format!("Parameter '{}' may contain unresolved variables", key));
                }
            }
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct OperationManager {
    operations: HashMap<String, Box<dyn Operation>>,
}

impl OperationManager {
    pub fn new() -> Self {
        let mut manager = Self {
            operations: HashMap::new(),
        };

        // Register built-in operations
        manager.register_operation(Box::new(DeployOperation));
        manager.register_operation(Box::new(ValidateOperation));
        manager.register_operation(Box::new(DiffOperation));

        manager
    }

    pub fn register_operation(&mut self, operation: Box<dyn Operation>) {
        self.operations.insert(operation.name().to_string(), operation);
    }

    pub fn get_operation(&self, name: &str) -> Option<&Box<dyn Operation>> {
        self.operations.get(name)
    }

    pub fn list_operations(&self) -> Vec<&str> {
        self.operations.keys().map(|s| s.as_str()).collect()
    }

    pub async fn execute_operation(
        &self,
        name: &str,
        collection: &Collection,
        environment: &Environment,
    ) -> Result<OperationResult> {
        let operation = self.get_operation(name)
            .ok_or_else(|| CacophonyError::NotFound(format!("Operation '{}' not found", name)))?;

        operation.execute(collection, environment).await
    }

    pub fn validate_operation(
        &self,
        name: &str,
        collection: &Collection,
        environment: &Environment,
    ) -> Result<ValidationResult> {
        let operation = self.get_operation(name)
            .ok_or_else(|| CacophonyError::NotFound(format!("Operation '{}' not found", name)))?;

        operation.validate(collection, environment)
    }
} 