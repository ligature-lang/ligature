use async_trait::async_trait;
use serde_json::Value;
use std::collections::HashMap;
use std::process::Command;

use crate::error::{CacophonyError, Result};
use crate::operation::{Operation, OperationResult, ValidationResult};

#[async_trait]
pub trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn description(&self) -> &str;
    fn operations(&self) -> Vec<Box<dyn Operation>>;
    fn configure(&mut self, config: &Value) -> Result<()>;
}

pub struct TerraformPlugin {
    name: String,
    version: String,
    config: TerraformConfig,
}

#[derive(Debug, Clone)]
pub struct TerraformConfig {
    pub workspace: Option<String>,
    pub backend: Option<String>,
    pub variables: HashMap<String, String>,
    pub dry_run: bool,
    pub timeout: u64,
    pub retries: u32,
    pub terraform_path: Option<String>,
}

impl Default for TerraformConfig {
    fn default() -> Self {
        Self {
            workspace: Some("default".to_string()),
            backend: None,
            variables: HashMap::new(),
            dry_run: false,
            timeout: 600,
            retries: 3,
            terraform_path: None,
        }
    }
}

impl TerraformPlugin {
    pub fn new() -> Self {
        Self {
            name: "terraform".to_string(),
            version: "1.0.0".to_string(),
            config: TerraformConfig::default(),
        }
    }

    fn get_terraform_path(&self) -> &str {
        self.config.terraform_path.as_deref().unwrap_or("terraform")
    }

    fn generate_terraform_config(
        &self,
        collection: &crate::collection::Collection,
        environment: &crate::environment::Environment,
    ) -> Result<String> {
        let mut config = String::new();

        // Add Terraform version requirement
        config.push_str("terraform {\n");
        config.push_str("  required_version = \">= 1.0\"\n");

        if let Some(backend) = &self.config.backend {
            config.push_str(&format!("  backend \"{}\" {{}}\n", backend));
        }

        config.push_str("}\n\n");

        // Add provider configurations
        config.push_str("provider \"aws\" {\n");
        config.push_str("  region = \"us-west-2\"\n");
        config.push_str("}\n\n");

        // Generate resources from collection programs
        for program in &collection.programs {
            let resource_config = self.generate_resource_config(&program.name, environment)?;
            config.push_str(&resource_config);
            config.push_str("\n");
        }

        // Add variables
        config.push_str("variable \"environment\" {\n");
        config.push_str("  description = \"Environment name\"\n");
        config.push_str("  type = string\n");
        config.push_str("}\n\n");

        for (key, value) in &environment.variables {
            config.push_str(&format!("variable \"{}\" {{\n", key));
            config.push_str(&format!("  description = \"{}\"\n", key));
            config.push_str("  type = string\n");
            config.push_str(&format!("  default = \"{}\"\n", value));
            config.push_str("}\n\n");
        }

        Ok(config)
    }

    fn generate_resource_config(
        &self,
        program: &str,
        environment: &crate::environment::Environment,
    ) -> Result<String> {
        // Generate Terraform configuration for a program
        // This is a simplified implementation - in practice, you'd parse the Ligature AST
        // and generate appropriate Terraform resources based on the program structure

        let mut config = String::new();

        // Example: Generate an EC2 instance
        config.push_str(&format!("resource \"aws_instance\" \"{}\" {{\n", program));
        config.push_str("  ami = \"ami-12345678\"\n");
        config.push_str("  instance_type = \"t3.micro\"\n");
        config.push_str(&format!("  tags = {{\n"));
        config.push_str(&format!(
            "    Name = \"{}-{}\"\n",
            program, environment.name
        ));
        config.push_str(&format!("    Environment = \"{}\"\n", environment.name));
        config.push_str(&format!("    ManagedBy = \"cacophony\"\n"));
        config.push_str(&format!("  }}\n"));
        config.push_str("}\n");

        Ok(config)
    }

    async fn execute_terraform_command(&self, args: &[&str], working_dir: &str) -> Result<String> {
        let mut cmd = Command::new(self.get_terraform_path());
        cmd.args(args);
        cmd.current_dir(working_dir);

        // Set environment variables
        for (key, value) in &self.config.variables {
            cmd.env(format!("TF_VAR_{}", key), value);
        }

        if let Some(workspace) = &self.config.workspace {
            cmd.env("TF_WORKSPACE", workspace);
        }

        let output = cmd
            .output()
            .map_err(|e| CacophonyError::Plugin(format!("Failed to execute terraform: {}", e)))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(CacophonyError::Plugin(format!(
                "Terraform command failed: {}",
                stderr
            )));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.to_string())
    }

    async fn init_terraform(&self, working_dir: &str) -> Result<()> {
        tracing::info!("Initializing Terraform in {}", working_dir);

        let args = if self.config.dry_run {
            vec!["init", "-input=false"]
        } else {
            vec!["init"]
        };

        self.execute_terraform_command(&args, working_dir).await?;
        Ok(())
    }

    async fn select_workspace(&self, working_dir: &str) -> Result<()> {
        if let Some(workspace) = &self.config.workspace {
            tracing::info!("Selecting Terraform workspace: {}", workspace);

            // Check if workspace exists, create if not
            let list_output = self
                .execute_terraform_command(&["workspace", "list"], working_dir)
                .await?;

            if !list_output.contains(workspace) {
                self.execute_terraform_command(&["workspace", "new", workspace], working_dir)
                    .await?;
            } else {
                self.execute_terraform_command(&["workspace", "select", workspace], working_dir)
                    .await?;
            }
        }

        Ok(())
    }
}

#[async_trait]
impl Plugin for TerraformPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        "Terraform infrastructure management plugin"
    }

    fn operations(&self) -> Vec<Box<dyn Operation>> {
        vec![
            Box::new(TerraformPlanOperation {
                config: self.config.clone(),
            }),
            Box::new(TerraformApplyOperation {
                config: self.config.clone(),
            }),
            Box::new(TerraformDestroyOperation {
                config: self.config.clone(),
            }),
        ]
    }

    fn configure(&mut self, config: &Value) -> Result<()> {
        if let Some(workspace) = config.get("workspace").and_then(|v| v.as_str()) {
            self.config.workspace = Some(workspace.to_string());
        }

        if let Some(backend) = config.get("backend").and_then(|v| v.as_str()) {
            self.config.backend = Some(backend.to_string());
        }

        if let Some(variables) = config.get("variables").and_then(|v| v.as_object()) {
            for (key, value) in variables {
                if let Some(val_str) = value.as_str() {
                    self.config
                        .variables
                        .insert(key.clone(), val_str.to_string());
                }
            }
        }

        if let Some(dry_run) = config.get("dry_run").and_then(|v| v.as_bool()) {
            self.config.dry_run = dry_run;
        }

        if let Some(timeout) = config.get("timeout").and_then(|v| v.as_u64()) {
            self.config.timeout = timeout;
        }

        if let Some(retries) = config.get("retries").and_then(|v| v.as_u64()) {
            self.config.retries = retries as u32;
        }

        if let Some(terraform_path) = config.get("terraform_path").and_then(|v| v.as_str()) {
            self.config.terraform_path = Some(terraform_path.to_string());
        }

        Ok(())
    }
}

pub struct TerraformPlanOperation {
    config: TerraformConfig,
}

#[async_trait]
impl Operation for TerraformPlanOperation {
    fn name(&self) -> &str {
        "terraform-plan"
    }

    fn description(&self) -> &str {
        "Generate Terraform execution plan"
    }

    async fn execute(
        &self,
        collection: &crate::collection::Collection,
        environment: &crate::environment::Environment,
    ) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();

        tracing::info!(
            "Executing Terraform plan operation for collection '{}'",
            collection.name
        );

        let plugin = TerraformPlugin {
            name: "terraform".to_string(),
            version: "1.0.0".to_string(),
            config: self.config.clone(),
        };

        // Create temporary working directory
        let temp_dir = tempfile::tempdir().map_err(|e| {
            CacophonyError::Plugin(format!("Failed to create temp directory: {}", e))
        })?;
        let working_dir = temp_dir.path().to_str().unwrap();

        // Generate Terraform configuration
        let config_content = plugin.generate_terraform_config(collection, environment)?;
        let config_path = std::path::Path::new(working_dir).join("main.tf");
        std::fs::write(&config_path, config_content).map_err(|e| {
            CacophonyError::Plugin(format!("Failed to write Terraform config: {}", e))
        })?;

        // Initialize Terraform
        plugin.init_terraform(working_dir).await?;

        // Select workspace
        plugin.select_workspace(working_dir).await?;

        // Generate plan
        let plan_args = if self.config.dry_run {
            vec!["plan", "-detailed-exitcode", "-out=plan.tfplan"]
        } else {
            vec!["plan", "-detailed-exitcode", "-out=plan.tfplan"]
        };

        let plan_output = plugin
            .execute_terraform_command(&plan_args, working_dir)
            .await?;

        let duration = start_time.elapsed();

        Ok(OperationResult {
            success: true,
            message: format!(
                "Terraform plan generated for collection '{}'",
                collection.name
            ),
            details: {
                let mut details = HashMap::new();
                details.insert("plan_output".to_string(), Value::String(plan_output));
                details.insert(
                    "workspace".to_string(),
                    Value::String(
                        self.config
                            .workspace
                            .clone()
                            .unwrap_or_else(|| "default".to_string()),
                    ),
                );
                details.insert("dry_run".to_string(), Value::Bool(self.config.dry_run));
                details
            },
            duration,
        })
    }

    fn validate(
        &self,
        collection: &crate::collection::Collection,
        _environment: &crate::environment::Environment,
    ) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate Terraform configuration
        if self.config.workspace.is_none() {
            warnings.push("No Terraform workspace specified".to_string());
        }

        // Validate collection has Terraform-compatible programs
        if collection.programs.is_empty() {
            errors.push("Collection has no programs to plan".to_string());
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct TerraformApplyOperation {
    config: TerraformConfig,
}

#[async_trait]
impl Operation for TerraformApplyOperation {
    fn name(&self) -> &str {
        "terraform-apply"
    }

    fn description(&self) -> &str {
        "Apply Terraform configuration"
    }

    async fn execute(
        &self,
        collection: &crate::collection::Collection,
        environment: &crate::environment::Environment,
    ) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();

        tracing::info!(
            "Executing Terraform apply operation for collection '{}'",
            collection.name
        );

        let plugin = TerraformPlugin {
            name: "terraform".to_string(),
            version: "1.0.0".to_string(),
            config: self.config.clone(),
        };

        // Create temporary working directory
        let temp_dir = tempfile::tempdir().map_err(|e| {
            CacophonyError::Plugin(format!("Failed to create temp directory: {}", e))
        })?;
        let working_dir = temp_dir.path().to_str().unwrap();

        // Generate Terraform configuration
        let config_content = plugin.generate_terraform_config(collection, environment)?;
        let config_path = std::path::Path::new(working_dir).join("main.tf");
        std::fs::write(&config_path, config_content).map_err(|e| {
            CacophonyError::Plugin(format!("Failed to write Terraform config: {}", e))
        })?;

        // Initialize Terraform
        plugin.init_terraform(working_dir).await?;

        // Select workspace
        plugin.select_workspace(working_dir).await?;

        // Generate plan first
        let plan_args = vec!["plan", "-detailed-exitcode", "-out=plan.tfplan"];
        plugin
            .execute_terraform_command(&plan_args, working_dir)
            .await?;

        // Apply the plan
        let apply_args = if self.config.dry_run {
            vec!["apply", "-auto-approve", "plan.tfplan"]
        } else {
            vec!["apply", "-auto-approve", "plan.tfplan"]
        };

        let apply_output = plugin
            .execute_terraform_command(&apply_args, working_dir)
            .await?;

        let duration = start_time.elapsed();

        Ok(OperationResult {
            success: true,
            message: format!(
                "Terraform apply completed for collection '{}'",
                collection.name
            ),
            details: {
                let mut details = HashMap::new();
                details.insert("apply_output".to_string(), Value::String(apply_output));
                details.insert(
                    "workspace".to_string(),
                    Value::String(
                        self.config
                            .workspace
                            .clone()
                            .unwrap_or_else(|| "default".to_string()),
                    ),
                );
                details.insert("dry_run".to_string(), Value::Bool(self.config.dry_run));
                details
            },
            duration,
        })
    }

    fn validate(
        &self,
        collection: &crate::collection::Collection,
        _environment: &crate::environment::Environment,
    ) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate Terraform configuration
        if self.config.workspace.is_none() {
            warnings.push("No Terraform workspace specified".to_string());
        }

        // Validate collection has Terraform-compatible programs
        if collection.programs.is_empty() {
            errors.push("Collection has no programs to apply".to_string());
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct TerraformDestroyOperation {
    config: TerraformConfig,
}

#[async_trait]
impl Operation for TerraformDestroyOperation {
    fn name(&self) -> &str {
        "terraform-destroy"
    }

    fn description(&self) -> &str {
        "Destroy Terraform-managed infrastructure"
    }

    async fn execute(
        &self,
        collection: &crate::collection::Collection,
        environment: &crate::environment::Environment,
    ) -> Result<OperationResult> {
        let start_time = std::time::Instant::now();

        tracing::info!(
            "Executing Terraform destroy operation for collection '{}'",
            collection.name
        );

        let plugin = TerraformPlugin {
            name: "terraform".to_string(),
            version: "1.0.0".to_string(),
            config: self.config.clone(),
        };

        // Create temporary working directory
        let temp_dir = tempfile::tempdir().map_err(|e| {
            CacophonyError::Plugin(format!("Failed to create temp directory: {}", e))
        })?;
        let working_dir = temp_dir.path().to_str().unwrap();

        // Generate Terraform configuration
        let config_content = plugin.generate_terraform_config(collection, environment)?;
        let config_path = std::path::Path::new(working_dir).join("main.tf");
        std::fs::write(&config_path, config_content).map_err(|e| {
            CacophonyError::Plugin(format!("Failed to write Terraform config: {}", e))
        })?;

        // Initialize Terraform
        plugin.init_terraform(working_dir).await?;

        // Select workspace
        plugin.select_workspace(working_dir).await?;

        // Destroy infrastructure
        let destroy_args = if self.config.dry_run {
            vec!["destroy", "-auto-approve"]
        } else {
            vec!["destroy", "-auto-approve"]
        };

        let destroy_output = plugin
            .execute_terraform_command(&destroy_args, working_dir)
            .await?;

        let duration = start_time.elapsed();

        Ok(OperationResult {
            success: true,
            message: format!(
                "Terraform destroy completed for collection '{}'",
                collection.name
            ),
            details: {
                let mut details = HashMap::new();
                details.insert("destroy_output".to_string(), Value::String(destroy_output));
                details.insert(
                    "workspace".to_string(),
                    Value::String(
                        self.config
                            .workspace
                            .clone()
                            .unwrap_or_else(|| "default".to_string()),
                    ),
                );
                details.insert("dry_run".to_string(), Value::Bool(self.config.dry_run));
                details
            },
            duration,
        })
    }

    fn validate(
        &self,
        collection: &crate::collection::Collection,
        _environment: &crate::environment::Environment,
    ) -> Result<ValidationResult> {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate Terraform configuration
        if self.config.workspace.is_none() {
            warnings.push("No Terraform workspace specified".to_string());
        }

        // Validate collection has Terraform-compatible programs
        if collection.programs.is_empty() {
            errors.push("Collection has no programs to destroy".to_string());
        }

        Ok(ValidationResult { errors, warnings })
    }
}

pub struct PluginManager {
    plugins: HashMap<String, Box<dyn Plugin>>,
}

impl PluginManager {
    pub fn new() -> Self {
        let mut manager = Self {
            plugins: HashMap::new(),
        };

        // Register built-in plugins
        manager.register_plugin(Box::new(TerraformPlugin::new()));

        manager
    }

    pub fn register_plugin(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.insert(plugin.name().to_string(), plugin);
    }

    pub fn get_plugin(&self, name: &str) -> Option<&Box<dyn Plugin>> {
        self.plugins.get(name)
    }

    pub fn get_plugin_mut(&mut self, name: &str) -> Option<&mut Box<dyn Plugin>> {
        self.plugins.get_mut(name)
    }

    pub fn list_plugins(&self) -> Vec<&str> {
        self.plugins.keys().map(|s| s.as_str()).collect()
    }

    pub fn get_operations(&self) -> Vec<Box<dyn Operation>> {
        let mut operations = Vec::new();

        for plugin in self.plugins.values() {
            operations.extend(plugin.operations());
        }

        operations
    }

    pub fn configure_plugin(&mut self, name: &str, config: &Value) -> Result<()> {
        let plugin = self
            .get_plugin_mut(name)
            .ok_or_else(|| CacophonyError::NotFound(format!("Plugin '{}' not found", name)))?;

        plugin.configure(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collection::{Collection, LigatureProgram};
    use crate::config::{CollectionConfig, EnvironmentConfig};
    use crate::environment::Environment;
    use serde_json::json;

    fn create_test_collection(name: &str, program_names: Vec<&str>) -> Collection {
        let programs = program_names
            .into_iter()
            .map(|name| LigatureProgram {
                name: name.to_string(),
                content: format!("test content for {}", name),
                path: std::path::PathBuf::from(format!("{}.lig", name)),
            })
            .collect();

        Collection {
            name: name.to_string(),
            config: CollectionConfig {
                name: name.to_string(),
                description: None,
                dependencies: vec![],
                operations: vec![],
                environments: vec![],
                config: None,
            },
            programs,
            dependencies: vec![],
            variables: HashMap::new(),
        }
    }

    fn create_test_environment(name: &str) -> Environment {
        Environment {
            name: name.to_string(),
            config: EnvironmentConfig {
                name: name.to_string(),
                description: None,
                variables: HashMap::new(),
                plugins: vec![],
                overrides: None,
            },
            variables: HashMap::new(),
            plugins: vec![],
        }
    }

    #[tokio::test]
    async fn test_terraform_plugin_creation() {
        let plugin = TerraformPlugin::new();
        assert_eq!(plugin.name(), "terraform");
        assert_eq!(plugin.version(), "1.0.0");
        assert_eq!(
            plugin.description(),
            "Terraform infrastructure management plugin"
        );
    }

    #[tokio::test]
    async fn test_terraform_plugin_configuration() {
        let mut plugin = TerraformPlugin::new();
        let config = json!({
            "workspace": "test-workspace",
            "backend": "s3",
            "dry_run": true,
            "timeout": 1200,
            "retries": 5,
            "terraform_path": "/usr/local/bin/terraform",
            "variables": {
                "environment": "test",
                "instance_count": "2"
            }
        });

        let result = plugin.configure(&config);
        assert!(result.is_ok());

        assert_eq!(plugin.config.workspace, Some("test-workspace".to_string()));
        assert_eq!(plugin.config.backend, Some("s3".to_string()));
        assert_eq!(plugin.config.dry_run, true);
        assert_eq!(plugin.config.timeout, 1200);
        assert_eq!(plugin.config.retries, 5);
        assert_eq!(
            plugin.config.terraform_path,
            Some("/usr/local/bin/terraform".to_string())
        );
        assert_eq!(
            plugin.config.variables.get("environment"),
            Some(&"test".to_string())
        );
        assert_eq!(
            plugin.config.variables.get("instance_count"),
            Some(&"2".to_string())
        );
    }

    #[tokio::test]
    async fn test_terraform_plugin_operations() {
        let plugin = TerraformPlugin::new();
        let operations = plugin.operations();

        assert_eq!(operations.len(), 3);

        let operation_names: Vec<&str> = operations.iter().map(|op| op.name()).collect();
        assert!(operation_names.contains(&"terraform-plan"));
        assert!(operation_names.contains(&"terraform-apply"));
        assert!(operation_names.contains(&"terraform-destroy"));
    }

    #[tokio::test]
    async fn test_terraform_plan_operation() {
        let operation = TerraformPlanOperation {
            config: TerraformConfig {
                workspace: Some("test".to_string()),
                dry_run: true,
                ..Default::default()
            },
        };

        let collection = create_test_collection("test-collection", vec!["test-program"]);
        let environment = create_test_environment("test-env");

        let validation = operation.validate(&collection, &environment).unwrap();
        assert!(validation.is_valid());
    }

    #[tokio::test]
    async fn test_terraform_apply_operation() {
        let operation = TerraformApplyOperation {
            config: TerraformConfig {
                workspace: Some("test".to_string()),
                dry_run: true,
                ..Default::default()
            },
        };

        let collection = create_test_collection("test-collection", vec!["test-program"]);
        let environment = create_test_environment("test-env");

        let validation = operation.validate(&collection, &environment).unwrap();
        assert!(validation.is_valid());
    }

    #[tokio::test]
    async fn test_terraform_destroy_operation() {
        let operation = TerraformDestroyOperation {
            config: TerraformConfig {
                workspace: Some("test".to_string()),
                dry_run: true,
                ..Default::default()
            },
        };

        let collection = create_test_collection("test-collection", vec!["test-program"]);
        let environment = create_test_environment("test-env");

        let validation = operation.validate(&collection, &environment).unwrap();
        assert!(validation.is_valid());
    }

    #[tokio::test]
    async fn test_plugin_manager() {
        let mut manager = PluginManager::new();

        // Test that built-in plugins are registered
        let plugins = manager.list_plugins();
        assert!(plugins.contains(&"terraform"));

        // Test getting a plugin
        let terraform_plugin = manager.get_plugin("terraform");
        assert!(terraform_plugin.is_some());
        assert_eq!(terraform_plugin.unwrap().name(), "terraform");

        // Test getting operations
        let operations = manager.get_operations();
        assert!(!operations.is_empty());

        let operation_names: Vec<&str> = operations.iter().map(|op| op.name()).collect();
        assert!(operation_names.contains(&"terraform-plan"));
    }

    #[tokio::test]
    async fn test_terraform_config_generation() {
        let plugin = TerraformPlugin {
            name: "terraform".to_string(),
            version: "1.0.0".to_string(),
            config: TerraformConfig {
                workspace: Some("test".to_string()),
                ..Default::default()
            },
        };

        let collection = create_test_collection("test-collection", vec!["test-app"]);
        let mut environment = create_test_environment("test-env");
        environment
            .variables
            .insert("AWS_REGION".to_string(), json!("us-west-2"));
        environment
            .variables
            .insert("ENVIRONMENT".to_string(), json!("test"));

        let config = plugin
            .generate_terraform_config(&collection, &environment)
            .unwrap();

        // Verify the generated config contains expected elements
        assert!(config.contains("terraform {"));
        assert!(config.contains("provider \"aws\" {"));
        assert!(config.contains("resource \"aws_instance\""));
        assert!(config.contains("variable \"environment\""));
        assert!(config.contains("variable \"AWS_REGION\""));
    }

    #[tokio::test]
    async fn test_validation_with_empty_collection() {
        let operation = TerraformPlanOperation {
            config: TerraformConfig::default(),
        };

        let collection = create_test_collection("empty-collection", vec![]);
        let environment = create_test_environment("test-env");

        let validation = operation.validate(&collection, &environment).unwrap();
        assert!(!validation.is_valid());
        assert!(validation
            .errors
            .contains(&"Collection has no programs to plan".to_string()));
    }
}
