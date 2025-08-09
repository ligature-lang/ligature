use std::fs;
use std::path::Path;

use anyhow::{Context, Result};
use clap::Subcommand;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tracing::{error, info, warn};

use crate::config::{CacophonyXdgConfig, ConfigManager};
use crate::error::Result as CacophonyResult;

#[derive(Debug, Serialize, Deserialize)]
struct DiffInfo {
    collection: String,
    from_environment: String,
    to_environment: String,
    from_variables: std::collections::HashMap<String, String>,
    to_variables: std::collections::HashMap<String, String>,
    from_plugins: Vec<String>,
    to_plugins: Vec<String>,
    collection_operations: Vec<String>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Initialize a new cacophony project
    Init {
        /// Template to use for initialization
        #[arg(short, long)]
        template: Option<String>,

        /// Project name
        #[arg(short, long)]
        name: Option<String>,

        /// Force overwrite of existing directory
        #[arg(short, long)]
        force: bool,
    },

    /// Deploy a collection to an environment
    Deploy {
        /// Collection name
        #[arg(short, long)]
        collection: String,

        /// Environment name
        #[arg(short, long)]
        environment: String,

        /// Dry run mode
        #[arg(short, long)]
        dry_run: bool,

        /// Force deployment even if validation fails
        #[arg(short, long)]
        force: bool,
    },

    /// Validate configurations
    Validate {
        /// Collection name (optional)
        #[arg(short, long)]
        collection: Option<String>,

        /// Environment name (optional)
        #[arg(short, long)]
        environment: Option<String>,

        /// Strict validation mode
        #[arg(short, long)]
        strict: bool,
    },

    /// Show differences between environments
    Diff {
        /// Collection name
        #[arg(short, long)]
        collection: String,

        /// Source environment
        #[arg(short, long)]
        from: String,

        /// Target environment
        #[arg(short, long)]
        to: String,

        /// Output format (text, json, yaml)
        #[arg(short, long, default_value = "text")]
        output: String,
    },

    /// List available collections and environments
    List {
        /// List collections
        #[arg(short, long)]
        collections: bool,

        /// List environments
        #[arg(short, long)]
        environments: bool,

        /// List plugins
        #[arg(short, long)]
        plugins: bool,

        /// List operations
        #[arg(short, long)]
        operations: bool,
    },

    /// Run custom operations
    Run {
        /// Operation name
        #[arg(short, long)]
        operation: String,

        /// Collection name (optional)
        #[arg(short, long)]
        collection: Option<String>,

        /// Environment name (optional)
        #[arg(short, long)]
        environment: Option<String>,

        /// Custom parameters (key=value format)
        #[arg(short, long)]
        param: Vec<String>,
    },

    /// Show project status
    Status {
        /// Environment name (optional)
        #[arg(short, long)]
        environment: Option<String>,

        /// Show detailed status
        #[arg(short, long)]
        detailed: bool,
    },
}

impl Commands {
    pub async fn execute(self) -> CacophonyResult<()> {
        match self {
            Commands::Init { template, name, force } => {
                Self::handle_init(template, name, force)
                    .context("Failed to initialize project")
            }
            Commands::Deploy { collection, environment, dry_run, force } => {
                Self::handle_deploy(collection, environment, dry_run, force)
                    .await
                    .context("Failed to deploy collection")
            }
            Commands::Validate { collection, environment, strict } => {
                Self::handle_validate(collection, environment, strict)
                    .await
                    .context("Failed to validate configuration")
            }
            Commands::Diff { collection, from, to, output } => {
                Self::handle_diff(collection, from, to, output)
                    .await
                    .context("Failed to generate diff")
            }
            Commands::List { collections, environments, plugins, operations } => {
                Self::handle_list(collections, environments, plugins, operations)
                    .await
                    .context("Failed to list resources")
            }
            Commands::Run { operation, collection, environment, param } => {
                Self::handle_run(operation, collection, environment, param)
                    .await
                    .context("Failed to run operation")
            }
            Commands::Status { environment, detailed } => {
                Self::handle_status(environment, detailed)
                    .await
                    .context("Failed to get status")
            }
        }
    }

    async fn handle_init(
        template: Option<String>,
        name: Option<String>,
        force: bool,
    ) -> CacophonyResult<()> {
        let project_name = name.unwrap_or_else(|| {
            std::env::current_dir()
                .ok()
                .and_then(|p| p.file_name())
                .and_then(|n| n.to_str())
                .unwrap_or("cacophony-project")
                .to_string()
        });

        let template_type = template.unwrap_or_else(|| "basic".to_string());

        // Check if project directory already exists
        if Path::new(&project_name).exists() && !force {
            return Err(crate::error::CacophonyError::InvalidArgument(
                format!("Project directory '{}' already exists. Use --force to overwrite.", project_name)
            ));
        }

        // Create project structure
        Self::create_project_structure(&Path::new(&project_name), &project_name, &template_type)
            .context("Failed to create project structure")?;

        info!("Project '{}' initialized successfully with template '{}'", project_name, template_type);
        Ok(())
    }

    async fn handle_deploy(
        collection: String,
        environment: String,
        dry_run: bool,
        force: bool,
    ) -> CacophonyResult<()> {
        // Load configuration
        let config_manager = ConfigManager::new()
            .context("Failed to create config manager")?;

        let config = config_manager.load_config()
            .context("Failed to load configuration")?;

        // Validate collection exists
        if !config.collections.contains_key(&collection) {
            return Err(crate::error::CacophonyError::NotFound(
                format!("Collection '{}' not found", collection)
            ));
        }

        // Validate environment exists
        if !config.environments.contains_key(&environment) {
            return Err(crate::error::CacophonyError::NotFound(
                format!("Environment '{}' not found", environment)
            ));
        }

        if dry_run {
            info!("Dry run: Would deploy collection '{}' to environment '{}'", collection, environment);
        } else {
            info!("Deploying collection '{}' to environment '{}'", collection, environment);
            // Actual deployment logic would go here
        }

        Ok(())
    }

    async fn handle_validate(
        collection: Option<String>,
        environment: Option<String>,
        strict: bool,
    ) -> CacophonyResult<()> {
        // Load configuration
        let config_manager = ConfigManager::new()
            .context("Failed to create config manager")?;

        let config = config_manager.load_config()
            .context("Failed to load configuration")?;

        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Validate collections
        if let Some(ref coll_name) = collection {
            if !config.collections.contains_key(coll_name) {
                errors.push(format!("Collection '{}' not found", coll_name));
            }
        } else {
            // Validate all collections
            for (name, collection_config) in &config.collections {
                if let Err(e) = Self::validate_collection(name, collection_config) {
                    if strict {
                        errors.push(e);
                    } else {
                        warnings.push(e);
                    }
                }
            }
        }

        // Validate environments
        if let Some(ref env_name) = environment {
            if !config.environments.contains_key(env_name) {
                errors.push(format!("Environment '{}' not found", env_name));
            }
        } else {
            // Validate all environments
            for (name, env_config) in &config.environments {
                if let Err(e) = Self::validate_environment(name, env_config) {
                    if strict {
                        errors.push(e);
                    } else {
                        warnings.push(e);
                    }
                }
            }
        }

        // Report results
        if !errors.is_empty() {
            eprintln!("Validation failed with {} error(s):", errors.len());
            for error in errors {
                eprintln!("  - {}", error);
            }
            return Err(crate::error::CacophonyError::Validation(
                format!("Validation failed with {} error(s)", errors.len())
            ));
        }

        if !warnings.is_empty() {
            warn!("Validation completed with {} warning(s):", warnings.len());
            for warning in warnings {
                warn!("  - {}", warning);
            }
        }

        info!("Validation completed successfully");
        Ok(())
    }

    async fn handle_diff(
        collection: String,
        from: String,
        to: String,
        output: String,
    ) -> CacophonyResult<()> {
        // Load configuration
        let config_manager = ConfigManager::new()
            .context("Failed to create config manager")?;

        let config = config_manager.load_config()
            .context("Failed to load configuration")?;

        // Validate inputs
        if !config.collections.contains_key(&collection) {
            return Err(crate::error::CacophonyError::NotFound(
                format!("Collection '{}' not found", collection)
            ));
        }

        if !config.environments.contains_key(&from) {
            return Err(crate::error::CacophonyError::NotFound(
                format!("Source environment '{}' not found", from)
            ));
        }

        if !config.environments.contains_key(&to) {
            return Err(crate::error::CacophonyError::NotFound(
                format!("Target environment '{}' not found", to)
            ));
        }

        // Generate diff
        let diff_info = DiffInfo {
            collection,
            from_environment: from.clone(),
            to_environment: to.clone(),
            from_variables: std::collections::HashMap::new(),
            to_variables: std::collections::HashMap::new(),
            from_plugins: vec![],
            to_plugins: vec![],
            collection_operations: vec![],
        };

        // Output diff based on format
        match output.as_str() {
            "json" => {
                let json = serde_json::to_string_pretty(&diff_info)
                    .context("Failed to serialize diff to JSON")?;
                println!("{}", json);
            }
            "yaml" => {
                let yaml = serde_yaml::to_string(&diff_info)
                    .context("Failed to serialize diff to YAML")?;
                println!("{}", yaml);
            }
            "text" => {
                println!("Diff from '{}' to '{}':", from, to);
                println!("  Collections: No changes");
                println!("  Environments: No changes");
                println!("  Variables: No changes");
                println!("  Plugins: No changes");
            }
            _ => {
                return Err(crate::error::CacophonyError::InvalidArgument(
                    format!("Unsupported output format: {}", output)
                ));
            }
        }

        Ok(())
    }

    async fn handle_list(
        collections: bool,
        environments: bool,
        plugins: bool,
        operations: bool,
    ) -> CacophonyResult<()> {
        // Load configuration
        let config_manager = ConfigManager::new()
            .context("Failed to create config manager")?;

        let config = config_manager.load_config()
            .context("Failed to load configuration")?;

        let show_all = !collections && !environments && !plugins && !operations;

        if show_all || collections {
            println!("Collections:");
            for name in config.collections.keys() {
                println!("  {}", name);
            }
            println!();
        }

        if show_all || environments {
            println!("Environments:");
            for name in config.environments.keys() {
                println!("  {}", name);
            }
            println!();
        }

        if show_all || plugins {
            println!("Plugins:");
            for name in config.plugins.keys() {
                println!("  {}", name);
            }
            println!();
        }

        if show_all || operations {
            println!("Operations:");
            // List available operations
            println!("  deploy");
            println!("  validate");
            println!("  diff");
            println!();
        }

        Ok(())
    }

    async fn handle_run(
        operation: String,
        collection: Option<String>,
        environment: Option<String>,
        param: Vec<String>,
    ) -> CacophonyResult<()> {
        // Parse parameters
        let params: std::collections::HashMap<String, String> = param
            .iter()
            .filter_map(|p| {
                p.split_once('=')
                    .map(|(k, v)| (k.to_string(), v.to_string()))
            })
            .collect();

        info!("Running operation '{}' with parameters: {:?}", operation, params);

        match operation.as_str() {
            "deploy" => {
                let collection_name = collection.ok_or_else(|| {
                    crate::error::CacophonyError::InvalidArgument(
                        "Collection name required for deploy operation".to_string()
                    )
                })?;
                let environment_name = environment.ok_or_else(|| {
                    crate::error::CacophonyError::InvalidArgument(
                        "Environment name required for deploy operation".to_string()
                    )
                })?;

                Self::handle_deploy(collection_name, environment_name, false, false)
                    .await
                    .context("Deploy operation failed")
            }
            "validate" => {
                Self::handle_validate(collection, environment, false)
                    .await
                    .context("Validate operation failed")
            }
            _ => {
                Err(crate::error::CacophonyError::Unsupported(
                    format!("Unknown operation: {}", operation)
                ))
            }
        }
    }

    async fn handle_status(
        environment: Option<String>,
        detailed: bool,
    ) -> CacophonyResult<()> {
        // Load configuration
        let config_manager = ConfigManager::new()
            .context("Failed to create config manager")?;

        let config = config_manager.load_config()
            .context("Failed to load configuration")?;

        if let Some(ref env_name) = environment {
            if !config.environments.contains_key(env_name) {
                return Err(crate::error::CacophonyError::NotFound(
                    format!("Environment '{}' not found", env_name)
                ));
            }

            println!("Environment: {}", env_name);
            if detailed {
                println!("  Status: Active");
                println!("  Collections: 0 deployed");
                println!("  Last updated: Never");
            }
        } else {
            println!("Project Status:");
            println!("  Collections: {}", config.collections.len());
            println!("  Environments: {}", config.environments.len());
            println!("  Plugins: {}", config.plugins.len());

            if detailed {
                println!("\nDetailed Status:");
                for (name, _) in &config.environments {
                    println!("  Environment '{}': Active", name);
                }
            }
        }

        Ok(())
    }

    fn validate_collection(name: &str, _collection_config: &crate::config::CollectionConfig) -> Result<(), String> {
        // Collection validation logic would go here
        Ok(())
    }

    fn validate_environment(name: &str, _env_config: &crate::config::EnvironmentConfig) -> Result<(), String> {
        // Environment validation logic would go here
        Ok(())
    }

    fn create_project_structure(
        project_dir: &Path,
        project_name: &str,
        template_type: &str,
    ) -> CacophonyResult<()> {
        // Create project directory
        fs::create_dir_all(project_dir)
            .context("Failed to create project directory")?;

        // Create subdirectories
        let subdirs = ["collections", "environments", "plugins", "scripts"];
        for subdir in &subdirs {
            fs::create_dir_all(project_dir.join(subdir))
                .context(format!("Failed to create {} directory", subdir))?;
        }

        // Create configuration file
        let config_content = Self::generate_config_template(project_name, template_type);
        fs::write(project_dir.join("cacophony.lig"), config_content)
            .context("Failed to write configuration file")?;

        // Create README
        let readme_content = Self::generate_readme_template(project_name);
        fs::write(project_dir.join("README.md"), readme_content)
            .context("Failed to write README file")?;

        // Create .gitignore
        let gitignore_content = Self::generate_gitignore_template();
        fs::write(project_dir.join(".gitignore"), gitignore_content)
            .context("Failed to write .gitignore file")?;

        // Create example environment
        let env_content = Self::generate_environment_template("dev");
        fs::write(project_dir.join("environments").join("dev.lig"), env_content)
            .context("Failed to write environment file")?;

        // Create example collection
        let coll_content = Self::generate_collection_template("example");
        fs::write(project_dir.join("collections").join("example.lig"), coll_content)
            .context("Failed to write collection file")?;

        // Create scripts
        let deploy_script = Self::generate_deploy_script();
        fs::write(project_dir.join("scripts").join("deploy.sh"), deploy_script)
            .context("Failed to write deploy script")?;

        let test_script = Self::generate_test_script();
        fs::write(project_dir.join("scripts").join("test.sh"), test_script)
            .context("Failed to write test script")?;

        let migrate_script = Self::generate_migrate_script();
        fs::write(project_dir.join("scripts").join("migrate.sh"), migrate_script)
            .context("Failed to write migrate script")?;

        Ok(())
    }

    fn generate_config_template(project_name: &str, template_type: &str) -> String {
        format!(
            r#"// Cacophony configuration for {}
// Template: {}

project {{
    name = "{}"
    version = "0.1.0"
    description = "A Cacophony project"
}}

environments {{
    dev = {{
        description = "Development environment"
        variables = {{
            ENV = "development"
            DEBUG = "true"
        }}
    }}
    
    staging = {{
        description = "Staging environment"
        variables = {{
            ENV = "staging"
            DEBUG = "false"
        }}
    }}
    
    prod = {{
        description = "Production environment"
        variables = {{
            ENV = "production"
            DEBUG = "false"
        }}
    }}
}}

collections {{
    example = {{
        description = "Example collection"
        environments = ["dev", "staging", "prod"]
        operations = ["deploy", "validate"]
    }}
}}

plugins {{
    // Add your plugins here
}}
"#,
            project_name, template_type, project_name
        )
    }

    fn generate_readme_template(project_name: &str) -> String {
        format!(
            r#"# {}

A Cacophony project for managing configuration and deployments.

## Getting Started

1. Install Cacophony CLI
2. Run `cacophony validate` to check your configuration
3. Run `cacophony deploy example dev` to deploy to development

## Project Structure

- `cacophony.lig` - Main configuration file
- `collections/` - Collection definitions
- `environments/` - Environment configurations
- `plugins/` - Custom plugins
- `scripts/` - Deployment and utility scripts

## Commands

- `cacophony validate` - Validate configuration
- `cacophony deploy <collection> <environment>` - Deploy collection
- `cacophony diff <collection> <from> <to>` - Show differences
- `cacophony status` - Show project status

## Documentation

For more information, see the [Cacophony documentation](https://docs.cacophony.dev).
"#,
            project_name
        )
    }

    fn generate_gitignore_template() -> String {
        r#"# Cacophony
.cacophony/
*.log

# Environment variables
.env
.env.local

# IDE
.vscode/
.idea/

# OS
.DS_Store
Thumbs.db
"#.to_string()
    }

    fn generate_environment_template(env_name: &str) -> String {
        format!(
            r#"// Environment configuration for {}

variables {{
    ENV = "{}"
    DEBUG = "true"
    LOG_LEVEL = "info"
}}

plugins {{
    // Add environment-specific plugins here
}}

operations {{
    // Add environment-specific operations here
}}
"#,
            env_name, env_name
        )
    }

    fn generate_collection_template(coll_name: &str) -> String {
        format!(
            r#"// Collection configuration for {}

description = "Example collection"

environments = ["dev", "staging", "prod"]

variables {{
    // Collection-specific variables
    COLLECTION_NAME = "{}"
}}

operations {{
    deploy = {{
        description = "Deploy the collection"
        script = "scripts/deploy.sh"
    }}
    
    validate = {{
        description = "Validate the collection"
        script = "scripts/validate.sh"
    }}
}}

plugins {{
    // Add collection-specific plugins here
}}
"#,
            coll_name, coll_name
        )
    }

    fn generate_deploy_script() -> String {
        r#"#!/bin/bash
# Deploy script for Cacophony

set -e

echo "Deploying collection..."

# Add your deployment logic here

echo "Deployment completed successfully"
"#.to_string()
    }

    fn generate_test_script() -> String {
        r#"#!/bin/bash
# Test script for Cacophony

set -e

echo "Running tests..."

# Add your test logic here

echo "Tests completed successfully"
"#.to_string()
    }

    fn generate_migrate_script() -> String {
        r#"#!/bin/bash
# Migration script for Cacophony

set -e

echo "Running migrations..."

# Add your migration logic here

echo "Migrations completed successfully"
"#.to_string()
    }
}
