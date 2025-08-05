use clap::Subcommand;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;
use tracing::{error, info, warn};

use crate::config::ConfigManager;
use crate::error::Result;

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
    pub async fn execute(self) -> Result<()> {
        println!("DEBUG: CLI execute called");
        // Load configuration using XDG
        println!("DEBUG: Creating ConfigManager with XDG");
        let config_manager = ConfigManager::with_xdg().await?;
        println!("DEBUG: ConfigManager created successfully");

        match self {
            Commands::Init {
                template,
                name,
                force,
            } => {
                info!("Initializing new cacophony project");

                // Get project name from argument or prompt
                let project_name = name.unwrap_or_else(|| {
                    // In a real implementation, you'd prompt the user
                    "my-cacophony-project".to_string()
                });

                // Get template type
                let template_type = template.unwrap_or_else(|| "basic".to_string());

                // Create project directory
                let project_dir = std::env::current_dir()?.join(&project_name);

                if project_dir.exists() && !force {
                    return Err(crate::error::CacophonyError::Internal(format!(
                        "Project directory '{}' already exists. Use --force to overwrite.",
                        project_dir.display()
                    )));
                }

                // Create project structure
                Self::create_project_structure(&project_dir, &project_name, &template_type)?;

                info!("Project created successfully at: {}", project_dir.display());
                info!("Next steps:");
                info!("  1. cd {}", project_name);
                info!("  2. cacophony list");
                info!("  3. Edit cacophony.lig to configure your project");

                Ok(())
            }

            Commands::Deploy {
                collection,
                environment,
                dry_run,
                force,
            } => {
                info!(
                    "Deploying collection '{}' to environment '{}'",
                    collection, environment
                );

                // Validate the configuration first
                let validation_result = config_manager.validate()?;
                if !validation_result.errors.is_empty() {
                    error!("Configuration validation failed:");
                    for err in &validation_result.errors {
                        error!("  - {}", err);
                    }
                    return Err(crate::error::CacophonyError::Config(
                        "Configuration validation failed".to_string(),
                    ));
                }

                // Check if collection exists
                let config = config_manager.get_config();
                let collection_config = config.collections.get(&collection).ok_or_else(|| {
                    crate::error::CacophonyError::Collection(format!(
                        "Collection '{}' not found",
                        collection
                    ))
                })?;

                // Check if environment exists
                let env_config = config.environments.get(&environment).ok_or_else(|| {
                    crate::error::CacophonyError::Environment(format!(
                        "Environment '{}' not found",
                        environment
                    ))
                })?;

                // Check if collection supports this environment
                if !collection_config.environments.contains(&environment) {
                    return Err(crate::error::CacophonyError::Config(format!(
                        "Collection '{}' does not support environment '{}'",
                        collection, environment
                    )));
                }

                // Check dependencies
                for dep in &collection_config.dependencies {
                    if dep != "none" && !config.collections.contains_key(dep) {
                        return Err(crate::error::CacophonyError::Config(format!(
                            "Collection '{}' depends on '{}' which is not defined",
                            collection, dep
                        )));
                    }
                }

                info!(
                    "✅ Collection '{}' validated for deployment to '{}'",
                    collection, environment
                );

                if dry_run {
                    info!(
                        "🔍 DRY RUN: Would deploy collection '{}' to environment '{}'",
                        collection, environment
                    );
                    info!(
                        "   Collection: {}",
                        collection_config
                            .description
                            .as_deref()
                            .unwrap_or("No description")
                    );
                    info!(
                        "   Environment: {}",
                        env_config
                            .description
                            .as_deref()
                            .unwrap_or("No description")
                    );
                    info!("   Operations: {:?}", collection_config.operations);
                    info!("   Dependencies: {:?}", collection_config.dependencies);
                    info!("   Environment variables: {:?}", env_config.variables);
                    return Ok(());
                }

                // Execute deployment operations
                info!(
                    "🚀 Starting deployment of collection '{}' to environment '{}'",
                    collection, environment
                );

                for operation_name in &collection_config.operations {
                    if let Some(operation_config) = config.operations.get(operation_name) {
                        info!("  📋 Executing operation: {}", operation_name);

                        // Check if operation script exists
                        if let Some(script) = &operation_config.script {
                            let script_path = Path::new(script);
                            if !script_path.exists() {
                                warn!("  ⚠️  Operation script '{}' not found, skipping", script);
                                continue;
                            }

                            // Execute the operation script
                            let output = std::process::Command::new("bash")
                                .arg(script)
                                .arg("--environment")
                                .arg(&environment)
                                .arg("--collection")
                                .arg(&collection)
                                .output();

                            match output {
                                Ok(output) => {
                                    if output.status.success() {
                                        info!(
                                            "  ✅ Operation '{}' completed successfully",
                                            operation_name
                                        );
                                        if !output.stdout.is_empty() {
                                            info!(
                                                "  📄 Output: {}",
                                                String::from_utf8_lossy(&output.stdout)
                                            );
                                        }
                                    } else {
                                        error!("  ❌ Operation '{}' failed", operation_name);
                                        if !output.stderr.is_empty() {
                                            error!(
                                                "  📄 Error: {}",
                                                String::from_utf8_lossy(&output.stderr)
                                            );
                                        }
                                        if !force {
                                            return Err(crate::error::CacophonyError::Operation(
                                                format!("Operation '{}' failed", operation_name),
                                            ));
                                        }
                                    }
                                }
                                Err(e) => {
                                    error!(
                                        "  ❌ Failed to execute operation '{}': {}",
                                        operation_name, e
                                    );
                                    if !force {
                                        return Err(crate::error::CacophonyError::Operation(
                                            format!(
                                                "Failed to execute operation '{}': {}",
                                                operation_name, e
                                            ),
                                        ));
                                    }
                                }
                            }
                        } else {
                            warn!(
                                "  ⚠️  Operation '{}' has no script defined, skipping",
                                operation_name
                            );
                        }
                    } else {
                        warn!(
                            "  ⚠️  Operation '{}' not defined in configuration",
                            operation_name
                        );
                    }
                }

                info!(
                    "✅ Deployment of collection '{}' to environment '{}' completed",
                    collection, environment
                );
                Ok(())
            }

            Commands::Validate {
                collection,
                environment,
                strict,
            } => {
                info!("Validating configuration");

                // Use the existing validate method from ConfigManager
                let validation_result = config_manager.validate()?;

                let mut errors = validation_result.errors;
                let mut warnings = validation_result.warnings;

                // Additional validation for specific collection/environment if provided
                let config = config_manager.get_config();

                // Filter by specific collection if provided
                if let Some(coll_name) = collection {
                    if !config.collections.contains_key(&coll_name) {
                        errors.push(format!("Collection '{}' not found", coll_name));
                    } else {
                        info!("Validating collection: {}", coll_name);
                        // Collection-specific validation could be added here
                    }
                }

                // Filter by specific environment if provided
                if let Some(env_name) = environment {
                    if !config.environments.contains_key(&env_name) {
                        errors.push(format!("Environment '{}' not found", env_name));
                    } else {
                        info!("Validating environment: {}", env_name);
                        // Environment-specific validation could be added here
                    }
                }

                // Additional strict mode checks
                if strict {
                    info!("Strict validation mode enabled");

                    // Check for required variables in strict mode
                    for (env_name, env_config) in &config.environments {
                        let required_vars = ["DATABASE_URL", "API_BASE_URL"];
                        for var in &required_vars {
                            if !env_config.variables.contains_key(*var) {
                                warnings.push(format!(
                                    "Environment '{}' missing recommended variable: {}",
                                    env_name, var
                                ));
                            }
                        }
                    }

                    // Check for undefined operations
                    for (coll_name, coll_config) in &config.collections {
                        for op in &coll_config.operations {
                            if !config.operations.contains_key(op) {
                                warnings.push(format!(
                                    "Collection '{}' references undefined operation: {}",
                                    coll_name, op
                                ));
                            }
                        }
                    }

                    // Check if scripts exist
                    for (op_name, op_config) in &config.operations {
                        if let Some(script_path) = &op_config.script {
                            let script_file = std::env::current_dir()?.join(script_path);
                            if !script_file.exists() {
                                warnings.push(format!(
                                    "Operation '{}' script not found: {}",
                                    op_name, script_path
                                ));
                            }
                        }
                    }
                }

                // Report results
                if errors.is_empty() && warnings.is_empty() {
                    info!("✅ Configuration validation passed");
                    if strict {
                        info!("✅ Strict validation passed");
                    }
                } else {
                    if !errors.is_empty() {
                        error!(
                            "❌ Configuration validation failed with {} errors:",
                            errors.len()
                        );
                        for error in &errors {
                            error!("  - {}", error);
                        }
                    }

                    if !warnings.is_empty() {
                        warn!(
                            "⚠️  Configuration validation completed with {} warnings:",
                            warnings.len()
                        );
                        for warning in &warnings {
                            warn!("  - {}", warning);
                        }
                    }

                    if !errors.is_empty() {
                        return Err(crate::error::CacophonyError::Internal(format!(
                            "Configuration validation failed with {} errors",
                            errors.len()
                        )));
                    }
                }

                Ok(())
            }

            Commands::Diff {
                collection,
                from,
                to,
                output,
            } => {
                info!(
                    "Showing differences for collection '{}' from '{}' to '{}'",
                    collection, from, to
                );

                // Get the configuration
                let config = config_manager.get_config();

                // Check if collection exists
                let collection_config = config.collections.get(&collection).ok_or_else(|| {
                    crate::error::CacophonyError::Collection(format!(
                        "Collection '{}' not found",
                        collection
                    ))
                })?;

                // Check if environments exist
                let from_env = config.environments.get(&from).ok_or_else(|| {
                    crate::error::CacophonyError::Environment(format!(
                        "Environment '{}' not found",
                        from
                    ))
                })?;

                let to_env = config.environments.get(&to).ok_or_else(|| {
                    crate::error::CacophonyError::Environment(format!(
                        "Environment '{}' not found",
                        to
                    ))
                })?;

                // Check if collection supports both environments
                if !collection_config.environments.contains(&from) {
                    return Err(crate::error::CacophonyError::Config(format!(
                        "Collection '{}' does not support environment '{}'",
                        collection, from
                    )));
                }

                if !collection_config.environments.contains(&to) {
                    return Err(crate::error::CacophonyError::Config(format!(
                        "Collection '{}' does not support environment '{}'",
                        collection, to
                    )));
                }

                // Generate diff information
                let diff_info = DiffInfo {
                    collection: collection.clone(),
                    from_environment: from.clone(),
                    to_environment: to.clone(),
                    from_variables: from_env.variables.clone(),
                    to_variables: to_env.variables.clone(),
                    from_plugins: from_env.plugins.clone(),
                    to_plugins: to_env.plugins.clone(),
                    collection_operations: collection_config.operations.clone(),
                };

                // Output in requested format
                match output.as_str() {
                    "json" => {
                        let json = serde_json::to_string_pretty(&diff_info)
                            .map_err(|e| crate::error::CacophonyError::Json(e))?;
                        println!("{}", json);
                    }
                    "yaml" => {
                        let yaml = serde_yaml::to_string(&diff_info)
                            .map_err(|e| crate::error::CacophonyError::Yaml(e.to_string()))?;
                        println!("{}", yaml);
                    }
                    "text" | _ => {
                        println!("📊 Environment Diff for Collection: {}", collection);
                        println!(
                            "   From: {} ({})",
                            from,
                            from_env.description.as_deref().unwrap_or("No description")
                        );
                        println!(
                            "   To:   {} ({})",
                            to,
                            to_env.description.as_deref().unwrap_or("No description")
                        );
                        println!();

                        // Variables diff
                        println!("🔧 Environment Variables:");
                        let mut all_keys: std::collections::HashSet<_> =
                            from_env.variables.keys().collect();
                        all_keys.extend(to_env.variables.keys());

                        for key in all_keys.iter().sorted() {
                            let from_val = from_env.variables.get(*key);
                            let to_val = to_env.variables.get(*key);

                            match (from_val, to_val) {
                                (Some(f), Some(t)) if f == t => {
                                    println!("   {}: {} (unchanged)", key, f);
                                }
                                (Some(f), Some(t)) => {
                                    println!("   {}: {} → {}", key, f, t);
                                }
                                (Some(f), None) => {
                                    println!("   {}: {} → <removed>", key, f);
                                }
                                (None, Some(t)) => {
                                    println!("   {}: <added> → {}", key, t);
                                }
                                (None, None) => unreachable!(),
                            }
                        }
                        println!();

                        // Plugins diff
                        println!("🔌 Plugins:");
                        let mut all_plugins: std::collections::HashSet<_> =
                            from_env.plugins.iter().collect();
                        all_plugins.extend(to_env.plugins.iter());

                        for plugin in all_plugins.iter().sorted() {
                            let from_has = from_env.plugins.contains(plugin);
                            let to_has = to_env.plugins.contains(plugin);

                            match (from_has, to_has) {
                                (true, true) => {
                                    println!("   {}: ✓ (unchanged)", plugin);
                                }
                                (true, false) => {
                                    println!("   {}: ✓ → ✗ (removed)", plugin);
                                }
                                (false, true) => {
                                    println!("   {}: ✗ → ✓ (added)", plugin);
                                }
                                (false, false) => unreachable!(),
                            }
                        }
                        println!();

                        // Operations
                        println!("⚙️  Operations:");
                        for operation in &collection_config.operations {
                            println!("   {}", operation);
                        }
                    }
                }

                Ok(())
            }

            Commands::List {
                collections,
                environments,
                plugins,
                operations,
            } => {
                info!("Listing available resources");

                // If no specific resource type is specified, list all
                let list_all = !collections && !environments && !plugins && !operations;

                if list_all || collections {
                    let collections_list = config_manager.list_collections();
                    if collections_list.is_empty() {
                        info!("No collections configured");
                    } else {
                        info!("Collections: {}", collections_list.join(", "));
                    }
                }

                if list_all || environments {
                    let environments_list = config_manager.list_environments();
                    if environments_list.is_empty() {
                        info!("No environments configured");
                    } else {
                        info!("Environments: {}", environments_list.join(", "));
                    }
                }

                if list_all || plugins {
                    let plugins_list = config_manager.list_plugins();
                    if plugins_list.is_empty() {
                        info!("No plugins configured");
                    } else {
                        info!("Plugins: {}", plugins_list.join(", "));
                    }
                }

                if list_all || operations {
                    let operations_list = config_manager.list_operations();
                    if operations_list.is_empty() {
                        info!("No operations configured");
                    } else {
                        info!("Operations: {}", operations_list.join(", "));
                    }
                }

                Ok(())
            }

            Commands::Run {
                operation,
                collection,
                environment,
                param,
            } => {
                info!("Running operation '{}'", operation);

                // Get the configuration
                let config = config_manager.get_config();

                // Check if operation exists
                let operation_config = config.operations.get(&operation).ok_or_else(|| {
                    crate::error::CacophonyError::Operation(format!(
                        "Operation '{}' not found",
                        operation
                    ))
                })?;

                // Parse custom parameters
                let mut custom_params = std::collections::HashMap::new();
                for param_str in &param {
                    if let Some((key, value)) = param_str.split_once('=') {
                        custom_params.insert(key.to_string(), value.to_string());
                    } else {
                        warn!(
                            "Invalid parameter format: '{}', expected key=value",
                            param_str
                        );
                    }
                }

                // Validate collection if provided
                if let Some(ref coll_name) = collection {
                    let collection_config = config.collections.get(coll_name).ok_or_else(|| {
                        crate::error::CacophonyError::Collection(format!(
                            "Collection '{}' not found",
                            coll_name
                        ))
                    })?;

                    if !collection_config.operations.contains(&operation) {
                        return Err(crate::error::CacophonyError::Operation(format!(
                            "Collection '{}' does not support operation '{}'",
                            coll_name, operation
                        )));
                    }
                }

                // Validate environment if provided
                if let Some(ref env_name) = environment {
                    let env_config = config.environments.get(env_name).ok_or_else(|| {
                        crate::error::CacophonyError::Environment(format!(
                            "Environment '{}' not found",
                            env_name
                        ))
                    })?;

                    // If collection is also provided, check if it supports this environment
                    if let Some(ref coll_name) = collection {
                        let collection_config = config.collections.get(coll_name).unwrap();
                        if !collection_config.environments.contains(env_name) {
                            return Err(crate::error::CacophonyError::Config(format!(
                                "Collection '{}' does not support environment '{}'",
                                coll_name, env_name
                            )));
                        }
                    }
                }

                info!("✅ Operation '{}' validated", operation);
                info!(
                    "   Description: {}",
                    operation_config
                        .description
                        .as_deref()
                        .unwrap_or("No description")
                );

                if let Some(ref coll_name) = collection {
                    info!("   Collection: {}", coll_name);
                }

                if let Some(ref env_name) = environment {
                    info!("   Environment: {}", env_name);
                }

                if !custom_params.is_empty() {
                    info!("   Custom parameters: {:?}", custom_params);
                }

                // Execute the operation
                if let Some(script) = &operation_config.script {
                    let script_path = Path::new(script);
                    if !script_path.exists() {
                        return Err(crate::error::CacophonyError::Operation(format!(
                            "Operation script '{}' not found",
                            script
                        )));
                    }

                    info!("🚀 Executing operation script: {}", script);

                    // Build command with arguments
                    let mut command = std::process::Command::new("bash");
                    command.arg(script);

                    if let Some(ref coll_name) = collection {
                        command.arg("--collection").arg(coll_name);
                    }

                    if let Some(ref env_name) = environment {
                        command.arg("--environment").arg(env_name);
                    }

                    // Add custom parameters
                    for (key, value) in &custom_params {
                        command.arg("--param").arg(&format!("{}={}", key, value));
                    }

                    // Execute the command
                    let output = command.output();

                    match output {
                        Ok(output) => {
                            if output.status.success() {
                                info!("✅ Operation '{}' completed successfully", operation);
                                if !output.stdout.is_empty() {
                                    info!("📄 Output: {}", String::from_utf8_lossy(&output.stdout));
                                }
                            } else {
                                error!("❌ Operation '{}' failed", operation);
                                if !output.stderr.is_empty() {
                                    error!("📄 Error: {}", String::from_utf8_lossy(&output.stderr));
                                }
                                return Err(crate::error::CacophonyError::Operation(format!(
                                    "Operation '{}' failed",
                                    operation
                                )));
                            }
                        }
                        Err(e) => {
                            error!("❌ Failed to execute operation '{}': {}", operation, e);
                            return Err(crate::error::CacophonyError::Operation(format!(
                                "Failed to execute operation '{}': {}",
                                operation, e
                            )));
                        }
                    }
                } else {
                    warn!("⚠️  Operation '{}' has no script defined", operation);
                }

                info!("✅ Operation '{}' completed", operation);
                Ok(())
            }

            Commands::Status {
                environment,
                detailed,
            } => {
                info!("Showing project status");

                // Get the configuration
                let config = config_manager.get_config();

                // Show project information
                println!(
                    "📋 Project: {} v{}",
                    config.project.name, config.project.version
                );
                if let Some(desc) = &config.project.description {
                    println!("   Description: {}", desc);
                }
                if let Some(repo) = &config.project.repository {
                    println!("   Repository: {}", repo);
                }
                if let Some(license) = &config.project.license {
                    println!("   License: {}", license);
                }
                println!();

                // Show environments
                println!("🌍 Environments ({}):", config.environments.len());
                for (name, env_config) in &config.environments {
                    let status_icon = if let Some(ref target_env) = environment {
                        if name == target_env {
                            "🎯"
                        } else {
                            "  "
                        }
                    } else {
                        "  "
                    };

                    println!(
                        "   {} {} ({})",
                        status_icon,
                        name,
                        env_config
                            .description
                            .as_deref()
                            .unwrap_or("No description")
                    );

                    if detailed {
                        println!("      Variables: {}", env_config.variables.len());
                        println!("      Plugins: {}", env_config.plugins.join(", "));
                    }
                }
                println!();

                // Show collections
                println!("📦 Collections ({}):", config.collections.len());
                for (name, coll_config) in &config.collections {
                    println!(
                        "   {} ({})",
                        name,
                        coll_config
                            .description
                            .as_deref()
                            .unwrap_or("No description")
                    );

                    if detailed {
                        println!(
                            "      Dependencies: {}",
                            coll_config.dependencies.join(", ")
                        );
                        println!("      Operations: {}", coll_config.operations.join(", "));
                        println!(
                            "      Environments: {}",
                            coll_config.environments.join(", ")
                        );
                    }
                }
                println!();

                // Show operations
                println!("⚙️  Operations ({}):", config.operations.len());
                for (name, op_config) in &config.operations {
                    println!(
                        "   {} ({})",
                        name,
                        op_config.description.as_deref().unwrap_or("No description")
                    );

                    if detailed {
                        if let Some(script) = &op_config.script {
                            println!("      Script: {}", script);
                        }
                        if let Some(timeout) = op_config.timeout {
                            println!("      Timeout: {}s", timeout);
                        }
                        if let Some(retries) = op_config.retries {
                            println!("      Retries: {}", retries);
                        }
                    }
                }
                println!();

                // Show plugins
                println!("🔌 Plugins ({}):", config.plugins.len());
                for plugin_config in &config.plugins {
                    let enabled_status = if plugin_config.enabled.unwrap_or(true) {
                        "✓"
                    } else {
                        "✗"
                    };
                    println!(
                        "   {} {} v{}",
                        enabled_status,
                        plugin_config.name,
                        plugin_config.version.as_deref().unwrap_or("unknown")
                    );
                }
                println!();

                // Show deployment status if environment is specified
                if let Some(ref env_name) = environment {
                    let env_config = config.environments.get(env_name).ok_or_else(|| {
                        crate::error::CacophonyError::Environment(format!(
                            "Environment '{}' not found",
                            env_name
                        ))
                    })?;

                    println!("🎯 Deployment Status for Environment: {}", env_name);
                    println!(
                        "   Environment: {} ({})",
                        env_name,
                        env_config
                            .description
                            .as_deref()
                            .unwrap_or("No description")
                    );
                    println!("   Variables: {}", env_config.variables.len());
                    println!("   Plugins: {}", env_config.plugins.join(", "));
                    println!();

                    // Show collections that can be deployed to this environment
                    let deployable_collections: Vec<_> = config
                        .collections
                        .iter()
                        .filter(|(_, coll_config)| coll_config.environments.contains(env_name))
                        .collect();

                    println!(
                        "📦 Deployable Collections ({}):",
                        deployable_collections.len()
                    );
                    for (name, coll_config) in deployable_collections {
                        println!(
                            "   {} ({})",
                            name,
                            coll_config
                                .description
                                .as_deref()
                                .unwrap_or("No description")
                        );

                        if detailed {
                            println!("      Operations: {}", coll_config.operations.join(", "));
                            println!(
                                "      Dependencies: {}",
                                coll_config.dependencies.join(", ")
                            );
                        }
                    }
                }

                Ok(())
            }
        }
    }

    fn create_project_structure(
        project_dir: &Path,
        project_name: &str,
        template_type: &str,
    ) -> Result<()> {
        // Create main project directory
        fs::create_dir_all(project_dir)?;

        // Create subdirectories
        let subdirs = ["environments", "collections", "scripts", "plugins"];

        for subdir in &subdirs {
            fs::create_dir_all(project_dir.join(subdir))?;
        }

        // Create cacophony.lig file
        let config_content = Self::generate_config_template(project_name, template_type);
        fs::write(project_dir.join("cacophony.lig"), config_content)?;

        // Create README.md
        let readme_content = Self::generate_readme_template(project_name);
        fs::write(project_dir.join("README.md"), readme_content)?;

        // Create .gitignore
        let gitignore_content = Self::generate_gitignore_template();
        fs::write(project_dir.join(".gitignore"), gitignore_content)?;

        // Create environment files
        let environments = ["dev", "staging", "prod"];
        for env in &environments {
            let env_content = Self::generate_environment_template(env);
            fs::write(
                project_dir
                    .join("environments")
                    .join(format!("{}.lig", env)),
                env_content,
            )?;
        }

        // Create collection files
        let collections = ["frontend", "backend", "database"];
        for coll in &collections {
            let coll_content = Self::generate_collection_template(coll);
            fs::write(
                project_dir
                    .join("collections")
                    .join(format!("{}.lig", coll)),
                coll_content,
            )?;
        }

        // Create scripts directory with example scripts
        let scripts = [
            ("deploy.sh", Self::generate_deploy_script()),
            ("test.sh", Self::generate_test_script()),
            ("migrate.sh", Self::generate_migrate_script()),
        ];

        for (script_name, script_content) in &scripts {
            fs::write(
                project_dir.join("scripts").join(script_name),
                script_content,
            )?;
            // Make scripts executable
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut perms =
                    fs::metadata(project_dir.join("scripts").join(script_name))?.permissions();
                perms.set_mode(0o755);
                fs::set_permissions(project_dir.join("scripts").join(script_name), perms)?;
            }
        }

        Ok(())
    }

    fn generate_config_template(project_name: &str, template_type: &str) -> String {
        match template_type {
            "terraform" => format!(
                r#"-- {}.lig
-- module Cacophony

-- Project metadata
let project = {{
  name = "{}",
  version = "1.0.0",
  description = "Terraform infrastructure with cacophony",
  authors = ["team@example.com"],
  repository = "https://github.com/example/{}",
  license = "Apache-2.0"
}};

-- Environment definitions
let environments = {{
  dev = {{
    name = "development",
    description = "Development environment",
    variables = {{
      AWS_REGION = "us-west-2",
      ENVIRONMENT = "dev",
      LOG_LEVEL = "debug"
    }},
    plugins = ["terraform"]
  }},
  
  staging = {{
    name = "staging",
    description = "Staging environment",
    variables = {{
      AWS_REGION = "us-west-2",
      ENVIRONMENT = "staging",
      LOG_LEVEL = "info"
    }},
    plugins = ["terraform"]
  }},
  
  prod = {{
    name = "production",
    description = "Production environment",
    variables = {{
      AWS_REGION = "us-west-2",
      ENVIRONMENT = "prod",
      LOG_LEVEL = "warn"
    }},
    plugins = ["terraform"]
  }}
}};

-- Collection definitions
let collections = {{
  frontend = {{
    name = "frontend",
    description = "Frontend application",
    dependencies = ["shared-types"],
    operations = ["deploy", "validate", "test"],
    environments = ["dev", "staging", "prod"]
  }},
  
  backend = {{
    name = "backend",
    description = "Backend API service",
    dependencies = ["shared-types", "database"],
    operations = ["deploy", "validate", "test", "migrate"],
    environments = ["dev", "staging", "prod"]
  }},
  
  database = {{
    name = "database",
    description = "Database configuration and migrations",
    dependencies = ["none"],
    operations = ["deploy", "migrate", "backup"],
    environments = ["dev", "staging", "prod"]
  }}
}};

-- Custom operations
let operations = {{
  migrate = {{
    name = "migrate",
    description = "Run database migrations",
    script = "scripts/migrate.sh",
    parameters = {{
      timeout = 300,
      retries = 3
    }}
  }},
  
  test = {{
    name = "test",
    description = "Run integration tests",
    script = "scripts/test.sh",
    parameters = {{
      parallel = true,
      coverage = true
    }}
  }}
}};

-- Configuration object
let config = {{ project = project, environments = environments, collections = collections, operations = operations }}; 

-- Export the configuration
export config;
"#,
                project_name, project_name, project_name
            ),
            _ => format!(
                r#"-- {}.lig
-- module Cacophony

-- Project metadata
let project = {{
  name = "{}",
  version = "1.0.0",
  description = "Basic cacophony project",
  authors = ["team@example.com"],
  repository = "https://github.com/example/{}",
  license = "Apache-2.0"
}};

-- Environment definitions
let environments = {{
  dev = {{
    name = "development",
    description = "Development environment",
    variables = {{
      LOG_LEVEL = "debug"
    }},
    plugins = []
  }}
}};

-- Collection definitions
let collections = {{
  app = {{
    name = "app",
    description = "Main application",
    dependencies = [],
    operations = ["deploy", "validate"],
    environments = ["dev"]
  }}
}};

-- Custom operations
let operations = {{
  deploy = {{
    name = "deploy",
    description = "Deploy application",
    script = "scripts/deploy.sh",
    parameters = {{
      timeout = 300
    }}
  }}
}};

-- Configuration object
let config = {{ project = project, environments = environments, collections = collections, operations = operations }}; 

-- Export the configuration
export config;
"#,
                project_name, project_name, project_name
            ),
        }
    }

    fn generate_readme_template(project_name: &str) -> String {
        format!(
            r#"# {}

A Cacophony-managed project for orchestrating Ligature programs.

## Quick Start

1. List available resources:
   ```bash
   cacophony list
   ```

2. Validate your configuration:
   ```bash
   cacophony validate
   ```

3. Deploy a collection:
   ```bash
   cacophony deploy --collection app --environment dev
   ```

## Project Structure

- `cacophony.lig` - Main configuration file
- `environments/` - Environment-specific configurations
- `collections/` - Collection definitions
- `scripts/` - Custom operation scripts
- `plugins/` - Custom plugins (optional)

## Configuration

Edit `cacophony.lig` to configure your project's:
- Project metadata
- Environments and variables
- Collections and dependencies
- Custom operations

## Documentation

For more information, see the [Cacophony documentation](https://github.com/fugue-ai/ligature).
"#,
            project_name
        )
    }

    fn generate_gitignore_template() -> String {
        r#"# Cacophony artifacts
.cacophony/
*.log

# Build artifacts
target/
dist/
build/

# Environment files
.env
.env.local

# IDE files
.vscode/
.idea/
*.swp
*.swo

# OS files
.DS_Store
Thumbs.db
"#
        .to_string()
    }

    fn generate_environment_template(env_name: &str) -> String {
        format!(
            r#"-- {}.lig
-- module {}

let overrides = {{
  variables = {{
    "ENV" = "{}"
  }},
  
  collections = {{
    app = {{
      replicas = 1,
      resources = {{
        cpu = "100m",
        memory = "128Mi"
      }}
    }}
  }}
}};

export overrides;
"#,
            env_name, env_name, env_name
        )
    }

    fn generate_collection_template(coll_name: &str) -> String {
        format!(
            r#"-- {}.lig
-- module {}

let config = {{
  name = "{}",
  type = "service",
  
  deploy = {{
    replicas = 2,
    resources = {{
      cpu = "500m",
      memory = "512Mi"
    }},
    
    ports = [{{
      container = 80,
      service = 8080,
      protocol = "http"
    }}]
  }},
  
  environment = {{
    "NODE_ENV" = "production"
  }}
}};

export config;
"#,
            coll_name, coll_name, coll_name
        )
    }

    fn generate_deploy_script() -> String {
        r#"#!/bin/bash
set -e

echo "Deploying application..."

# Add your deployment logic here
echo "Deployment completed successfully"
"#
        .to_string()
    }

    fn generate_test_script() -> String {
        r#"#!/bin/bash
set -e

echo "Running tests..."

# Add your test logic here
echo "Tests completed successfully"
"#
        .to_string()
    }

    fn generate_migrate_script() -> String {
        r#"#!/bin/bash
set -e

echo "Running database migrations..."

# Add your migration logic here
echo "Migrations completed successfully"
"#
        .to_string()
    }
}
