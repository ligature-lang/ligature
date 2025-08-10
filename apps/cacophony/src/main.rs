use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;
use ligature_ast::DeclarationKind;
use ligature_error::{ErrorReportConfig, StandardError, StandardErrorReporter};
use ligature_eval::value::ValueKind;
use ligature_eval::{Evaluator, Value};
use ligature_parser::Declaration;

// Import Cacophony configuration types
use cacophony_config::*;

/// Type alias for configuration values
type ConfigValues = Vec<(String, Value)>;

#[derive(Parser)]
#[command(name = "cacophony")]
#[command(about = "Configuration management tool for Ligature")]
struct Cli {
    #[arg(short, long)]
    file: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,

    #[arg(long)]
    validate: bool,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(file) = cli.file {
        process_file(&file, cli.verbose, cli.validate)
    } else {
        process_stdin(cli.verbose, cli.validate)
    }
}

fn process_file(file: &PathBuf, verbose: bool, validate: bool) -> Result<()> {
    // Read file with context
    let source = std::fs::read_to_string(file)
        .with_context(|| format!("Failed to read file: {}", file.display()))?;

    // Process the configuration
    let result = process_configuration(&source, file, validate);

    match result {
        Ok(config) => {
            if verbose {
                println!("Configuration processed successfully:");
                println!("  File: {}", file.display());
                println!("  Size: {} bytes", source.len());
                println!("  Validated: {validate}");
                println!("  Project: {}", config.project.name);
                println!("  Environments: {}", config.environments.len());
                println!("  Collections: {}", config.collections.len());
                println!("  Operations: {}", config.operations.len());
                println!("  Plugins: {}", config.plugins.len());
            } else {
                println!("✓ Configuration processed successfully");
                println!("  Project: {}", config.project.name);
                println!(
                    "  Found {} environments, {} collections, {} operations",
                    config.environments.len(),
                    config.collections.len(),
                    config.operations.len()
                );
            }
            Ok(())
        }
        Err(e) => {
            // Use the new standardized error reporter
            let mut reporter = StandardErrorReporter::with_source_and_config(
                source,
                ErrorReportConfig {
                    show_source: true,
                    show_suggestions: true,
                    show_error_codes: true,
                    show_categories: true,
                    color_output: true,
                    max_errors: 10,
                    show_metadata: false,
                    group_by_category: true,
                },
            );

            // Convert anyhow error to standard error
            let standard_error = StandardError::internal_error(e.to_string());
            reporter.add_error(standard_error);

            eprintln!("{}", reporter.report());
            Err(e)
        }
    }
}

fn process_stdin(verbose: bool, validate: bool) -> Result<()> {
    use std::io::{self, BufRead};

    let stdin = io::stdin();
    let mut handle = stdin.lock();
    let mut buffer = String::new();

    while handle.read_line(&mut buffer)? > 0 {
        let result = process_configuration(&buffer, PathBuf::from("<stdin>").as_path(), validate);

        match result {
            Ok(config) => {
                if verbose {
                    println!("✓ Line processed successfully");
                    println!("  Project: {}", config.project.name);
                    println!("  Environments: {}", config.environments.len());
                    println!("  Collections: {}", config.collections.len());
                }
            }
            Err(e) => {
                if verbose {
                    eprintln!("Error: {e:?}");
                } else {
                    eprintln!("Error: {e}");
                }
            }
        }

        buffer.clear();
    }

    Ok(())
}

fn process_configuration(
    source: &str,
    file: &std::path::Path,
    validate: bool,
) -> Result<CacophonyConfig> {
    // Parse configuration with error context
    let mut parser = ligature_parser::Parser::new();
    let program = parser
        .parse_program(source)
        .with_context(|| format!("Failed to parse configuration from {}", file.display()))?;

    if validate {
        // Validate configuration with error context
        validate_configuration(&program).with_context(|| "Configuration validation failed")?;
    }

    // Apply configuration using the evaluator and extract structured config
    let config = apply_configuration(&program).with_context(|| "Failed to apply configuration")?;

    Ok(config)
}

fn validate_configuration(program: &ligature_parser::Program) -> Result<()> {
    // Validate each declaration
    for decl in &program.declarations {
        validate_declaration(decl).with_context(|| "Failed to validate declaration".to_string())?;
    }
    Ok(())
}

fn validate_declaration(decl: &Declaration) -> Result<()> {
    // Validate declaration structure
    match &decl.kind {
        DeclarationKind::Value(value_decl) => {
            if value_decl.name.is_empty() {
                return Err(anyhow::anyhow!("Variable name cannot be empty"));
            }
            // Additional validation could be added here (type checking, etc.)
        }
        _ => {
            // For now, we only process value declarations as configuration
            // Other declaration types are ignored
        }
    }
    Ok(())
}

fn apply_configuration(program: &ligature_parser::Program) -> Result<CacophonyConfig> {
    // Create a new evaluator
    let mut evaluator = Evaluator::new();

    // Evaluate the program - this will populate the evaluator's environment
    evaluator
        .evaluate_program(program)
        .with_context(|| "Failed to evaluate configuration program")?;

    // Extract configuration values from the evaluator's environment
    let config_values = extract_configuration_values(&evaluator.environment);

    // Convert the configuration values to a structured CacophonyConfig
    let config = convert_to_cacophony_config(&config_values)
        .with_context(|| "Failed to convert configuration values to CacophonyConfig")?;

    Ok(config)
}

fn extract_configuration_values(
    environment: &ligature_eval::EvaluationEnvironment,
) -> ConfigValues {
    let mut config_values = Vec::new();

    // Get all bindings from the environment
    let bindings = environment.current_bindings();

    for (name, value) in bindings {
        // Only include values that are not functions or modules (i.e., actual configuration data)
        if !is_function_or_module(value) {
            config_values.push((name.clone(), value.clone()));
        }
    }

    config_values
}

fn is_function_or_module(value: &Value) -> bool {
    matches!(
        &value.kind,
        ValueKind::Function { .. } | ValueKind::Closure { .. } | ValueKind::Module { .. }
    )
}

fn convert_to_cacophony_config(config_values: &ConfigValues) -> Result<CacophonyConfig> {
    // Look for the main configuration object
    let mut config = create_default_cacophony_config();

    for (name, value) in config_values {
        match name.as_str() {
            "config" => {
                // This should be the main configuration object
                if let Some(record) = value.as_record() {
                    config = convert_record_to_cacophony_config(record)?;
                } else {
                    return Err(anyhow::anyhow!("Expected 'config' to be a record"));
                }
            }
            "project" => {
                if let Some(record) = value.as_record() {
                    config.project = convert_record_to_project_config(record)?;
                }
            }
            "environments" => {
                if let Some(record) = value.as_record() {
                    config.environments = convert_record_to_environments(record)?;
                }
            }
            "collections" => {
                if let Some(record) = value.as_record() {
                    config.collections = convert_record_to_collections(record)?;
                }
            }
            "operations" => {
                if let Some(record) = value.as_record() {
                    config.operations = convert_record_to_operations(record)?;
                }
            }
            "plugins" => {
                if let Some(list) = value.as_list() {
                    config.plugins = convert_list_to_plugins(list)?;
                }
            }
            _ => {
                // Ignore other values
            }
        }
    }

    Ok(config)
}

fn convert_record_to_cacophony_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<CacophonyConfig> {
    let mut config = create_default_cacophony_config();

    for (key, value) in record {
        match key.as_str() {
            "project" => {
                if let Some(record) = value.as_record() {
                    config.project = convert_record_to_project_config(record)?;
                }
            }
            "environments" => {
                if let Some(record) = value.as_record() {
                    config.environments = convert_record_to_environments(record)?;
                }
            }
            "collections" => {
                if let Some(record) = value.as_record() {
                    config.collections = convert_record_to_collections(record)?;
                }
            }
            "operations" => {
                if let Some(record) = value.as_record() {
                    config.operations = convert_record_to_operations(record)?;
                }
            }
            "plugins" => {
                if let Some(list) = value.as_list() {
                    config.plugins = convert_list_to_plugins(list)?;
                }
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_record_to_project_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<ProjectConfig> {
    let mut config = create_default_project_config();

    for (key, value) in record {
        match key.as_str() {
            "name" => {
                if let Some(name) = value.as_string() {
                    config.name = name.to_string();
                }
            }
            "version" => {
                if let Some(version) = value.as_string() {
                    config.version = version.to_string();
                }
            }
            "description" => {
                if let Some(desc) = value.as_string() {
                    config.description = Some(desc.to_string());
                }
            }
            "authors" => {
                if let Some(list) = value.as_list() {
                    config.authors = convert_list_to_strings(list)?;
                }
            }
            "repository" => {
                if let Some(repo) = value.as_string() {
                    config.repository = Some(repo.to_string());
                }
            }
            "license" => {
                if let Some(license) = value.as_string() {
                    config.license = Some(license.to_string());
                }
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_record_to_environments(
    record: &std::collections::HashMap<String, Value>,
) -> Result<std::collections::HashMap<String, EnvironmentConfig>> {
    let mut environments = std::collections::HashMap::new();

    for (name, value) in record {
        if let Some(env_record) = value.as_record() {
            let env_config = convert_record_to_environment_config(env_record)?;
            environments.insert(name.clone(), env_config);
        }
    }

    Ok(environments)
}

fn convert_record_to_environment_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<EnvironmentConfig> {
    let mut config = create_default_environment_config();

    for (key, value) in record {
        match key.as_str() {
            "name" => {
                if let Some(name) = value.as_string() {
                    config.name = name.to_string();
                }
            }
            "description" => {
                if let Some(desc) = value.as_string() {
                    config.description = Some(desc.to_string());
                }
            }
            "variables" => {
                if let Some(record) = value.as_record() {
                    config.variables = convert_record_to_string_map(record)?;
                }
            }
            "plugins" => {
                if let Some(list) = value.as_list() {
                    config.plugins = convert_list_to_strings(list)?;
                }
            }
            "overrides" => {
                // TODO: Implement overrides conversion
                // For now, we'll skip this
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_record_to_collections(
    record: &std::collections::HashMap<String, Value>,
) -> Result<std::collections::HashMap<String, CollectionConfig>> {
    let mut collections = std::collections::HashMap::new();

    for (name, value) in record {
        if let Some(coll_record) = value.as_record() {
            let coll_config = convert_record_to_collection_config(coll_record)?;
            collections.insert(name.clone(), coll_config);
        }
    }

    Ok(collections)
}

fn convert_record_to_collection_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<CollectionConfig> {
    let mut config = create_default_collection_config();

    for (key, value) in record {
        match key.as_str() {
            "name" => {
                if let Some(name) = value.as_string() {
                    config.name = name.to_string();
                }
            }
            "description" => {
                if let Some(desc) = value.as_string() {
                    config.description = Some(desc.to_string());
                }
            }
            "dependencies" => {
                if let Some(list) = value.as_list() {
                    config.dependencies = convert_list_to_strings(list)?;
                }
            }
            "operations" => {
                if let Some(list) = value.as_list() {
                    config.operations = convert_list_to_strings(list)?;
                }
            }
            "environments" => {
                if let Some(list) = value.as_list() {
                    config.environments = convert_list_to_strings(list)?;
                }
            }
            "config" => {
                // TODO: Implement config conversion to serde_json::Value
                // For now, we'll skip this
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_record_to_operations(
    record: &std::collections::HashMap<String, Value>,
) -> Result<std::collections::HashMap<String, OperationConfig>> {
    let mut operations = std::collections::HashMap::new();

    for (name, value) in record {
        if let Some(op_record) = value.as_record() {
            let op_config = convert_record_to_operation_config(op_record)?;
            operations.insert(name.clone(), op_config);
        }
    }

    Ok(operations)
}

fn convert_record_to_operation_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<OperationConfig> {
    let mut config = create_default_operation_config();

    for (key, value) in record {
        match key.as_str() {
            "name" => {
                if let Some(name) = value.as_string() {
                    config.name = name.to_string();
                }
            }
            "description" => {
                if let Some(desc) = value.as_string() {
                    config.description = Some(desc.to_string());
                }
            }
            "script" => {
                if let Some(script) = value.as_string() {
                    config.script = Some(script.to_string());
                }
            }
            "parameters" => {
                // TODO: Implement parameters conversion to serde_json::Value
                // For now, we'll skip this
            }
            "timeout" => {
                if let Some(timeout) = value.as_integer() {
                    config.timeout = Some(timeout as u64);
                }
            }
            "retries" => {
                if let Some(retries) = value.as_integer() {
                    config.retries = Some(retries as u32);
                }
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_list_to_plugins(list: &[Value]) -> Result<Vec<PluginConfig>> {
    let mut plugins = Vec::new();

    for value in list {
        if let Some(record) = value.as_record() {
            let plugin_config = convert_record_to_plugin_config(record)?;
            plugins.push(plugin_config);
        }
    }

    Ok(plugins)
}

fn convert_record_to_plugin_config(
    record: &std::collections::HashMap<String, Value>,
) -> Result<PluginConfig> {
    let mut config = create_default_plugin_config();

    for (key, value) in record {
        match key.as_str() {
            "name" => {
                if let Some(name) = value.as_string() {
                    config.name = name.to_string();
                }
            }
            "version" => {
                if let Some(version) = value.as_string() {
                    config.version = Some(version.to_string());
                }
            }
            "config" => {
                // TODO: Implement config conversion to serde_json::Value
                // For now, we'll skip this
            }
            "enabled" => {
                if let Some(enabled) = value.as_boolean() {
                    config.enabled = Some(enabled);
                }
            }
            _ => {
                // Ignore unknown fields
            }
        }
    }

    Ok(config)
}

fn convert_record_to_string_map(
    record: &std::collections::HashMap<String, Value>,
) -> Result<std::collections::HashMap<String, String>> {
    let mut map = std::collections::HashMap::new();

    for (key, value) in record {
        if let Some(string_value) = value.as_string() {
            map.insert(key.clone(), string_value.to_string());
        }
    }

    Ok(map)
}

fn convert_list_to_strings(list: &[Value]) -> Result<Vec<String>> {
    let mut strings = Vec::new();

    for value in list {
        if let Some(string_value) = value.as_string() {
            strings.push(string_value.to_string());
        }
    }

    Ok(strings)
}

// Helper functions to create default configurations
fn create_default_cacophony_config() -> CacophonyConfig {
    CacophonyConfig {
        project: create_default_project_config(),
        environments: std::collections::HashMap::new(),
        collections: std::collections::HashMap::new(),
        plugins: Vec::new(),
        operations: std::collections::HashMap::new(),
    }
}

fn create_default_project_config() -> ProjectConfig {
    ProjectConfig {
        name: "default".to_string(),
        version: "0.1.0".to_string(),
        description: None,
        authors: Vec::new(),
        repository: None,
        license: None,
    }
}

fn create_default_environment_config() -> EnvironmentConfig {
    EnvironmentConfig {
        name: "default".to_string(),
        description: None,
        variables: std::collections::HashMap::new(),
        plugins: Vec::new(),
        overrides: None,
    }
}

fn create_default_collection_config() -> CollectionConfig {
    CollectionConfig {
        name: "default".to_string(),
        description: None,
        dependencies: Vec::new(),
        operations: Vec::new(),
        environments: Vec::new(),
        config: None,
    }
}

fn create_default_operation_config() -> OperationConfig {
    OperationConfig {
        name: "default".to_string(),
        description: None,
        script: None,
        parameters: None,
        timeout: None,
        retries: None,
    }
}

fn create_default_plugin_config() -> PluginConfig {
    PluginConfig {
        name: "default".to_string(),
        version: None,
        config: None,
        enabled: None,
    }
}
