use embouchure_xdg::{
    ConfigChangeEvent, ConfigHotReloader, ConfigReloadCallback, ConfigSchema, ConfigValidator,
    Constraint, FieldConstraint, FieldSchema, FieldType, HotReloadConfig, XdgConfig, XdgPaths,
};
use serde_json::json;
use std::collections::HashMap;
use std::path::Path;
use tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Configuration Management Example ===\n");

    // 1. Create configuration file examples
    create_configuration_examples().await?;

    // 2. Set up configuration validation
    let validator = setup_configuration_validation()?;

    // 3. Demonstrate configuration validation
    demonstrate_configuration_validation(&validator).await?;

    // 4. Set up and demonstrate hot-reloading
    demonstrate_hot_reloading(&validator).await?;

    println!("Configuration management example completed successfully!");
    Ok(())
}

/// Create configuration file examples
async fn create_configuration_examples() -> Result<(), Box<dyn std::error::Error>> {
    println!("1. Creating configuration file examples...");

    // Initialize XDG paths
    let xdg_paths = XdgPaths::new("ligature-example")?;
    let config_dir = xdg_paths.config_dir()?;

    // Ensure config directory exists
    tokio::fs::create_dir_all(&config_dir).await?;

    // Create CLI configuration example
    let cli_config = r#"
# Ligature CLI Configuration Example
[logging]
level = "info"
log_to_file = true
log_to_console = false
max_file_size = 10485760
max_files = 5
include_timestamps = true

[performance]
enable_parallel = true
worker_threads = 0
enable_caching = true
cache_ttl_seconds = 3600

[defaults]
output_format = "text"
verbose = false
show_progress = true
timeout_seconds = 30

[cache]
enabled = true
max_size = 104857600
max_age = 86400
auto_clean = true
"#;

    let cli_config_path = config_dir.join("ligature-cli.toml");
    tokio::fs::write(&cli_config_path, cli_config).await?;
    println!("   Created: {}", cli_config_path.display());

    // Create Cacophony configuration example
    let cacophony_config = r#"
# Cacophony Configuration Example
[project]
name = "example-project"
version = "1.0.0"
description = "Example Ligature project"
authors = ["Developer"]
license = "Apache-2.0"

[environments.development]
name = "development"
variables = { DATABASE_URL = "sqlite:///dev.db", LOG_LEVEL = "debug" }
plugins = ["debug-plugin"]

[collections.core]
name = "core"
dependencies = []
operations = ["parse", "evaluate"]
environments = ["development"]

[[plugins]]
name = "debug-plugin"
version = "1.0.0"
enabled = true

[operations.parse]
name = "parse"
description = "Parse Ligature code"
timeout = 30
"#;

    let cacophony_config_path = config_dir.join("cacophony.toml");
    tokio::fs::write(&cacophony_config_path, cacophony_config).await?;
    println!("   Created: {}", cacophony_config_path.display());

    // Create LSP configuration example
    let lsp_config = r#"
# LSP Server Configuration Example
[server]
name = "ligature-lsp"
version = "1.0.0"
enabled = true
port = 0
max_connections = 10

[diagnostics]
enabled = true
default_severity = "warning"
enable_detailed_explanations = true
enable_fix_suggestions = true

[completion]
enabled = true
enable_context_aware = true
enable_type_aware = true
max_completion_items = 50

[formatting]
enabled = true
indent_style = "spaces"
indent_size = 2
max_line_length = 80
"#;

    let lsp_config_path = config_dir.join("lsp-server.toml");
    tokio::fs::write(&lsp_config_path, lsp_config).await?;
    println!("   Created: {}", lsp_config_path.display());

    println!("   Configuration examples created successfully!\n");
    Ok(())
}

/// Set up configuration validation with schemas
fn setup_configuration_validation() -> Result<ConfigValidator, Box<dyn std::error::Error>> {
    println!("2. Setting up configuration validation...");

    let mut validator = ConfigValidator::new();

    // CLI Configuration Schema
    let cli_schema = ConfigSchema {
        fields: {
            let mut fields = HashMap::new();

            // Logging section
            fields.insert(
                "logging".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Logging configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            // Performance section
            fields.insert(
                "performance".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Performance settings".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            // Defaults section
            fields.insert(
                "defaults".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Default settings".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            // Cache section
            fields.insert(
                "cache".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Cache settings".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields
        },
        required_fields: vec![
            "logging".to_string(),
            "performance".to_string(),
            "defaults".to_string(),
            "cache".to_string(),
        ],
        optional_fields: vec![],
        dependencies: HashMap::new(),
        constraints: vec![],
    };

    // Cacophony Configuration Schema
    let cacophony_schema = ConfigSchema {
        fields: {
            let mut fields = HashMap::new();

            fields.insert(
                "project".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Project configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "environments".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: false,
                    default: None,
                    description: Some("Environment configurations".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "collections".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: false,
                    default: None,
                    description: Some("Collection configurations".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "plugins".to_string(),
                FieldSchema {
                    field_type: FieldType::Array,
                    required: false,
                    default: None,
                    description: Some("Plugin configurations".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "operations".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: false,
                    default: None,
                    description: Some("Operation configurations".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields
        },
        required_fields: vec!["project".to_string()],
        optional_fields: vec![
            "environments".to_string(),
            "collections".to_string(),
            "plugins".to_string(),
            "operations".to_string(),
        ],
        dependencies: HashMap::new(),
        constraints: vec![],
    };

    // LSP Configuration Schema
    let lsp_schema = ConfigSchema {
        fields: {
            let mut fields = HashMap::new();

            fields.insert(
                "server".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Server configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "diagnostics".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Diagnostics configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "completion".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Completion configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields.insert(
                "formatting".to_string(),
                FieldSchema {
                    field_type: FieldType::Object,
                    required: true,
                    default: None,
                    description: Some("Formatting configuration".to_string()),
                    constraints: vec![],
                    allowed_values: None,
                    pattern: None,
                    min_value: None,
                    max_value: None,
                    min_length: None,
                    max_length: None,
                },
            );

            fields
        },
        required_fields: vec![
            "server".to_string(),
            "diagnostics".to_string(),
            "completion".to_string(),
            "formatting".to_string(),
        ],
        optional_fields: vec![],
        dependencies: HashMap::new(),
        constraints: vec![],
    };

    // Register schemas
    validator.register_schema("cli", cli_schema);
    validator.register_schema("cacophony", cacophony_schema);
    validator.register_schema("lsp", lsp_schema);

    // Register custom validators
    validator.register_custom_validator("port", |value| {
        if let Some(port) = value.as_u64() {
            if port > 0 && port <= 65535 {
                Ok(())
            } else {
                Err(embouchure_xdg::ValidationError::ConstraintViolation(
                    format!("Port must be between 1 and 65535, got {}", port),
                ))
            }
        } else {
            Err(embouchure_xdg::ValidationError::TypeMismatch {
                expected: "port number".to_string(),
                actual: "non-number".to_string(),
            })
        }
    });

    println!("   Configuration validation setup completed!\n");
    Ok(validator)
}

/// Demonstrate configuration validation
async fn demonstrate_configuration_validation(
    validator: &ConfigValidator,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("3. Demonstrating configuration validation...");

    // Test valid CLI configuration
    let valid_cli_config = json!({
        "logging": {
            "level": "info",
            "log_to_file": true,
            "log_to_console": false,
            "max_file_size": 10485760,
            "max_files": 5,
            "include_timestamps": true
        },
        "performance": {
            "enable_parallel": true,
            "worker_threads": 0,
            "enable_caching": true,
            "cache_ttl_seconds": 3600
        },
        "defaults": {
            "output_format": "text",
            "verbose": false,
            "show_progress": true,
            "timeout_seconds": 30
        },
        "cache": {
            "enabled": true,
            "max_size": 104857600,
            "max_age": 86400,
            "auto_clean": true
        }
    });

    match validator.validate_config(&valid_cli_config, "cli") {
        Ok(()) => println!("   ✓ Valid CLI configuration passed validation"),
        Err(e) => println!("   ✗ Valid CLI configuration failed validation: {}", e),
    }

    // Test invalid CLI configuration (missing required field)
    let invalid_cli_config = json!({
        "logging": {
            "level": "info"
        },
        "performance": {
            "enable_parallel": true
        }
        // Missing "defaults" and "cache" sections
    });

    match validator.validate_config(&invalid_cli_config, "cli") {
        Ok(()) => println!("   ✗ Invalid CLI configuration unexpectedly passed validation"),
        Err(e) => println!(
            "   ✓ Invalid CLI configuration correctly failed validation: {}",
            e
        ),
    }

    // Test valid Cacophony configuration
    let valid_cacophony_config = json!({
        "project": {
            "name": "example-project",
            "version": "1.0.0",
            "description": "Example project",
            "authors": ["Developer"],
            "license": "Apache-2.0"
        },
        "environments": {
            "development": {
                "name": "development",
                "variables": {
                    "DATABASE_URL": "sqlite:///dev.db",
                    "LOG_LEVEL": "debug"
                },
                "plugins": ["debug-plugin"]
            }
        }
    });

    match validator.validate_config(&valid_cacophony_config, "cacophony") {
        Ok(()) => println!("   ✓ Valid Cacophony configuration passed validation"),
        Err(e) => println!(
            "   ✗ Valid Cacophony configuration failed validation: {}",
            e
        ),
    }

    println!("   Configuration validation demonstration completed!\n");
    Ok(())
}

/// Demonstrate hot-reloading functionality
async fn demonstrate_hot_reloading(
    validator: &ConfigValidator,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("4. Demonstrating configuration hot-reloading...");

    // Create a temporary directory for testing
    let temp_dir = tempfile::tempdir()?;
    let config_dir = temp_dir.path();

    // Create initial configuration file
    let initial_config = r#"
[test]
value = "initial"
enabled = true
"#;

    let config_path = config_dir.join("test.toml");
    tokio::fs::write(&config_path, initial_config).await?;

    // Set up hot reload configuration
    let hot_reload_config = HotReloadConfig {
        enabled: true,
        debounce_ms: 100, // Short debounce for testing
        recursive: true,
        watch_extensions: vec!["toml".to_string(), "json".to_string()],
        exclude_directories: vec![".git".to_string()],
        max_retries: 3,
        retry_delay_ms: 100,
    };

    // Create hot reloader
    let mut reloader = ConfigHotReloader::new(hot_reload_config, validator.clone());

    // Register callback for configuration changes
    let callback: ConfigReloadCallback = Box::new(|event, config| {
        match event {
            ConfigChangeEvent::Created(path) => {
                println!("   📄 Configuration file created: {}", path.display());
            }
            ConfigChangeEvent::Modified(path) => {
                println!("   ✏️  Configuration file modified: {}", path.display());
                println!("      New configuration: {config:?}");
            }
            ConfigChangeEvent::Deleted(path) => {
                println!("   🗑️  Configuration file deleted: {}", path.display());
            }
            ConfigChangeEvent::Renamed { from, to } => {
                println!(
                    "   🔄 Configuration file renamed: {} -> {}",
                    from.display(),
                    to.display()
                );
            }
        }
        Ok(())
    });

    reloader.register_callback("example", callback)?;

    // Start watching
    reloader.start_watching(config_dir).await?;
    println!(
        "   🔍 Started watching configuration directory: {}",
        config_dir.display()
    );

    // Simulate configuration changes
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;

    // Modify the configuration file
    let updated_config = r#"
[test]
value = "updated"
enabled = false
"#;

    tokio::fs::write(&config_path, updated_config).await?;
    println!("   📝 Modified configuration file");

    // Wait for the change to be detected
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;

    // Create a new configuration file
    let new_config = r#"
[new_section]
setting = "new_value"
"#;

    let new_config_path = config_dir.join("new.toml");
    tokio::fs::write(&new_config_path, new_config).await?;
    println!("   📄 Created new configuration file");

    // Wait for the change to be detected
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;

    // Stop watching
    reloader.stop_watching()?;
    println!("   🛑 Stopped watching configuration directory");

    println!("   Configuration hot-reloading demonstration completed!\n");
    Ok(())
}
