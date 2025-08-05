# Ligature Configuration Management

This directory contains comprehensive configuration management features for the Ligature project, including configuration file examples, validation, and hot-reloading capabilities.

## Overview

The configuration management system provides:

1. **Configuration File Examples** - Ready-to-use configuration templates
2. **Configuration Validation** - Schema-based validation with custom constraints
3. **Configuration Hot-Reloading** - Automatic reloading when files change
4. **XDG Base Directory Support** - Standard configuration locations

## Configuration File Examples

### 1. Ligature CLI Configuration (`ligature-cli.toml`)

A comprehensive configuration for the Ligature CLI tool with sections for:

- **Logging**: Log levels, file/console output, rotation settings
- **Performance**: Parallel processing, caching, worker threads
- **Defaults**: Output format, verbosity, progress display
- **Cache**: Cache size, TTL, auto-cleanup
- **Development**: Debug mode, timing, experimental features
- **Editor**: LSP integration, auto-completion, syntax highlighting
- **Network**: Timeouts, HTTPS, proxy settings
- **Security**: SSL verification, audit logging

### 2. Cacophony Configuration (`cacophony.toml`)

Configuration for the Cacophony project management tool:

- **Project**: Name, version, description, authors, license
- **Environments**: Development, staging, production with variables
- **Collections**: Dependencies, operations, environment mappings
- **Plugins**: Plugin configurations with versions and settings
- **Operations**: Scripts, parameters, timeouts, retries
- **Settings**: Global application settings

### 3. LSP Server Configuration (`lsp-server.toml`)

Language Server Protocol server configuration:

- **Server**: Name, version, port, connection limits
- **Diagnostics**: Error reporting, severity levels, fix suggestions
- **Completion**: Auto-completion, context awareness, snippets
- **Formatting**: Indentation, line length, code style
- **Hover**: Information display, type info, documentation
- **Performance**: Caching, parallel processing, optimizations

## Configuration Validation

The validation system provides:

### Schema-Based Validation

```rust
use ligature_xdg::{ConfigValidator, ConfigSchema, FieldSchema, FieldType};

let mut validator = ConfigValidator::new();

// Define a schema
let schema = ConfigSchema {
    fields: {
        let mut fields = HashMap::new();
        fields.insert("port".to_string(), FieldSchema {
            field_type: FieldType::Port,
            required: true,
            default: Some(serde_json::Value::Number(8080.into())),
            description: Some("Server port".to_string()),
            constraints: vec![FieldConstraint::MinValue(1.0), FieldConstraint::MaxValue(65535.0)],
            // ... other fields
        });
        fields
    },
    required_fields: vec!["port".to_string()],
    // ... other schema fields
};

validator.register_schema("app", schema);

// Validate configuration
let config = serde_json::json!({
    "port": 3000
});

match validator.validate_config(&config, "app") {
    Ok(()) => println!("Configuration is valid"),
    Err(e) => println!("Validation error: {}", e),
}
```

### Field Types

Supported field types include:

- `String` - Text values
- `Integer` - Whole numbers
- `Float` - Decimal numbers
- `Boolean` - True/false values
- `Object` - Nested configuration objects
- `Array` - Lists of values
- `File` - File paths (validated for existence)
- `Directory` - Directory paths (validated for existence)
- `Url` - Valid URLs
- `Email` - Email addresses
- `IpAddress` - IP addresses
- `Port` - Port numbers (1-65535)
- `Duration` - Time durations
- `Size` - File sizes

### Constraints

Available constraints:

- `Required` - Field must be present
- `Optional` - Field can be missing
- `MinValue/MaxValue` - Numeric range validation
- `MinLength/MaxLength` - String length validation
- `Pattern` - Regular expression validation
- `AllowedValues` - Enumeration of valid values
- `FileExists` - File must exist
- `DirectoryExists` - Directory must exist
- `ValidUrl` - Valid URL format
- `ValidEmail` - Valid email format
- `ValidIpAddress` - Valid IP address
- `ValidPort` - Valid port number
- `ValidDuration` - Valid duration format
- `ValidSize` - Valid size format
- `Custom` - Custom validation functions

### Custom Validators

Register custom validation functions:

```rust
validator.register_custom_validator("custom_port", |value| {
    if let Some(port) = value.as_u64() {
        if port >= 1024 && port <= 65535 {
            Ok(())
        } else {
            Err(ValidationError::ConstraintViolation(
                "Port must be between 1024 and 65535".to_string()
            ))
        }
    } else {
        Err(ValidationError::TypeMismatch {
            expected: "port number".to_string(),
            actual: "non-number".to_string(),
        })
    }
});
```

## Configuration Hot-Reloading

The hot-reloading system automatically detects and reloads configuration files when they change.

### Basic Usage

```rust
use ligature_xdg::{ConfigHotReloader, HotReloadConfig, ConfigChangeEvent};

// Create hot reload configuration
let config = HotReloadConfig {
    enabled: true,
    debounce_ms: 500,
    recursive: true,
    watch_extensions: vec!["toml".to_string(), "json".to_string()],
    exclude_directories: vec![".git".to_string()],
    max_retries: 3,
    retry_delay_ms: 1000,
};

// Create hot reloader
let mut reloader = ConfigHotReloader::new(config, validator);

// Register callback for configuration changes
reloader.register_callback("my_app", Box::new(|event, config| {
    match event {
        ConfigChangeEvent::Created(path) => {
            println!("Configuration file created: {}", path.display());
        }
        ConfigChangeEvent::Modified(path) => {
            println!("Configuration file modified: {}", path.display());
            // Apply new configuration
            apply_config(config);
        }
        ConfigChangeEvent::Deleted(path) => {
            println!("Configuration file deleted: {}", path.display());
        }
        ConfigChangeEvent::Renamed { from, to } => {
            println!("Configuration file renamed: {} -> {}", from.display(), to.display());
        }
    }
    Ok(())
}))?;

// Start watching
reloader.start_watching(&config_dir).await?;

// Stop watching when done
reloader.stop_watching()?;
```

### Hot Reload Configuration

- `enabled` - Whether hot reloading is enabled
- `debounce_ms` - Debounce time to avoid rapid reloads
- `recursive` - Watch subdirectories recursively
- `watch_extensions` - File extensions to watch
- `exclude_directories` - Directories to exclude
- `max_retries` - Maximum retries on validation failure
- `retry_delay_ms` - Delay between retries

## XDG Base Directory Support

The system uses XDG base directories for standard configuration locations:

- **Config**: `~/.config/ligature/` (or `$XDG_CONFIG_HOME/ligature/`)
- **Data**: `~/.local/share/ligature/` (or `$XDG_DATA_HOME/ligature/`)
- **Cache**: `~/.cache/ligature/` (or `$XDG_CACHE_HOME/ligature/`)
- **State**: `~/.local/state/ligature/` (or `$XDG_STATE_HOME/ligature/`)

### Usage

```rust
use ligature_xdg::{XdgConfig, XdgPaths};

// Get XDG paths
let xdg_paths = XdgPaths::new("ligature")?;
let config_dir = xdg_paths.config_dir()?;
let data_dir = xdg_paths.data_dir()?;
let cache_dir = xdg_paths.cache_dir()?;

// Load configuration
let xdg_config = XdgConfig::new("ligature", "config.toml")?;
let config = xdg_config.load().await?;
```

## Running the Example

To run the comprehensive configuration management example:

```bash
cd examples/config
cargo run --bin configuration_management_example
```

This will:

1. Create configuration file examples in your XDG config directory
2. Set up validation schemas for different configuration types
3. Demonstrate validation with valid and invalid configurations
4. Show hot-reloading functionality with file system events

## Error Handling

The system provides comprehensive error handling:

```rust
use ligature_xdg::{ValidationError, HotReloadError};

match validator.validate_config(&config, "schema") {
    Ok(()) => println!("Configuration is valid"),
    Err(ValidationError::MissingRequiredField { field }) => {
        println!("Missing required field: {}", field);
    }
    Err(ValidationError::TypeMismatch { expected, actual }) => {
        println!("Type mismatch: expected {}, got {}", expected, actual);
    }
    Err(ValidationError::ConstraintViolation(msg)) => {
        println!("Constraint violation: {}", msg);
    }
    Err(e) => println!("Other validation error: {}", e),
}
```

## Best Practices

1. **Use XDG Directories**: Always use XDG base directories for configuration storage
2. **Validate Early**: Validate configurations as soon as they're loaded
3. **Provide Defaults**: Always provide sensible default values
4. **Document Schemas**: Document your configuration schemas for users
5. **Handle Errors Gracefully**: Provide clear error messages for validation failures
6. **Use Hot Reloading**: Enable hot reloading for development environments
7. **Cache Configurations**: Cache validated configurations for performance
8. **Secure Sensitive Data**: Never store sensitive data in plain text

## Dependencies

The configuration management system requires these dependencies:

```toml
[dependencies]
ligature-xdg = { path = "../../crates/ligature-xdg" }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tokio = { version = "1.0", features = ["fs", "sync", "time"] }
notify = "6.1"
regex = "1.10"
url = "2.4"
tempfile = "3.8"
```

## Contributing

When adding new configuration features:

1. Add comprehensive examples
2. Update validation schemas
3. Add tests for new functionality
4. Update documentation
5. Follow the existing code style and patterns 