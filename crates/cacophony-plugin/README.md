# Cacophony Plugins

This crate provides the plugin system for the Cacophony CLI tool. It includes the plugin trait, plugin manager, and built-in plugins.

## Overview

The plugin system allows Cacophony to be extended with additional functionality through a clean, modular architecture. Plugins can provide new operations, integrate with external tools, and extend the capabilities of the CLI.

## Features

- **Plugin Trait**: A standardized interface for all plugins
- **Plugin Manager**: Centralized plugin registration and management
- **Built-in Plugins**: Includes the Terraform plugin for infrastructure management
- **Operation System**: Plugins can provide custom operations
- **Configuration Support**: Plugins can be configured through JSON configuration

## Usage

### Basic Plugin Usage

```rust
use cacophony_plugins::{PluginManager, Plugin};

// Create a plugin manager
let mut manager = PluginManager::new();

// Get a plugin
let terraform_plugin = manager.get_plugin("terraform");
if let Some(plugin) = terraform_plugin {
    println!("Plugin: {}", plugin.name());
    println!("Version: {}", plugin.version());
    println!("Description: {}", plugin.description());
}

// List all available plugins
let plugins = manager.list_plugins();
println!("Available plugins: {:?}", plugins);

// Get all operations from all plugins
let operations = manager.get_operations();
for operation in operations {
    println!("Operation: {} - {}", operation.name(), operation.description());
}
```

### Plugin Configuration

```rust
use serde_json::json;

// Configure a plugin
let config = json!({
    "workspace": "production",
    "backend": "s3",
    "dry_run": false,
    "variables": {
        "environment": "prod",
        "instance_count": "3"
    }
});

manager.configure_plugin("terraform", &config)?;
```

## Built-in Plugins

### Terraform Plugin

The Terraform plugin provides infrastructure management capabilities:

- **terraform-plan**: Generate Terraform execution plans
- **terraform-apply**: Apply Terraform configurations
- **terraform-destroy**: Destroy Terraform-managed infrastructure

#### Configuration Options

- `workspace`: Terraform workspace name
- `backend`: Terraform backend configuration
- `variables`: Terraform variables as key-value pairs
- `dry_run`: Whether to perform dry-run operations
- `timeout`: Operation timeout in seconds
- `retries`: Number of retry attempts
- `terraform_path`: Path to Terraform executable

## Creating Custom Plugins

To create a custom plugin, implement the `Plugin` trait:

```rust
use async_trait::async_trait;
use cacophony_plugins::{Plugin, Operation, OperationResult, ValidationResult};
use serde_json::Value;

pub struct MyCustomPlugin {
    name: String,
    version: String,
    config: MyConfig,
}

#[async_trait]
impl Plugin for MyCustomPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        "My custom plugin description"
    }

    fn operations(&self) -> Vec<Box<dyn Operation>> {
        vec![
            Box::new(MyCustomOperation {
                config: self.config.clone(),
            }),
        ]
    }

    fn configure(&mut self, config: &Value) -> Result<()> {
        // Parse and apply configuration
        Ok(())
    }
}
```

## Dependencies

- `cacophony-core`: Core types and traits
- `async-trait`: Async trait support
- `serde_json`: JSON configuration support
- `tokio`: Async runtime
- `tracing`: Logging support

## License

Apache-2.0
