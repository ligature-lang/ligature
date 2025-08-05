# Ligature XDG Configuration

A unified XDG base directory implementation for all Ligature components, providing standardized configuration, data, cache, and state directory management.

## Features

- **XDG Base Directory Compliance**: Follows the XDG Base Directory Specification
- **Cross-Platform Support**: Works on Linux, macOS, and Windows with appropriate fallbacks
- **Component Isolation**: Each Ligature component gets its own subdirectory
- **Multiple Format Support**: JSON, YAML, and TOML configuration files
- **Async Support**: Full async/await support for file operations
- **Error Handling**: Comprehensive error types with detailed context

## Quick Start

```rust
use ligature_xdg::{config_for_component, XdgPaths};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct MyConfig {
    name: String,
    enabled: bool,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Get XDG paths for your component
    let paths = XdgPaths::new("my-component")?;
    println!("Config dir: {}", paths.config_dir()?.display());

    // Load/save configuration
    let config_manager = config_for_component("my-component")?;
    let config = MyConfig {
        name: "example".to_string(),
        enabled: true,
    };

    // Save configuration
    let saved_path = config_manager.save(&config).await?;

    // Load configuration
    let loaded_config = config_manager.load::<MyConfig>().await?.unwrap();

    Ok(())
}
```

## Directory Structure

For a component named "example", the following directory structure is created:

```
~/.config/ligature/example/     # Configuration files
~/.local/share/ligature/example/ # Data files
~/.cache/ligature/example/       # Cache files
~/.local/state/ligature/example/ # State files
```

## API Reference

### XdgPaths

The core struct for managing XDG base directories for a component.

```rust
let paths = XdgPaths::new("my-component")?;

// Get directory paths
let config_dir = paths.config_dir()?;
let data_dir = paths.data_dir()?;
let cache_dir = paths.cache_dir()?;
let state_dir = paths.state_dir()?;

// Get file paths
let config_file = paths.config_file("config.json")?;
let data_file = paths.data_file("data.db")?;

// Ensure directories exist
paths.ensure_directories().await?;

// Find files in standard locations
let config_path = paths.find_config_file("config.json")?;
let data_path = paths.find_data_file("data.db")?;
```

### XdgConfig

Configuration file management with automatic format detection.

```rust
// Create config manager with default JSON file
let config = config_for_component("my-component")?;

// Create config manager with specific format
let yaml_config = yaml_config_for_component("my-component")?;
let toml_config = toml_config_for_component("my-component")?;

// Save configuration
let saved_path = config.save(&my_config).await?;

// Load configuration
let loaded_config = config.load::<MyConfig>().await?;

// Load from specific file
let custom_config = config.load_from("custom.yaml").await?;
```

## Supported File Formats

- **JSON**: Default format, human-readable
- **YAML**: Alternative format, more readable for complex configurations
- **TOML**: Alternative format, good for hierarchical configurations

The format is automatically detected based on file extension.

## Error Handling

All operations return a `Result<T, XdgError>` where `XdgError` provides detailed error information:

```rust
use ligature_xdg::error::XdgError;

match result {
    Ok(value) => println!("Success: {:?}", value),
    Err(XdgError::ConfigNotFound(path)) => println!("Config not found: {}", path),
    Err(XdgError::InvalidComponentName { name, reason }) => {
        println!("Invalid component name '{}': {}", name, reason);
    },
    Err(e) => println!("Other error: {}", e),
}
```

## Component Name Validation

Component names must follow these rules:

- Non-empty
- ASCII alphanumeric characters, hyphens, and underscores only
- Cannot start or end with hyphen or underscore
- Cannot contain consecutive hyphens or underscores

Valid examples: `keywork`, `krox`, `cli`, `lsp`, `test-component`, `test_component`

## Examples

See the `examples/` directory for complete usage examples:

```bash
cargo run --example basic_usage
```

## Integration with Ligature Components

This crate is designed to be used by all Ligature components:

- **keywork**: Package manager configuration and cache
- **krox**: Client configuration and execution cache
- **ligature-cli**: CLI preferences and compilation cache
- **ligature-lsp**: Language server configuration
- **cacophony**: Project configuration and build cache

## License

Apache-2.0
