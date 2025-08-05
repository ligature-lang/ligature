# XDG Integration Quick Reference

## For Developers

This quick reference guide shows how to use the `ligature-xdg` crate in your own components or applications.

## Basic Usage

### 1. Add Dependency

Add to your `Cargo.toml`:

```toml
[dependencies]
ligature-xdg = { path = "../ligature-xdg" }
serde = { version = "1.0", features = ["derive"] }
```

### 2. Define Configuration Structure

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MyConfig {
    pub name: String,
    pub version: String,
    pub settings: Settings,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Settings {
    pub enabled: bool,
    pub timeout: u64,
    pub max_retries: u32,
}

impl Default for MyConfig {
    fn default() -> Self {
        Self {
            name: "my-component".to_string(),
            version: "1.0.0".to_string(),
            settings: Settings {
                enabled: true,
                timeout: 30,
                max_retries: 3,
            },
        }
    }
}
```

### 3. Create XDG Configuration Manager

```rust
use ligature_xdg::{config_for_component, XdgPaths};

pub struct MyXdgConfig {
    paths: XdgPaths,
    config_manager: ligature_xdg::XdgConfig,
    config: MyConfig,
}

impl MyXdgConfig {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let paths = XdgPaths::new("my-component")?;
        let config_manager = config_for_component("my-component")?;

        // Ensure directories exist
        paths.ensure_directories().await?;

        // Load existing configuration or use defaults
        let config = if let Some(loaded_config) = config_manager.load::<MyConfig>().await? {
            loaded_config
        } else {
            let default_config = MyConfig::default();
            // Save default configuration
            config_manager.save(&default_config).await?;
            default_config
        };

        Ok(Self {
            paths,
            config_manager,
            config,
        })
    }

    // Get current configuration
    pub fn config(&self) -> &MyConfig {
        &self.config
    }

    // Save configuration
    pub async fn save(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.config_manager.save(&self.config).await?;
        Ok(())
    }

    // Get XDG paths
    pub fn config_dir(&self) -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
        Ok(self.paths.config_dir()?)
    }

    pub fn cache_dir(&self) -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
        Ok(self.paths.cache_dir()?)
    }

    pub fn data_dir(&self) -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
        Ok(self.paths.data_dir()?)
    }

    pub fn state_dir(&self) -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
        Ok(self.paths.state_dir()?)
    }
}
```

## File Format Examples

### JSON Configuration

```rust
use ligature_xdg::config_for_component;

let config_manager = config_for_component("my-component")?;
// Uses config.json by default
```

### YAML Configuration

```rust
use ligature_xdg::yaml_config_for_component;

let config_manager = yaml_config_for_component("my-component")?;
// Uses config.yaml
```

### TOML Configuration

```rust
use ligature_xdg::toml_config_for_component;

let config_manager = toml_config_for_component("my-component")?;
// Uses config.toml
```

## Advanced Usage

### Custom File Names

```rust
use ligature_xdg::XdgConfig;

let config_manager = XdgConfig::new("my-component", "custom-config.json")?;
```

### Multiple Configuration Files

```rust
use ligature_xdg::XdgPaths;

let paths = XdgPaths::new("my-component")?;

// Load from specific file
let config_path = paths.config_file("production.json")?;
let config = serde_json::from_str::<MyConfig>(&std::fs::read_to_string(config_path)?)?;

// Save to specific file
let output_path = paths.config_file("backup.json")?;
std::fs::write(output_path, serde_json::to_string_pretty(&config)?)?;
```

### Error Handling

```rust
use ligature_xdg::error::XdgError;

match result {
    Ok(value) => println!("Success: {:?}", value),
    Err(XdgError::ConfigNotFound(path)) => {
        println!("Configuration not found at: {}", path.display());
        // Create default configuration
    },
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

**Valid examples:**

- `keywork`
- `krox`
- `cli`
- `lsp`
- `test-component`
- `test_component`

**Invalid examples:**

- `-component` (starts with hyphen)
- `component-` (ends with hyphen)
- `test--component` (consecutive hyphens)
- `test__component` (consecutive underscores)
- `test component` (contains space)

## Directory Structure

For a component named "my-component":

```
~/.config/ligature/my-component/
├── config.json          # Default configuration
├── production.json      # Environment-specific config
└── backup.json          # Backup configuration

~/.local/share/ligature/my-component/
├── data.db              # Persistent data
├── templates/           # Template files
└── plugins/             # Plugin files

~/.cache/ligature/my-component/
├── compiled/            # Compiled artifacts
├── temp/                # Temporary files
└── logs/                # Log files

~/.local/state/ligature/my-component/
├── session.json         # Session state
├── locks/               # Lock files
└── runtime/             # Runtime state
```

## Testing

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_config_creation() {
        let config = MyXdgConfig::new().await.unwrap();
        assert_eq!(config.config().name, "my-component");
        assert_eq!(config.config().settings.timeout, 30);
    }

    #[tokio::test]
    async fn test_config_modification() {
        let mut config = MyXdgConfig::new().await.unwrap();

        // Modify configuration
        config.config.settings.timeout = 60;
        config.save().await.unwrap();

        // Reload and verify
        let reloaded = MyXdgConfig::new().await.unwrap();
        assert_eq!(reloaded.config().settings.timeout, 60);
    }

    #[tokio::test]
    async fn test_paths() {
        let config = MyXdgConfig::new().await.unwrap();

        let config_dir = config.config_dir().unwrap();
        let cache_dir = config.cache_dir().unwrap();

        assert!(config_dir.to_string_lossy().contains("my-component"));
        assert!(cache_dir.to_string_lossy().contains("my-component"));
    }
}
```

### Integration Tests

```rust
#[tokio::test]
async fn test_full_workflow() {
    // Create configuration
    let config = MyXdgConfig::new().await.unwrap();

    // Verify directories exist
    assert!(config.config_dir().unwrap().exists());
    assert!(config.cache_dir().unwrap().exists());
    assert!(config.data_dir().unwrap().exists());
    assert!(config.state_dir().unwrap().exists());

    // Verify configuration file exists
    let config_file = config.config_dir().unwrap().join("config.json");
    assert!(config_file.exists());

    // Verify configuration can be loaded
    let loaded_config = serde_json::from_str::<MyConfig>(
        &std::fs::read_to_string(config_file).unwrap()
    ).unwrap();
    assert_eq!(loaded_config.name, "my-component");
}
```

## Best Practices

### 1. **Component Naming**

- Use descriptive, lowercase names
- Use hyphens for multi-word names
- Keep names short but meaningful

### 2. **Configuration Structure**

- Use nested structures for organization
- Provide sensible defaults
- Use strong typing with serde

### 3. **Error Handling**

- Handle XDG errors gracefully
- Provide fallback configurations
- Log errors for debugging

### 4. **File Management**

- Clean up temporary files
- Use appropriate file permissions
- Handle concurrent access

### 5. **Testing**

- Test with temporary directories
- Verify configuration persistence
- Test error conditions

## Migration from Legacy Systems

If migrating from a legacy configuration system:

```rust
use std::path::Path;

pub async fn migrate_legacy_config(
    legacy_path: &Path,
    component_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let xdg_config = MyXdgConfig::new().await?;

    // Load legacy configuration
    if legacy_path.exists() {
        let legacy_config = std::fs::read_to_string(legacy_path)?;
        let config: MyConfig = serde_json::from_str(&legacy_config)?;

        // Save to XDG location
        xdg_config.config_manager.save(&config).await?;

        // Backup legacy file
        let backup_path = legacy_path.with_extension("backup");
        std::fs::rename(legacy_path, backup_path)?;

        println!("Migrated configuration from {} to XDG location", legacy_path.display());
    }

    Ok(())
}
```

## Environment Variable Support

```rust
use std::env;

pub fn get_custom_xdg_home() -> Option<std::path::PathBuf> {
    env::var("MY_COMPONENT_XDG_HOME")
        .ok()
        .map(|s| s.into())
}

pub async fn create_with_custom_path() -> Result<MyXdgConfig, Box<dyn std::error::Error>> {
    if let Some(custom_path) = get_custom_xdg_home() {
        // Use custom XDG home directory
        env::set_var("XDG_CONFIG_HOME", custom_path.join("config"));
        env::set_var("XDG_CACHE_HOME", custom_path.join("cache"));
        env::set_var("XDG_DATA_HOME", custom_path.join("data"));
        env::set_var("XDG_STATE_HOME", custom_path.join("state"));
    }

    MyXdgConfig::new().await
}
```

This quick reference provides the essential information needed to integrate XDG support into your Ligature components. For more detailed information, see the main [XDG Integration Guide](xdg-integration.md).
