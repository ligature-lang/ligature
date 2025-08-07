# Baton Engine Plugin

A plugin interface for Baton verification engines that allows multiple provers to be registered and used interchangeably.

## Overview

The `baton-engine-plugin` crate provides a plugin system for different verification engines that can be used with the Baton formal verification system. This allows you to:

- Register multiple verification engines (e.g., Lean, Coq, Isabelle, etc.)
- Switch between engines dynamically
- Use different engines for different types of verification tasks
- Extend the system with custom verification engines

## Features

- **Plugin Management**: Register, initialize, and manage multiple verification engine plugins
- **Engine Abstraction**: Common interface for all verification engines
- **Capability Discovery**: Query engine capabilities and supported features
- **Configuration Management**: Configure engines with JSON-based configuration
- **Health Monitoring**: Monitor engine health and status
- **Statistics Collection**: Collect performance and usage statistics

## Usage

### Basic Usage

```rust
use baton_engine_plugin::prelude::*;
use serde_json::json;

#[tokio::main]
async fn main() -> BatonResult<()> {
    // Create a plugin manager
    let manager = EnginePluginManager::new();

    // Register a plugin (example with a hypothetical Lean plugin)
    let lean_plugin = LeanEnginePlugin::new();
    manager.register_plugin(Box::new(lean_plugin)).await?;

    // Initialize the plugin with configuration
    let config = json!({
        "lean_path": "/usr/bin/lean",
        "timeout": 30,
        "memory_limit": 1024
    });
    manager.initialize_plugin("lean", &config).await?;

    // Get the default engine
    let engine = manager.get_default_engine().await?;

    // Use the engine for verification
    let response = engine.verify_evaluation(
        "1 + 1",
        "2",
        None
    ).await?;

    println!("Verification result: {:?}", response);

    Ok(())
}
```

### Plugin Implementation

To create a new verification engine plugin, implement the `EnginePlugin` and `VerificationEngine` traits:

```rust
use baton_engine_plugin::prelude::*;
use async_trait::async_trait;

struct MyEnginePlugin {
    engine: Option<MyEngine>,
    config: Value,
}

impl MyEnginePlugin {
    fn new() -> Self {
        Self {
            engine: None,
            config: Value::Null,
        }
    }
}

#[async_trait]
impl EnginePlugin for MyEnginePlugin {
    fn name(&self) -> &str {
        "my-engine"
    }

    fn version(&self) -> &str {
        "1.0.0"
    }

    fn description(&self) -> &str {
        "My custom verification engine"
    }

    fn engine_info(&self) -> EngineInfo {
        EngineInfo {
            name: "My Engine".to_string(),
            version: "1.0.0".to_string(),
            description: "A custom verification engine".to_string(),
            vendor: "My Company".to_string(),
            homepage: Some("https://example.com".to_string()),
            documentation: None,
            license: Some("MIT".to_string()),
            supported_languages: vec!["rust".to_string()],
            supported_features: vec!["evaluation".to_string(), "type_checking".to_string()],
            config_schema: None,
        }
    }

    fn capabilities(&self) -> EngineCapabilities {
        EngineCapabilities {
            supports_evaluation: true,
            supports_type_checking: true,
            supports_theorem_verification: false,
            // ... other capabilities
            ..Default::default()
        }
    }

    async fn initialize(&mut self, config: &Value) -> BatonResult<()> {
        self.config = config.clone();
        self.engine = Some(MyEngine::new(config)?);
        Ok(())
    }

    async fn shutdown(&mut self) -> BatonResult<()> {
        self.engine = None;
        Ok(())
    }

    async fn status(&self) -> BatonResult<EngineStatus> {
        if self.engine.is_some() {
            Ok(EngineStatus::Ready)
        } else {
            Ok(EngineStatus::Uninitialized)
        }
    }

    async fn configure(&mut self, config: &Value) -> BatonResult<()> {
        self.config = config.clone();
        if let Some(ref mut engine) = self.engine {
            engine.configure(config)?;
        }
        Ok(())
    }

    fn get_engine(&self) -> BatonResult<Box<dyn VerificationEngine>> {
        if let Some(ref engine) = self.engine {
            Ok(Box::new(engine.clone()))
        } else {
            Err(BatonError::NotInitialized("Engine not initialized".to_string()))
        }
    }
}

#[async_trait]
impl VerificationEngine for MyEngine {
    async fn verify_evaluation(
        &self,
        expression: &str,
        expected_value: &str,
        context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        // Implement evaluation verification logic
        let result = self.evaluate(expression, context).await?;

        let response = if result == expected_value {
            LeanResponse::VerificationSuccess {
                result: result.clone(),
                proof: None,
                proof_steps: None,
                execution_time: Some(100),
            }
        } else {
            LeanResponse::VerificationFailure {
                error: format!("Expected {}, got {}", expected_value, result),
                details: None,
                error_type: Some(ErrorType::Semantics),
                suggestions: None,
            }
        };

        Ok(VerificationResponse::new(response, 100))
    }

    // Implement other verification methods...
    async fn verify_type_check(
        &self,
        _expression: &str,
        _expected_type: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        todo!("Implement type checking")
    }

    // ... implement all other required methods
}
```

### Multiple Engine Management

```rust
use baton_engine_plugin::prelude::*;

async fn manage_multiple_engines() -> BatonResult<()> {
    let manager = EnginePluginManager::new();

    // Register multiple engines
    manager.register_plugin(Box::new(LeanEnginePlugin::new())).await?;
    manager.register_plugin(Box::new(CoqEnginePlugin::new())).await?;
    manager.register_plugin(Box::new(IsabelleEnginePlugin::new())).await?;

    // Initialize all engines
    let lean_config = json!({"lean_path": "/usr/bin/lean"});
    let coq_config = json!({"coq_path": "/usr/bin/coq"});
    let isabelle_config = json!({"isabelle_path": "/usr/bin/isabelle"});

    manager.initialize_plugin("lean", &lean_config).await?;
    manager.initialize_plugin("coq", &coq_config).await?;
    manager.initialize_plugin("isabelle", &isabelle_config).await?;

    // List all plugins
    let plugins = manager.list_plugins().await;
    println!("Available plugins: {:?}", plugins);

    // Get capabilities of each engine
    for plugin_name in &plugins {
        let capabilities = manager.get_plugin_capabilities(plugin_name).await?;
        println!("{} capabilities: {:?}", plugin_name, capabilities);
    }

    // Set default engine
    manager.set_default_engine("lean").await?;

    // Use specific engine
    let lean_engine = manager.get_engine("lean").await?;
    let coq_engine = manager.get_engine("coq").await?;

    // Compare results from different engines
    let lean_result = lean_engine.verify_evaluation("1 + 1", "2", None).await?;
    let coq_result = coq_engine.verify_evaluation("1 + 1", "2", None).await?;

    // Health check
    let health_status = manager.health_check().await;
    println!("Engine health: {:?}", health_status);

    Ok(())
}
```

## API Reference

### Core Types

- `EnginePluginManager`: Manages plugin registration and lifecycle
- `EnginePlugin`: Trait for verification engine plugins
- `VerificationEngine`: Trait for verification engines
- `EngineInfo`: Information about an engine
- `EngineCapabilities`: Capabilities of an engine
- `EngineStatus`: Status of an engine

### Key Methods

#### EnginePluginManager

- `register_plugin(plugin)`: Register a new plugin
- `unregister_plugin(name)`: Unregister a plugin
- `initialize_plugin(name, config)`: Initialize a plugin with configuration
- `get_engine(name)`: Get a specific engine
- `get_default_engine()`: Get the default engine
- `set_default_engine(name)`: Set the default engine
- `list_plugins()`: List all registered plugins
- `health_check()`: Check health of all engines

#### EnginePlugin

- `name()`: Get plugin name
- `version()`: Get plugin version
- `description()`: Get plugin description
- `engine_info()`: Get engine information
- `capabilities()`: Get engine capabilities
- `initialize(config)`: Initialize the plugin
- `shutdown()`: Shutdown the plugin
- `status()`: Get plugin status
- `configure(config)`: Configure the plugin
- `get_engine()`: Get the verification engine

#### VerificationEngine

- `verify_evaluation(expr, expected, context)`: Verify expression evaluation
- `verify_type_check(expr, expected_type, context)`: Verify type checking
- `verify_theorem(theorem, proof, timeout, context)`: Verify theorem
- `run_differential_test(test_case, test_type, context)`: Run differential test
- `get_version()`: Get engine version
- `ping()`: Ping the engine
- `get_stats()`: Get engine statistics
- `get_health_status()`: Get engine health status

## Configuration

Engines can be configured using JSON configuration objects:

```json
{
  "engine_config": {
    "path": "/usr/bin/lean",
    "args": ["--json"],
    "environment": {
      "LEAN_PATH": "/usr/lib/lean"
    }
  },
  "timeout_config": {
    "default_timeout": 30,
    "max_timeout": 300,
    "evaluation_timeout": 10,
    "theorem_timeout": 60
  },
  "performance_config": {
    "max_concurrent_requests": 10,
    "memory_limit_mb": 1024,
    "cpu_limit_percent": 80.0
  },
  "logging_config": {
    "log_level": "info",
    "structured_logging": true,
    "enable_request_logging": false
  },
  "cache_config": {
    "enable_cache": true,
    "cache_ttl": 3600,
    "max_cache_size_mb": 100
  }
}
```

## Error Handling

The crate uses the `BatonError` type for error handling:

```rust
use baton_error::prelude::*;

match manager.get_engine("nonexistent").await {
    Ok(engine) => {
        // Use engine
    }
    Err(BatonError::NotFound(msg)) => {
        println!("Engine not found: {}", msg);
    }
    Err(BatonError::NotInitialized(msg)) => {
        println!("Engine not initialized: {}", msg);
    }
    Err(e) => {
        println!("Other error: {:?}", e);
    }
}
```

## Testing

The crate includes comprehensive tests for the plugin system:

```bash
cargo test
```

## Contributing

To add a new verification engine:

1. Implement the `EnginePlugin` and `VerificationEngine` traits
2. Add tests for your implementation
3. Update documentation with usage examples
4. Submit a pull request

## License

This crate is licensed under the Apache 2.0 License.
