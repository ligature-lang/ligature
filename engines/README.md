# Engines

This directory contains verification engines that integrate with the Ligature language ecosystem, particularly the Baton verification engine system.

## Overview

The engines in this directory provide formal verification capabilities for Ligature programs and configurations. They implement the Baton verification engine interface, allowing for standardized verification operations across different theorem provers and verification tools.

## Available Engines

### Lean Engine (`lean/`)

The **Baton Lean Engine Plugin** provides integration with the Lean theorem prover for formal verification of Ligature programs.

**Features:**

- Full integration with Lean theorem prover
- Verification operations (evaluation, type checking, theorem verification)
- Configuration management with JSON-based configuration
- Performance monitoring and health checks
- Differential testing support
- Specification validation and consistency checking

**Quick Start:**

```rust
use baton_engine_plugin::prelude::*;
use baton_lean_engine::prelude::*;

let manager = EnginePluginManager::new();
let lean_plugin = LeanEnginePlugin::new();
manager.register_plugin(Box::new(lean_plugin)).await?;
```

For detailed usage and configuration, see the [Lean Engine README](lean/README.md).

## Architecture

### Baton Verification Engine System

The engines in this directory are built on the Baton verification engine system, which provides:

- **Plugin Architecture**: Standardized interface for different verification engines
- **Configuration Management**: Flexible configuration for each engine
- **Performance Monitoring**: Built-in statistics and health monitoring
- **Differential Testing**: Support for comparing results across different engines
- **Async Operations**: Non-blocking verification operations

### Engine Interface

All engines implement the `EnginePlugin` trait, providing:

- **Initialization**: Engine setup and configuration
- **Verification Operations**: Core verification functionality
- **Health Monitoring**: Engine status and performance metrics
- **Resource Management**: Proper cleanup and resource handling

## Adding New Engines

To add a new verification engine:

1. Create a new directory in `engines/`
2. Implement the `EnginePlugin` trait from `baton-engine-plugin`
3. Add the engine to the workspace in the root `Cargo.toml`
4. Create comprehensive documentation and examples
5. Add tests and integration with the verification system

### Example Engine Structure

```
engines/your-engine/
├── Cargo.toml
├── README.md
├── src/
│   ├── lib.rs
│   ├── engine.rs
│   └── plugin.rs
├── examples/
│   └── basic_usage.rs
└── spec/
    └── engine_spec.md
```

## Dependencies

Engines depend on the following core crates:

- `baton-engine-plugin`: Core plugin interface and management
- `baton-core`: Core verification functionality
- `baton-protocol`: Communication protocols
- `baton-error`: Error handling and types

## Contributing

When contributing to engines:

1. Follow the existing code style and patterns
2. Add comprehensive tests for all functionality
3. Update documentation for any new features
4. Ensure proper error handling and resource management
5. Add examples demonstrating usage patterns

## Related Documentation

- [Baton Engine Plugin Documentation](../../crates/baton-engine-plugin/README.md)
- [Ligature Language Documentation](../../README.md)
- [Verification System Architecture](../../docs/architecture/)
