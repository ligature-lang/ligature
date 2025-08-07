# Baton Lean Engine Plugin

A Lean theorem prover plugin for the Baton verification engine system.

## Overview

The `baton-lean-engine` crate provides a Lean theorem prover plugin that implements the Baton verification engine interface. This plugin wraps the existing `baton-verification` functionality and provides a standardized interface for Lean-based formal verification.

## Features

- **Lean Integration**: Full integration with Lean theorem prover
- **Verification Operations**: Support for evaluation, type checking, theorem verification, and more
- **Configuration Management**: Flexible JSON-based configuration
- **Performance Monitoring**: Built-in statistics and health monitoring
- **Differential Testing**: Support for comparing Rust and Lean results
- **Specification Checking**: Lean specification validation and consistency checking

## Installation

Add the following to your `Cargo.toml`:

```toml
[dependencies]
baton-lean-engine = { path = "./engines/lean" }
baton-engine-plugin = { path = "./crates/baton-engine-plugin" }
```

## Usage

### Basic Usage

```rust
use baton_engine_plugin::prelude::*;
use baton_lean_engine::prelude::*;
use serde_json::json;

#[tokio::main]
async fn main() -> BatonResult<()> {
    // Create a plugin manager
    let manager = EnginePluginManager::new();

    // Create and register the Lean plugin
    let lean_plugin = LeanEnginePlugin::new();
    manager.register_plugin(Box::new(lean_plugin)).await?;

    // Initialize the plugin with configuration
    let config = json!({
        "timeout": 60,
        "enable_cache": true,
        "client_config": {
            "lean_path": "/usr/bin/lean",
            "connection_timeout": 30,
            "request_timeout": 60
        }
    });
    manager.initialize_plugin("lean", &config).await?;

    // Get the Lean engine
    let engine = manager.get_engine("lean").await?;

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

### Advanced Configuration

```rust
use baton_engine_plugin::prelude::*;
use baton_lean_engine::prelude::*;
use serde_json::json;

async fn configure_lean_engine() -> BatonResult<()> {
    let manager = EnginePluginManager::new();

    // Create Lean plugin with custom configuration
    let config = json!({
        "timeout": 120,
        "enable_cache": true,
        "cache_ttl": 7200,
        "run_differential_tests": true,
        "verify_type_safety": true,
        "verify_termination": true,
        "verify_determinism": false,
        "max_concurrent_tasks": 5,
        "enable_performance_monitoring": true,
        "enable_detailed_logging": true,
        "client_config": {
            "lean_path": "/usr/local/bin/lean",
            "connection_timeout": 60,
            "request_timeout": 120,
            "max_retries": 5
        },
        "build_config": {
            "build_timeout": 600,
            "parallel_build": true,
            "clean_build": false
        }
    });

    let lean_plugin = LeanEnginePlugin::with_config(config.clone());
    manager.register_plugin(Box::new(lean_plugin)).await?;
    manager.initialize_plugin("lean", &config).await?;

    // Get plugin information
    let info = manager.get_plugin_info("lean").await?;
    println!("Lean engine info: {:?}", info);

    // Get plugin capabilities
    let capabilities = manager.get_plugin_capabilities("lean").await?;
    println!("Lean capabilities: {:?}", capabilities);

    Ok(())
}
```

### Multiple Verification Operations

```rust
use baton_engine_plugin::prelude::*;
use baton_lean_engine::prelude::*;

async fn perform_verifications(engine: &dyn VerificationEngine) -> BatonResult<()> {
    // Verify expression evaluation
    let eval_response = engine.verify_evaluation(
        "2 + 3 * 4",
        "14",
        None
    ).await?;
    println!("Evaluation result: {:?}", eval_response);

    // Verify type checking
    let type_response = engine.verify_type_check(
        "fun x => x + 1",
        "Nat → Nat",
        None
    ).await?;
    println!("Type check result: {:?}", type_response);

    // Verify theorem
    let theorem_response = engine.verify_theorem(
        "∀ n : Nat, n + 0 = n",
        Some("by induction on n"),
        Some(30),
        None
    ).await?;
    println!("Theorem verification result: {:?}", theorem_response);

    // Run differential test
    let diff_response = engine.run_differential_test(
        "test_expression",
        DifferentialTestType::Evaluation,
        None
    ).await?;
    println!("Differential test result: {:?}", diff_response);

    Ok(())
}
```

## Configuration

The Lean engine plugin supports comprehensive configuration through JSON:

### Top-level Configuration

- `timeout`: Default timeout in seconds (default: 30)
- `enable_cache`: Enable result caching (default: true)
- `cache_ttl`: Cache TTL in seconds (default: 3600)
- `run_differential_tests`: Enable differential testing (default: true)
- `verify_type_safety`: Enable type safety verification (default: true)
- `verify_termination`: Enable termination verification (default: false)
- `verify_determinism`: Enable determinism verification (default: false)
- `max_concurrent_tasks`: Maximum concurrent verification tasks (default: 10)
- `enable_performance_monitoring`: Enable performance monitoring (default: true)
- `enable_detailed_logging`: Enable detailed logging (default: false)

### Client Configuration

- `lean_path`: Path to the Lean executable
- `connection_timeout`: Connection timeout in seconds (default: 30)
- `request_timeout`: Request timeout in seconds (default: 60)
- `max_retries`: Maximum retry attempts (default: 3)

### Build Configuration

- `build_timeout`: Build timeout in seconds (default: 300)
- `parallel_build`: Enable parallel building (default: true)
- `clean_build`: Perform clean build (default: false)

## Supported Operations

The Lean engine plugin supports the following verification operations:

### Core Operations

- ✅ **Expression Evaluation**: Verify expression evaluation results
- ✅ **Type Checking**: Verify type checking results
- ✅ **Theorem Verification**: Verify mathematical theorems
- ✅ **Lemma Verification**: Verify mathematical lemmas
- ✅ **Type Safety**: Verify type safety properties
- ✅ **Termination**: Verify termination properties
- ✅ **Determinism**: Verify determinism properties

### Advanced Operations

- ✅ **Differential Testing**: Compare Rust and Lean results
- ✅ **Result Comparison**: Compare different verification results
- ✅ **Specification Checking**: Validate Lean specifications
- ✅ **Consistency Checking**: Check specification consistency
- ✅ **Invariant Verification**: Verify program invariants
- ✅ **Refinement Verification**: Verify refinement relations

### Future Operations

- 🔄 **Operational Semantics**: Verify operational semantics (planned)
- 🔄 **Test Extraction**: Extract test cases from specifications (planned)
- 🔄 **Counterexample Generation**: Generate counterexamples (planned)

## Performance Characteristics

The Lean engine plugin has the following performance characteristics:

- **Average verification time**: 5 seconds
- **Memory usage**: 512 MB
- **CPU usage**: 75%
- **Throughput**: 0.2 verifications per second
- **Scalability factor**: 0.8
- **Cache efficiency**: 90%

## Error Handling

The plugin uses the standard Baton error types:

```rust
use baton_error::prelude::*;

match engine.verify_evaluation("expr", "expected", None).await {
    Ok(response) => {
        println!("Verification successful: {:?}", response);
    }
    Err(BatonError::VerificationFailed(msg)) => {
        println!("Verification failed: {}", msg);
    }
    Err(BatonError::Timeout(msg)) => {
        println!("Verification timed out: {}", msg);
    }
    Err(e) => {
        println!("Other error: {:?}", e);
    }
}
```

## Testing

Run the tests with:

```bash
cargo test -p baton-lean-engine
```

## Examples

See the `examples/` directory for complete working examples:

```bash
cargo run --example basic_usage -p baton-lean-engine
```

## Dependencies

- `baton-engine-plugin`: Plugin interface
- `baton-verification`: Core verification functionality
- `baton-client`: Lean client communication
- `baton-protocol`: Communication protocol
- `baton-error`: Error handling
- `baton-core`: Core types

## License

This crate is licensed under the Apache 2.0 License.
