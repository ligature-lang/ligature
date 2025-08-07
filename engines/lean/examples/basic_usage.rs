//! Basic usage example for the baton-lean-engine plugin.
//!
//! This example demonstrates how to use the Lean engine plugin with the
//! baton-engine-plugin system.

use baton_engine_plugin::prelude::*;
use baton_lean_engine::prelude::*;
use serde_json::json;

#[tokio::main]
async fn main() -> BatonResult<()> {
    println!("=== Baton Lean Engine Plugin Example ===\n");

    // Create a plugin manager
    let manager = EnginePluginManager::new();
    println!("Created plugin manager");

    // Create and register the Lean plugin
    let lean_plugin = LeanEnginePlugin::new();
    manager.register_plugin(Box::new(lean_plugin)).await?;
    println!("Registered Lean plugin");

    // Initialize the plugin with configuration
    let config = json!({
        "timeout": 30,
        "enable_cache": true,
        "client_config": {
            "lean_path": "/usr/bin/lean",
            "connection_timeout": 10,
            "request_timeout": 30
        }
    });
    manager.initialize_plugin("lean", &config).await?;
    println!("Initialized Lean plugin");

    // Get plugin information
    let info = manager.get_plugin_info("lean").await?;
    println!("Plugin info: {info:?}");

    // Get plugin capabilities
    let capabilities = manager.get_plugin_capabilities("lean").await?;
    println!("Plugin capabilities: {capabilities:?}");

    // Get plugin status
    let status = manager.get_plugin_status("lean").await?;
    println!("Plugin status: {status:?}");

    // List all plugins
    let plugins = manager.list_plugins().await;
    println!("Registered plugins: {plugins:?}");

    // Get manager statistics
    let stats = manager.get_stats().await;
    println!("Manager stats: {stats:?}");

    // Note: The current implementation doesn't support engine cloning,
    // so we can't demonstrate actual verification usage yet.
    // This would be implemented in a future version.
    println!("\nNote: Engine usage demonstration requires engine cloning support");

    // Health check
    let health = manager.health_check().await;
    println!("Health status: {health:?}");

    // Shutdown
    manager.shutdown_all().await?;
    println!("Shutdown complete");

    println!("\n=== Example completed successfully ===");
    Ok(())
}
