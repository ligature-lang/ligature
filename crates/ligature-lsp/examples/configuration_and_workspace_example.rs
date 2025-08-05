//! Example demonstrating configuration and workspace management features.

use ligature_lsp::{config::ConfigurationManager, workspace::WorkspaceManager};
use std::sync::Arc;
use tokio::sync::RwLock;

type MainResult = Result<(), Box<dyn std::error::Error>>;

#[tokio::main]
async fn main() -> MainResult {
    // Initialize logging
    tracing_subscriber::fmt::init();

    println!("=== Ligature LSP Configuration and Workspace Example ===\n");

    // 1. Create a configuration manager
    println!("1. Creating configuration manager...");
    let mut config_manager = ConfigurationManager::new();

    // Load configuration from file if it exists
    let config_path = std::path::PathBuf::from("config_example.json");
    if config_path.exists() {
        println!("   Loading configuration from file...");
        config_manager = ConfigurationManager::from_file(config_path).await?;
        println!("   ✓ Configuration loaded successfully");
    } else {
        println!("   Using default configuration");
    }

    // 2. Validate configuration
    println!("\n2. Validating configuration...");
    let validation_errors = config_manager.validate();
    if validation_errors.is_empty() {
        println!("   ✓ Configuration is valid");
    } else {
        println!("   ⚠ Configuration has errors:");
        for error in &validation_errors {
            println!("     - {error}");
        }
    }

    // 3. Update configuration
    println!("\n3. Updating configuration...");
    let update_json = serde_json::json!({
        "formatting": {
            "indent_size": 4,
            "max_line_length": 120
        },
        "workspace": {
            "max_workspace_files": 2000
        }
    });

    config_manager.update_from_json(&update_json);
    println!("   ✓ Configuration updated");
    println!(
        "   - Indent size: {} spaces",
        config_manager.get_config().formatting.indent_size
    );
    println!(
        "   - Max line length: {} characters",
        config_manager.get_config().formatting.max_line_length
    );
    println!(
        "   - Max workspace files: {}",
        config_manager.get_config().workspace.max_workspace_files
    );

    // 4. Create workspace manager
    println!("\n4. Creating workspace manager...");
    let config = Arc::new(RwLock::new(config_manager.get_config().clone()));
    let _workspace_manager = Arc::new(WorkspaceManager::new(config));
    println!("   ✓ Workspace manager created");

    // 5. Test configuration overrides
    println!("\n5. Testing configuration overrides...");
    let workspace_override = serde_json::json!({
        "formatting": {
            "indent_size": 8
        }
    });

    config_manager.add_workspace_override(
        "file:///tmp/ligature-workspace-1".to_string(),
        workspace_override,
    );

    let workspace_config = config_manager.get_workspace_config("file:///tmp/ligature-workspace-1");
    println!(
        "   - Workspace 1 indent size: {} spaces",
        workspace_config.formatting.indent_size
    );

    let default_config = config_manager.get_workspace_config("file:///tmp/ligature-workspace-2");
    println!(
        "   - Workspace 2 indent size: {} spaces (default)",
        default_config.formatting.indent_size
    );

    // 6. Save configuration
    println!("\n6. Saving configuration...");
    config_manager
        .save_to_file(Some("updated_config.json".into()))
        .await?;
    println!("   ✓ Configuration saved to 'updated_config.json'");

    println!("\n=== Example completed successfully! ===");
    Ok(())
}
