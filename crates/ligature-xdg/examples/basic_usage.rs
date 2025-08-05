//! Basic usage example for the ligature-xdg crate.

use ligature_xdg::{config_for_component, XdgPaths};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct ExampleConfig {
    name: String,
    version: String,
    settings: Settings,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct Settings {
    enabled: bool,
    timeout: u64,
    max_retries: u32,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature XDG Configuration Example ===\n");

    // Example 1: Basic XDG paths
    println!("1. XDG Paths for 'example' component:");
    let paths = XdgPaths::new("example")?;
    println!("   Config dir: {}", paths.config_dir()?.display());
    println!("   Data dir: {}", paths.data_dir()?.display());
    println!("   Cache dir: {}", paths.cache_dir()?.display());
    println!("   State dir: {}", paths.state_dir()?.display());
    println!();

    // Example 2: Configuration management
    println!("2. Configuration Management:");
    let config_manager = config_for_component("example")?;
    println!("   Component: {}", config_manager.component());
    println!("   Default config file: {}", config_manager.default_filename());
    println!("   Config path: {}", config_manager.default_config_path()?.display());
    println!();

    // Example 3: Save and load configuration
    println!("3. Save and Load Configuration:");
    
    // Create a sample configuration
    let sample_config = ExampleConfig {
        name: "example-app".to_string(),
        version: "1.0.0".to_string(),
        settings: Settings {
            enabled: true,
            timeout: 30,
            max_retries: 3,
        },
    };

    // Save the configuration
    let saved_path = config_manager.save(&sample_config).await?;
    println!("   Saved config to: {}", saved_path.display());

    // Load the configuration
    let loaded_config = config_manager.load::<ExampleConfig>().await?.unwrap();
    println!("   Loaded config: {:?}", loaded_config);
    println!("   Config matches: {}", loaded_config == sample_config);
    println!();

    // Example 4: Different file formats
    println!("4. Different File Formats:");
    
    // JSON config
    let json_config = config_for_component("example-json")?;
    let json_path = json_config.save(&sample_config).await?;
    println!("   JSON config saved to: {}", json_path.display());

    // YAML config
    let yaml_config = ligature_xdg::yaml_config_for_component("example-yaml")?;
    let yaml_path = yaml_config.save(&sample_config).await?;
    println!("   YAML config saved to: {}", yaml_path.display());

    // TOML config
    let toml_config = ligature_xdg::toml_config_for_component("example-toml")?;
    let toml_path = toml_config.save(&sample_config).await?;
    println!("   TOML config saved to: {}", toml_path.display());
    println!();

    // Example 5: Directory creation
    println!("5. Directory Creation:");
    let paths = XdgPaths::new("example-dirs")?;
    paths.ensure_directories().await?;
    println!("   Created directories for component: {}", paths.component());
    println!("   Config dir exists: {}", paths.config_dir()?.exists());
    println!("   Data dir exists: {}", paths.data_dir()?.exists());
    println!("   Cache dir exists: {}", paths.cache_dir()?.exists());
    println!("   State dir exists: {}", paths.state_dir()?.exists());
    println!();

    // Example 6: File path utilities
    println!("6. File Path Utilities:");
    let paths = XdgPaths::new("example-files")?;
    println!("   Config file: {}", paths.config_file("settings.json")?.display());
    println!("   Data file: {}", paths.data_file("data.db")?.display());
    println!("   Cache file: {}", paths.cache_file("cache.dat")?.display());
    println!("   State file: {}", paths.state_file("state.json")?.display());
    println!();

    println!("=== Example completed successfully! ===");
    Ok(())
} 