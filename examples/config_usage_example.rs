//! Example demonstrating how to use the Ligature evaluator configuration system.
//!
//! This example shows:
//! - Loading configuration from files
//! - Creating evaluators with custom configuration
//! - Applying configuration at runtime
//! - Saving configuration files

use ligature_eval::{
    config::{ConfigFormat, EvaluatorConfig, EvaluatorConfigManager},
    Evaluator,
};
use std::path::PathBuf;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Evaluator Configuration Example ===\n");

    // Example 1: Create evaluator with default configuration
    println!("1. Creating evaluator with default configuration...");
    let mut evaluator = Evaluator::new();
    println!(
        "   Default cache size: {}",
        evaluator.config().cache.max_size
    );
    println!(
        "   Default cache memory: {} bytes",
        evaluator.config().cache.max_memory_bytes
    );
    println!();

    // Example 2: Create evaluator with custom configuration
    println!("2. Creating evaluator with custom configuration...");
    let mut custom_config = EvaluatorConfig::default();
    custom_config.cache.max_size = 5000;
    custom_config.cache.max_memory_bytes = 5 * 1024 * 1024; // 5MB
    custom_config.performance.max_stack_depth = 20000;
    custom_config.debug.cache_statistics = true;

    let custom_evaluator = Evaluator::with_config(custom_config);
    println!(
        "   Custom cache size: {}",
        custom_evaluator.config().cache.max_size
    );
    println!(
        "   Custom cache memory: {} bytes",
        custom_evaluator.config().cache.max_memory_bytes
    );
    println!();

    // Example 3: Load configuration from global files
    println!("3. Loading configuration from global files...");
    match Evaluator::with_config_from_files(None).await {
        Ok(loaded_evaluator) => {
            println!("   Successfully loaded global configuration");
            println!(
                "   Cache enabled: {}",
                loaded_evaluator.config().cache.enabled
            );
            println!(
                "   Cache size: {}",
                loaded_evaluator.config().cache.max_size
            );
        }
        Err(e) => {
            println!("   No global configuration found (this is normal): {}", e);
        }
    }
    println!();

    // Example 4: Load configuration from project-specific file
    println!("4. Loading configuration from project file...");
    let project_config = PathBuf::from("examples/evaluator_config_example.toml");
    match Evaluator::with_config_from_files(Some(project_config)).await {
        Ok(project_evaluator) => {
            println!("   Successfully loaded project configuration");
            println!(
                "   Cache enabled: {}",
                project_evaluator.config().cache.enabled
            );
            println!(
                "   Cache size: {}",
                project_evaluator.config().cache.max_size
            );
            println!(
                "   Cache warming enabled: {}",
                project_evaluator.config().cache.warming.enabled
            );
        }
        Err(e) => {
            println!("   Failed to load project configuration: {}", e);
        }
    }
    println!();

    // Example 5: Apply configuration at runtime
    println!("5. Applying configuration at runtime...");
    let mut runtime_evaluator = Evaluator::new();
    println!(
        "   Initial cache size: {}",
        runtime_evaluator.config().cache.max_size
    );

    let mut new_config = EvaluatorConfig::default();
    new_config.cache.max_size = 10000;
    new_config.cache.max_memory_bytes = 10 * 1024 * 1024; // 10MB
    new_config.performance.tail_call_optimization = false;
    new_config.debug.logging = true;

    runtime_evaluator.apply_config(new_config);
    println!(
        "   Updated cache size: {}",
        runtime_evaluator.config().cache.max_size
    );
    println!(
        "   TCO enabled: {}",
        runtime_evaluator
            .config()
            .performance
            .tail_call_optimization
    );
    println!(
        "   Logging enabled: {}",
        runtime_evaluator.config().debug.logging
    );
    println!();

    // Example 6: Save configuration to different formats
    println!("6. Saving configuration to different formats...");
    let config_manager = EvaluatorConfigManager::new()?;

    // Save as TOML
    match config_manager.save_default_config(ConfigFormat::Toml).await {
        Ok(path) => println!("   Saved TOML config to: {}", path.display()),
        Err(e) => println!("   Failed to save TOML config: {}", e),
    }

    // Save as JSON
    match config_manager.save_default_config(ConfigFormat::Json).await {
        Ok(path) => println!("   Saved JSON config to: {}", path.display()),
        Err(e) => println!("   Failed to save JSON config: {}", e),
    }

    // Save as YAML
    match config_manager.save_default_config(ConfigFormat::Yaml).await {
        Ok(path) => println!("   Saved YAML config to: {}", path.display()),
        Err(e) => println!("   Failed to save YAML config: {}", e),
    }
    println!();

    // Example 7: Demonstrate configuration hierarchy
    println!("7. Configuration hierarchy demonstration...");
    let mut base_config = EvaluatorConfig::default();
    base_config.cache.max_size = 1000;
    base_config.cache.max_memory_bytes = 1024 * 1024;
    base_config.debug.log_level = ligature_eval::config::LogLevel::Info;

    let mut override_config = EvaluatorConfig::default();
    override_config.cache.max_size = 2000;
    override_config.debug.log_level = ligature_eval::config::LogLevel::Debug;

    let merged_config = config_manager.merge_configs(base_config, override_config);
    println!("   Base cache size: 1000");
    println!("   Override cache size: 2000");
    println!("   Merged cache size: {}", merged_config.cache.max_size);
    println!("   Merged log level: {:?}", merged_config.debug.log_level);
    println!();

    // Example 8: Show cacheable expressions configuration
    println!("8. Cacheable expressions configuration...");
    let cacheable = &runtime_evaluator.config().cache.cacheable_expressions;
    println!("   Cache literals: {}", cacheable.literals);
    println!("   Cache variables: {}", cacheable.variables);
    println!("   Cache binary operations: {}", cacheable.binary_ops);
    println!("   Cache unary operations: {}", cacheable.unary_ops);
    println!("   Cache field access: {}", cacheable.field_access);
    println!("   Cache applications: {}", cacheable.applications);
    println!("   Cache let expressions: {}", cacheable.let_expressions);
    println!("   Cache records: {}", cacheable.records);
    println!("   Cache unions: {}", cacheable.unions);
    println!("   Cache matches: {}", cacheable.matches);
    println!("   Cache if expressions: {}", cacheable.if_expressions);
    println!();

    println!("=== Configuration Example Complete ===");
    println!();
    println!("Configuration files can be placed in:");
    println!("  - Global: ~/.config/ligature/eval.toml (or .json/.yaml)");
    println!("  - Project: ./eval.toml (or .json/.yaml) in your project directory");
    println!();
    println!("The system supports TOML, JSON, and YAML formats.");
    println!("Project configuration overrides global configuration.");

    Ok(())
}
