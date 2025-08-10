//! Command-line interface for Krox.

use clap::{Parser, Subcommand};
use tracing::info;

use crate::cache::EvictionPolicy;
use crate::error::{Error, Result};
use crate::{ClientBuilder, ExecutionMode};

/// Krox CLI - Client SDKs for invoking Ligature programs as side effects
#[derive(Parser)]
#[command(name = "krox")]
#[command(about = "Execute Ligature programs with caching and multiple execution modes")]
#[command(version)]
pub struct Cli {
    /// Execution mode
    #[arg(long, value_enum, default_value_t = ExecutionMode::Native)]
    mode: ExecutionMode,

    /// Enable caching
    #[arg(long, default_value_t = true)]
    cache: bool,

    /// Cache directory
    #[arg(long)]
    cache_dir: Option<String>,

    /// HTTP endpoint for remote execution
    #[arg(long)]
    http_endpoint: Option<String>,

    /// Path to ligature-cli binary
    #[arg(long)]
    ligature_cli_path: Option<String>,

    /// Request timeout in seconds
    #[arg(long, default_value_t = 30)]
    timeout: u64,

    /// Configuration file path
    #[arg(long)]
    config: Option<String>,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Output format
    #[arg(long, value_enum, default_value_t = OutputFormat::Pretty)]
    output: OutputFormat,

    /// Command to execute
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Execute a Ligature program from a file
    Execute {
        /// Path to the Ligature program file
        file: String,
    },
    /// Execute a Ligature program from source code
    Eval {
        /// Source code to execute
        source: String,
    },
    /// Cache management commands
    Cache {
        #[command(subcommand)]
        command: CacheCommands,
    },
    /// Show configuration
    Config {
        /// Output format
        #[arg(long, value_enum, default_value_t = ConfigFormat::Yaml)]
        format: ConfigFormat,
    },
}

#[derive(Subcommand)]
enum CacheCommands {
    /// Show cache statistics
    Stats,
    /// Clear the cache
    Clear,
    /// Validate cache integrity
    Validate,
    /// Set eviction policy
    SetPolicy {
        /// Eviction policy to use
        #[arg(value_enum)]
        policy: EvictionPolicy,
    },
    /// Set cache maximum age (in seconds)
    SetMaxAge {
        /// Maximum age in seconds
        age: u64,
    },
    /// Set cache maximum size (in bytes)
    SetMaxSize {
        /// Maximum size in bytes
        size: u64,
    },
}

#[derive(clap::ValueEnum, Clone)]
enum OutputFormat {
    Json,
    Yaml,
    Pretty,
}

#[derive(clap::ValueEnum, Clone)]
enum ConfigFormat {
    Json,
    Yaml,
}

impl Cli {
    /// Run the CLI application.
    pub async fn run() -> Result<()> {
        let cli = Cli::parse();

        // Initialize logging
        if cli.verbose {
            tracing_subscriber::fmt()
                .with_env_filter("krox=debug")
                .init();
        } else {
            tracing_subscriber::fmt()
                .with_env_filter("krox=info")
                .init();
        }

        // Load configuration if specified
        let config = if let Some(config_path) = cli.config {
            crate::config::ConfigManager::from_file(config_path).await?
        } else {
            crate::config::ConfigManager::new()
        };

        // Build client
        let mut builder = ClientBuilder::new()
            .execution_mode(cli.mode)
            .enable_cache(cli.cache)
            .http_timeout(std::time::Duration::from_secs(cli.timeout))
            .verbose(cli.verbose);

        if let Some(cache_dir) = cli.cache_dir {
            builder = builder.cache_dir(cache_dir);
        }

        if let Some(http_endpoint) = cli.http_endpoint {
            builder = builder.http_endpoint(http_endpoint);
        }

        if let Some(ligature_cli_path) = cli.ligature_cli_path {
            builder = builder.ligature_cli_path(ligature_cli_path);
        }

        let client = builder.build().await?;

        // Execute command
        match cli.command {
            Some(Commands::Execute { file }) => {
                let result = client.execute_file(&file).await?;
                Self::print_result(&result, cli.output)?;
            }
            Some(Commands::Eval { source }) => {
                let result = client.execute_source(&source).await?;
                Self::print_result(&result, cli.output)?;
            }
            Some(Commands::Cache { command }) => {
                Self::handle_cache(client, command).await?;
            }
            Some(Commands::Config { format }) => {
                Self::show_config(config, format).await?;
            }
            None => {
                // Default behavior: show help
                let _ = Cli::try_parse_from(["krox", "--help"]);
            }
        }

        Ok(())
    }

    /// Handle cache commands.
    async fn handle_cache(mut client: crate::Client, command: CacheCommands) -> Result<()> {
        match command {
            CacheCommands::Stats => {
                if let Some(stats) = client.cache_stats().await? {
                    println!("Cache Statistics:");
                    println!("  Total entries: {}", stats.total_entries);
                    println!("  Hits: {}", stats.hits);
                    println!("  Misses: {}", stats.misses);
                    println!("  Hit rate: {:.2}%", stats.hit_rate * 100.0);
                    println!("  Total size: {} bytes", stats.total_size);
                    println!("  Cache directory: {}", stats.cache_dir);
                    println!("  Evicted entries: {}", stats.evicted_entries);
                    println!("  Invalid entries: {}", stats.invalid_entries);
                } else {
                    println!("Caching is disabled");
                }
            }
            CacheCommands::Clear => {
                client.clear_cache().await?;
                println!("Cache cleared");
            }
            CacheCommands::Validate => {
                client.validate_cache().await?;
                println!("Cache validation completed");
            }
            CacheCommands::SetPolicy { policy } => {
                client.set_cache_eviction_policy(policy)?;
                println!("Cache eviction policy set to {:?}", policy);
            }
            CacheCommands::SetMaxAge { age } => {
                client.set_cache_max_age(std::time::Duration::from_secs(age))?;
                println!("Cache maximum age set to {} seconds", age);
            }
            CacheCommands::SetMaxSize { size } => {
                client.set_cache_max_size(size)?;
                println!("Cache maximum size set to {} bytes", size);
            }
        }
        Ok(())
    }

    /// Show configuration.
    async fn show_config(config: crate::config::ConfigManager, format: ConfigFormat) -> Result<()> {
        let config_data = config.config();

        match format {
            ConfigFormat::Json => {
                let json =
                    serde_json::to_string_pretty(config_data).map_err(Error::JsonSerialization)?;
                println!("{json}");
            }
            ConfigFormat::Yaml => {
                let yaml = serde_yaml::to_string(config_data).map_err(Error::YamlSerialization)?;
                println!("{yaml}");
            }
        }
        Ok(())
    }

    /// Print execution result in the specified format.
    fn print_result(result: &crate::ExecutionResult, format: OutputFormat) -> Result<()> {
        match format {
            OutputFormat::Json => {
                let json = serde_json::to_string_pretty(result).map_err(Error::JsonSerialization)?;
                println!("{json}");
            }
            OutputFormat::Yaml => {
                let yaml = serde_yaml::to_string(result).map_err(Error::YamlSerialization)?;
                println!("{yaml}");
            }
            OutputFormat::Pretty => {
                println!("Execution Result:");
                println!("  Value: {:?}", result.value);
                println!("  Duration: {:?}", result.metadata.duration);
                println!("  Cached: {}", result.metadata.cached);
                println!("  Mode: {:?}", result.metadata.mode);
                if !result.metadata.warnings.is_empty() {
                    println!("  Warnings:");
                    for warning in &result.metadata.warnings {
                        println!("    - {}", warning);
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cli_parsing() {
        let cli = Cli::try_parse_from(["krox", "--help"]);
        assert!(cli.is_ok());
    }

    #[test]
    fn test_cli_help() {
        let cli = Cli::try_parse_from(["krox", "cache", "--help"]);
        assert!(cli.is_ok());
    }
}
