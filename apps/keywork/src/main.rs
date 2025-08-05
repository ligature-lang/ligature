//! Package management CLI for Ligature registers.

use clap::{Parser, Subcommand};
use miette::Result;
use std::path::PathBuf;

mod commands;
mod dependency;
pub mod register;
mod registry;
mod xdg_config;

use commands::*;

#[derive(Parser)]
#[command(name = "keywork")]
#[command(about = "Package management for Ligature registers")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize a new register
    Init {
        /// Name of the register to create
        #[arg(value_name = "NAME")]
        name: String,

        /// Directory to create the register in
        #[arg(long, default_value = ".")]
        directory: PathBuf,
    },

    /// Build a register
    Build {
        /// Path to the register directory
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,

        /// Output directory for build artifacts
        #[arg(long, default_value = "dist")]
        output: PathBuf,
    },

    /// Install a register
    Install {
        /// Register name to install
        #[arg(value_name = "REGISTER")]
        register: String,

        /// Version to install (defaults to latest)
        #[arg(long)]
        version: Option<String>,

        /// Install globally
        #[arg(long)]
        global: bool,
    },

    /// Publish a register to the registry
    Publish {
        /// Path to the register directory
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,

        /// Registry URL
        #[arg(long)]
        registry: Option<String>,
    },

    /// List installed registers
    List {
        /// Show detailed information
        #[arg(long)]
        verbose: bool,

        /// Show only global registers
        #[arg(long)]
        global: bool,
    },

    /// Remove a register
    Remove {
        /// Register name to remove
        #[arg(value_name = "REGISTER")]
        register: String,

        /// Remove globally
        #[arg(long)]
        global: bool,
    },

    /// Update register dependencies
    Update {
        /// Path to the register directory
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,

        /// Update all dependencies
        #[arg(long)]
        all: bool,

        /// Specific dependency to update
        #[arg(long)]
        dependency: Option<String>,
    },

    /// Show register information
    Info {
        /// Register name or path
        #[arg(value_name = "REGISTER")]
        register: String,
    },

    /// Search for registers
    Search {
        /// Search query
        #[arg(value_name = "QUERY")]
        query: String,

        /// Registry URL to search
        #[arg(long)]
        registry: Option<String>,

        /// Maximum number of results
        #[arg(long, default_value = "10")]
        limit: usize,
    },

    /// Validate a register
    Validate {
        /// Path to the register directory
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,

        /// Show detailed validation results
        #[arg(long)]
        verbose: bool,
    },

    /// Discover packages in the registry
    Discover {
        /// Category to search in
        #[arg(value_name = "CATEGORY")]
        category: Option<String>,

        /// Maximum number of results
        #[arg(long, default_value = "20")]
        limit: usize,
    },

    /// Install dependencies for a project
    InstallDeps {
        /// Path to the register directory
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,
    },

    /// Clean the package cache
    CleanCache,

    /// Show package statistics
    Stats {
        /// Register name
        #[arg(value_name = "REGISTER")]
        register: String,
    },

    /// List available versions for a package
    Versions {
        /// Register name
        #[arg(value_name = "REGISTER")]
        register: String,
    },
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Init { name, directory } => init_register(name, directory).await,
        Commands::Build { path, output } => build_register(path, output).await,
        Commands::Install {
            register,
            version,
            global,
        } => install_register(register, version.as_deref(), *global).await,
        Commands::Publish { path, registry } => publish_register(path, registry.as_deref()).await,
        Commands::List { verbose, global } => list_registers(*verbose, *global).await,
        Commands::Remove { register, global } => remove_register(register, *global).await,
        Commands::Update {
            path,
            all,
            dependency,
        } => update_dependencies(path, *all, dependency.as_deref()).await,
        Commands::Info { register } => show_register_info(register).await,
        Commands::Search {
            query,
            registry,
            limit,
        } => search_registers(query, registry.as_deref(), *limit).await,
        Commands::Validate { path, verbose } => validate_register(path, *verbose).await,
        Commands::Discover { category, limit } => {
            discover_packages(category.as_deref(), *limit).await
        }
        Commands::InstallDeps { path } => install_dependencies_for_project(path).await,
        Commands::CleanCache => clean_cache().await,
        Commands::Stats { register } => show_package_stats(register).await,
        Commands::Versions { register } => list_available_versions(register).await,
    }
}
