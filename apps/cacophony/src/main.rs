use clap::Parser;
use tracing::{error, info, Level};
use tracing_subscriber::FmtSubscriber;

mod cli;
mod collection;
mod config;
mod environment;
mod error;
mod ligature_loader;
mod operation;
mod plugin;
mod xdg_config;

use cli::Commands;
use error::CacophonyError;

#[derive(Parser)]
#[command(name = "cacophony")]
#[command(about = "A CLI tool for orchestrating collections of Ligature programs")]
#[command(version = env!("CARGO_PKG_VERSION"))]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Enable verbose logging
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Log level (trace, debug, info, warn, error)
    #[arg(long, global = true, default_value = "info")]
    log_level: Option<Level>,
}

#[tokio::main]
async fn main() -> Result<(), CacophonyError> {
    println!("DEBUG: main.rs started");
    let cli = Cli::parse();

    // Initialize logging
    let log_level = cli.log_level.unwrap_or(if cli.verbose {
        Level::DEBUG
    } else {
        Level::INFO
    });

    tracing::info!("Setting log level to: {:?}", log_level);

    let _subscriber = FmtSubscriber::builder()
        .with_max_level(log_level)
        .with_target(false)
        .with_thread_ids(true)
        .with_thread_names(true)
        .init();

    info!("Starting cacophony CLI v{}", env!("CARGO_PKG_VERSION"));
    println!("DEBUG: About to execute command: {:?}", cli.command);

    // Execute the command
    match cli.command.execute().await {
        Ok(_) => {
            println!("DEBUG: Command executed successfully");
            info!("Command completed successfully");
            Ok(())
        }
        Err(e) => {
            println!("DEBUG: Command failed: {}", e);
            error!("Command failed: {}", e);
            Err(e)
        }
    }
}
