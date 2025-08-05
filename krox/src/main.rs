//! Main entry point for the Krox CLI.

use krox::cli::Cli;

#[tokio::main]
async fn main() {
    if let Err(e) = Cli::run().await {
        eprintln!("Error: {e}");
        std::process::exit(1);
    }
}
