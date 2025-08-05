//! Main binary for the Ligature Language Server Protocol implementation.

use ligature_lsp::start_server;

#[tokio::main]
async fn main() {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    tracing::info!("Starting Ligature Language Server...");

    // Start the LSP server
    start_server().await;
}
