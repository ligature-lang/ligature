//! Example demonstrating how to use the Krox library to execute Ligature programs.

use krox::{Client, ClientBuilder, ExecutionMode};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[tokio::main]
async fn main() -> Result<()> {
    println!("Krox Example - Ligature Program Execution");
    println!("==========================================");

    // Example 1: Create a client with native execution
    println!("\n1. Creating client with native execution...");
    match Client::new(ExecutionMode::Native).await {
        Ok(mut client) => {
            println!("   ✓ Native client created successfully");

            // Try to execute a simple Ligature program
            let source = "let x = 42";
            match client.execute_source(source).await {
                Ok(result) => {
                    println!("   ✓ Executed program: {source}");
                    println!("   ✓ Result: {:?}", result.value);
                    println!("   ✓ Duration: {:?}", result.metadata.duration);
                    println!("   ✓ Cached: {}", result.metadata.cached);
                }
                Err(e) => {
                    println!("   ✗ Failed to execute program: {e}");
                }
            }
        }
        Err(e) => {
            println!("   ✗ Failed to create native client: {e}");
            println!("   Note: This is expected if ligature-cli is not installed");
        }
    }

    // Example 2: Create a client with builder pattern
    println!("\n2. Creating client with builder pattern...");
    match ClientBuilder::new()
        .execution_mode(ExecutionMode::Native)
        .enable_cache(true)
        .verbose(false)
        .build()
        .await
    {
        Ok(mut client) => {
            println!("   ✓ Client created with builder successfully");

            // Check cache statistics
            if let Ok(Some(stats)) = client.cache_stats().await {
                println!("   ✓ Cache stats:");
                println!("     - Total entries: {}", stats.total_entries);
                println!("     - Hits: {}", stats.hits);
                println!("     - Misses: {}", stats.misses);
                println!("     - Hit rate: {:.2}%", stats.hit_rate * 100.0);
            }
        }
        Err(e) => {
            println!("   ✗ Failed to create client with builder: {e}");
        }
    }

    // Example 3: Try in-process execution (if available)
    println!("\n3. Trying in-process execution...");
    match Client::new(ExecutionMode::InProcess).await {
        Ok(mut client) => {
            println!("   ✓ In-process client created successfully");

            let source = "let y = 100";
            match client.execute_source(source).await {
                Ok(result) => {
                    println!("   ✓ Executed program: {source}");
                    println!("   ✓ Result: {:?}", result.value);
                }
                Err(e) => {
                    println!("   ✗ Failed to execute program: {e}");
                }
            }
        }
        Err(e) => {
            println!("   ✗ In-process execution not available: {e}");
            println!("   Note: This is expected as in-process execution is not yet implemented");
        }
    }

    println!("\nExample completed!");
    Ok(())
}
