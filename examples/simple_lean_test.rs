//! Very simple Lean test that bypasses specification requirements.
//!
//! This test focuses on basic process communication without requiring
//! a full specification setup.

#[cfg(feature = "lean-integration")]
use baton_client::{LeanClient, LeanClientConfig};
#[cfg(feature = "lean-integration")]
use baton_protocol::prelude::*;
#[cfg(feature = "lean-integration")]
use baton_verification::prelude::*;
use std::process::Command;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    println!("=== Simple Lean Communication Test ===");

    // First, check if Lean is installed
    println!("\n1. Checking if Lean is installed...");
    match Command::new("lean").arg("--version").output() {
        Ok(output) => {
            if output.status.success() {
                let version = String::from_utf8_lossy(&output.stdout);
                println!("✓ Lean is installed: {}", version.trim());
            } else {
                println!("✗ Lean command failed");
                return Ok(());
            }
        }
        Err(e) => {
            println!("✗ Lean not found: {}", e);
            return Ok(());
        }
    }

    // Test 2: Try to create a client with a dummy spec path
    println!("\n2. Testing client creation with dummy spec path...");
    let config = LeanClientConfig {
        lean_path: "lean".to_string(),
        spec_path: "/tmp".to_string(), // Use a directory that exists
        debug_logging: true,
        ..Default::default()
    };

    match LeanClient::with_config(config) {
        Ok(client) => {
            println!("✓ Client created with dummy config");

            // Test 3: Try to get version directly
            println!("\n3. Testing direct version check...");
            match client.get_version().await {
                Ok(version) => {
                    println!("✓ Direct version check: {}", version);
                }
                Err(e) => {
                    println!("✗ Direct version check failed: {:?}", e);
                }
            }

            // Test 4: Try ping
            println!("\n4. Testing ping...");
            match client.ping().await {
                Ok(is_available) => {
                    if is_available {
                        println!("✓ Ping successful");
                    } else {
                        println!("✗ Ping failed");
                    }
                }
                Err(e) => {
                    println!("✗ Ping error: {:?}", e);
                }
            }

            // Test 5: Try a simple verification request
            println!("\n5. Testing simple verification request...");
            let request = VerificationRequest::new(LeanRequest::Ping);
            match client.verify(request).await {
                Ok(response) => {
                    println!("✓ Verification request successful");
                    println!("  Execution time: {}ms", response.execution_time);
                    println!("  Response: {:?}", response.response);
                }
                Err(e) => {
                    println!("✗ Verification request failed: {:?}", e);
                }
            }
        }
        Err(e) => {
            println!("✗ Failed to create client with dummy config: {:?}", e);
        }
    }

    println!("\n=== Simple Test Complete ===");
    Ok(())
}
