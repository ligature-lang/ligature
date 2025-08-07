//! Simple test script to debug Lean process communication.
//!
//! This script tests basic communication with Lean to identify issues
//! in the process communication protocol.

#[cfg(feature = "lean-integration")]
use baton_client::LeanClient;
#[cfg(feature = "lean-integration")]
use baton_protocol::prelude::*;
#[cfg(feature = "lean-integration")]
use baton_verification::prelude::*;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    #[cfg(not(feature = "lean-integration"))]
    {
        println!("=== Lean Integration Not Enabled ===");
        println!("This example requires the 'lean-integration' feature to be enabled.");
        println!(
            "Run with: cargo run --example debug_lean_communication --features lean-integration"
        );
        return Ok(());
    }

    #[cfg(feature = "lean-integration")]
    {
        println!("=== Lean Process Communication Debug Test ===");

        // Test 1: Basic client creation
        println!("\n1. Testing client creation...");
        let client = match LeanClient::new() {
            Ok(client) => {
                println!("✓ Client created successfully");
                client
            }
            Err(e) => {
                println!("✗ Failed to create client: {:?}", e);
                return Ok(());
            }
        };

        // Test 2: Get Lean version
        println!("\n2. Testing Lean version...");
        match client.get_version().await {
            Ok(version) => {
                println!("✓ Lean version: {}", version);
            }
            Err(e) => {
                println!("✗ Failed to get Lean version: {:?}", e);
            }
        }

        // Test 3: Ping test
        println!("\n3. Testing ping...");
        match client.ping().await {
            Ok(is_available) => {
                if is_available {
                    println!("✓ Lean is available");
                } else {
                    println!("✗ Lean is not responding");
                }
            }
            Err(e) => {
                println!("✗ Ping failed: {:?}", e);
            }
        }

        // Test 4: Simple verification request
        println!("\n4. Testing simple verification request...");
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

        // Test 5: Evaluation verification request
        println!("\n5. Testing evaluation verification...");
        let request = VerificationRequest::new(LeanRequest::VerifyEvaluation {
            expression: "1 + 2".to_string(),
            expected_value: "3".to_string(),
            context: None,
        });
        match client.verify(request).await {
            Ok(response) => {
                println!("✓ Evaluation verification successful");
                println!("  Execution time: {}ms", response.execution_time);
                println!("  Response: {:?}", response.response);
            }
            Err(e) => {
                println!("✗ Evaluation verification failed: {:?}", e);
            }
        }

        // Test 6: Version request
        println!("\n6. Testing version request...");
        let request = VerificationRequest::new(LeanRequest::GetVersion);
        match client.verify(request).await {
            Ok(response) => {
                println!("✓ Version request successful");
                println!("  Execution time: {}ms", response.execution_time);
                println!("  Response: {:?}", response.response);
            }
            Err(e) => {
                println!("✗ Version request failed: {:?}", e);
            }
        }

        println!("\n=== Debug Test Complete ===");
        Ok(())
    }
}
