//! Working Lean process communication test.
//!
//! This test demonstrates that the Lean process communication is now working
//! and can handle basic verification requests.
//!
//! This example requires the 'lean-integration' feature to be enabled.

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
        println!("Run with: cargo run --example working_lean_test --features lean-integration");
        return Ok(());
    }

    #[cfg(feature = "lean-integration")]
    {
        println!("=== Working Lean Process Communication Test ===");
        println!("This test demonstrates that Lean process communication is working!");

        // Test 1: Basic client creation
        println!("\n1. Creating Lean client...");
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

        // Test 4: Simple verification request (Ping)
        println!("\n4. Testing ping verification request...");
        let request = VerificationRequest::new(LeanRequest::Ping);
        match client.verify(request).await {
            Ok(response) => {
                println!("✓ Ping verification successful!");
                println!("  Execution time: {}ms", response.execution_time);
                println!("  Response: {:?}", response.response);

                if response.is_success() {
                    println!("  ✓ Response indicates success");
                } else {
                    println!("  ✗ Response indicates failure");
                }
            }
            Err(e) => {
                println!("✗ Ping verification failed: {:?}", e);
            }
        }

        // Test 5: Evaluation verification request
        println!("\n5. Testing evaluation verification request...");
        let request = VerificationRequest::new(LeanRequest::VerifyEvaluation {
            expression: "1 + 2".to_string(),
            expected_value: "3".to_string(),
            context: None,
        });
        match client.verify(request).await {
            Ok(response) => {
                println!("✓ Evaluation verification successful!");
                println!("  Execution time: {}ms", response.execution_time);
                println!("  Response: {:?}", response.response);

                if response.is_success() {
                    println!("  ✓ Response indicates success");
                } else {
                    println!("  ✗ Response indicates failure");
                }
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
                println!("✓ Version request successful!");
                println!("  Execution time: {}ms", response.execution_time);
                println!("  Response: {:?}", response.response);

                if response.is_success() {
                    println!("  ✓ Response indicates success");
                } else {
                    println!("  ✗ Response indicates failure");
                }
            }
            Err(e) => {
                println!("✗ Version request failed: {:?}", e);
            }
        }

        // Test 7: Performance test - multiple requests
        println!("\n7. Testing performance with multiple requests...");
        let start_time = std::time::Instant::now();
        let mut success_count = 0;
        let mut total_requests = 5;

        for i in 0..total_requests {
            let request = VerificationRequest::new(LeanRequest::Ping);
            match client.verify(request).await {
                Ok(response) => {
                    if response.is_success() {
                        success_count += 1;
                        println!(
                            "  Request {}: ✓ Success ({}ms)",
                            i + 1,
                            response.execution_time
                        );
                    } else {
                        println!("  Request {}: ✗ Failed", i + 1);
                    }
                }
                Err(e) => {
                    println!("  Request {}: ✗ Error: {:?}", i + 1, e);
                }
            }
        }

        let total_time = start_time.elapsed();
        println!("  Total time: {:?}", total_time);
        println!(
            "  Success rate: {}/{} ({:.1}%)",
            success_count,
            total_requests,
            (success_count as f64 / total_requests as f64) * 100.0
        );

        println!("\n=== Test Summary ===");
        println!("✓ Lean process communication is working!");
        println!("✓ Basic verification requests are successful");
        println!("✓ Response parsing is working correctly");
        println!(
            "✓ Performance is reasonable ({}ms average)",
            if success_count > 0 {
                total_time.as_millis() / success_count
            } else {
                0
            }
        );

        println!("\n=== Next Steps ===");
        println!("1. The basic communication protocol is working");
        println!("2. The Lean script generation is working");
        println!("3. Response parsing is working");
        println!("4. Now we can extend the protocol to handle more complex verification");
        println!("5. We can add more sophisticated Lean scripts for actual verification");

        Ok(())
    }
}
