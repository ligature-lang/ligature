//! Example demonstrating Lean process communication for Ligature verification.

#[cfg(feature = "lean-integration")]
use baton_protocol::DifferentialTestType;
#[cfg(feature = "lean-integration")]
use baton_verification::prelude::*;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Lean Integration Example ===\n");

    // Create verification engine
    println!("1. Creating verification engine...");
    let engine = match VerificationEngine::new() {
        Ok(engine) => {
            println!("   ✓ Verification engine created successfully");
            engine
        }
        Err(e) => {
            println!("   ✗ Failed to create verification engine: {}", e);
            return Err(e.into());
        }
    };

    // Check Lean availability
    println!("\n2. Checking Lean availability...");
    match engine.ping().await {
        Ok(is_available) => {
            if is_available {
                println!("   ✓ Lean is available and responding");
            } else {
                println!("   ✗ Lean is not responding");
                return Err("Lean is not available".into());
            }
        }
        Err(e) => {
            println!("   ✗ Failed to ping Lean: {}", e);
            return Err(e.into());
        }
    }

    // Get Lean version
    println!("\n3. Getting Lean version...");
    match engine.get_lean_version().await {
        Ok(version) => {
            println!("   ✓ Lean version: {}", version);
        }
        Err(e) => {
            println!("   ✗ Failed to get Lean version: {}", e);
        }
    }

    // Test expression evaluation verification
    println!("\n4. Testing expression evaluation verification...");
    let eval_result = engine.verify_evaluation("1 + 2", "3", None).await;

    match eval_result {
        Ok(response) => {
            println!("   ✓ Evaluation verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Evaluation verification failed: {}", e);
        }
    }

    // Test type checking verification
    println!("\n5. Testing type checking verification...");
    let type_result = engine.verify_type_check("1 + 2", "Int", None).await;

    match type_result {
        Ok(response) => {
            println!("   ✓ Type checking verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Type checking verification failed: {}", e);
        }
    }

    // Test type safety verification
    println!("\n6. Testing type safety verification...");
    let safety_result = engine.verify_type_safety("1 + 2", None).await;

    match safety_result {
        Ok(response) => {
            println!("   ✓ Type safety verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Type safety verification failed: {}", e);
        }
    }

    // Test termination verification
    println!("\n7. Testing termination verification...");
    let termination_result = engine.verify_termination("1 + 2", None).await;

    match termination_result {
        Ok(response) => {
            println!("   ✓ Termination verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Termination verification failed: {}", e);
        }
    }

    // Test determinism verification
    println!("\n8. Testing determinism verification...");
    let determinism_result = engine.verify_determinism("1 + 2", None).await;

    match determinism_result {
        Ok(response) => {
            println!("   ✓ Determinism verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Determinism verification failed: {}", e);
        }
    }

    // Test differential testing
    println!("\n9. Testing differential testing...");
    let diff_result = engine
        .run_differential_test("1 + 2", DifferentialTestType::Evaluation, None)
        .await;

    match diff_result {
        Ok(response) => {
            println!("   ✓ Differential test successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Differential test failed: {}", e);
        }
    }

    // Test theorem verification
    println!("\n10. Testing theorem verification...");
    let theorem_result = engine
        .verify_theorem("example_theorem", None, None, None)
        .await;

    match theorem_result {
        Ok(response) => {
            println!("   ✓ Theorem verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Theorem verification failed: {}", e);
        }
    }

    // Test invariant verification
    println!("\n11. Testing invariant verification...");
    let invariant_result = engine.verify_invariant("x > 0", "x + 1", None).await;

    match invariant_result {
        Ok(response) => {
            println!("   ✓ Invariant verification successful");
            println!("   Result: {:?}", response.response);
            println!("   Execution time: {}ms", response.execution_time);
        }
        Err(e) => {
            println!("   ✗ Invariant verification failed: {}", e);
        }
    }

    // Get verification metrics
    println!("\n12. Getting verification metrics...");
    let metrics = engine.get_metrics().await;
    println!("   Total verifications: {}", metrics.total_verifications);
    println!(
        "   Successful verifications: {}",
        metrics.successful_verifications
    );
    println!("   Failed verifications: {}", metrics.failed_verifications);
    println!(
        "   Average verification time: {:?}",
        metrics.average_verification_time
    );
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate * 100.0);

    // Get client statistics
    println!("\n13. Getting client statistics...");
    let stats = engine.get_client_stats();
    println!("   Total requests: {}", stats.total_requests);
    println!("   Successful requests: {}", stats.successful_requests);
    println!("   Failed requests: {}", stats.failed_requests);
    println!(
        "   Average response time: {:?}",
        stats.average_response_time
    );

    // Get engine health status
    println!("\n14. Getting engine health status...");
    let health = engine.get_health_status().await;
    println!("   Lean available: {}", health.lean_available);
    println!("   Active tasks: {}", health.active_task_count);
    println!("   Cache size: {}", health.cache_size);
    println!("   Uptime: {:?}", health.uptime);

    // Test specification validation
    println!("\n15. Testing specification validation...");
    let validation_result = engine.validate_specification().await;
    match validation_result {
        Ok(result) => {
            println!("   ✓ Specification validation successful");
            println!("   Files validated: {}", result.files_validated.len());
            println!("   Errors: {}", result.errors.len());
            println!("   Warnings: {}", result.warnings.len());
        }
        Err(e) => {
            println!("   ✗ Specification validation failed: {}", e);
        }
    }

    println!("\n=== Example completed successfully! ===");
    Ok(())
}
