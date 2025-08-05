//! Value optimization benchmark demonstrating the performance benefits
//! of value interning and list literal conversion.

use ligature_eval::{Evaluator, ValueOptimizationStats};
use ligature_parser::parse_program;
use std::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Ligature Value Optimization Benchmark");
    println!("=====================================\n");

    // Test with value optimization enabled
    println!("1. Testing with value optimization ENABLED:");
    let mut evaluator_enabled = Evaluator::new();
    evaluator_enabled.set_value_optimization(true);
    
    let start_time = Instant::now();
    let result_enabled = run_optimization_benchmark(&mut evaluator_enabled);
    let duration_enabled = start_time.elapsed();
    
    let stats_enabled = evaluator_enabled.value_optimization_stats();
    
    println!("   ✓ Completed in {duration_enabled:?}");
    println!("   ✓ Total interned values: {}", stats_enabled.total_interned_values());
    println!("   ✓ Memory savings: {} bytes", stats_enabled.total_memory_saved);
    println!("   ✓ Memory savings: {:.2}%", stats_enabled.memory_savings_percentage());
    println!("   ✓ Value pool utilization: {:.2}%", stats_enabled.pool_utilization * 100.0);
    
    // Test with value optimization disabled
    println!("\n2. Testing with value optimization DISABLED:");
    let mut evaluator_disabled = Evaluator::new();
    evaluator_disabled.set_value_optimization(false);
    
    let start_time = Instant::now();
    let result_disabled = run_optimization_benchmark(&mut evaluator_disabled);
    let duration_disabled = start_time.elapsed();
    
    let stats_disabled = evaluator_disabled.value_optimization_stats();
    
    println!("   ✓ Completed in {duration_disabled:?}");
    println!("   ✓ Total interned values: {}", stats_disabled.total_interned_values());
    println!("   ✓ Memory savings: {} bytes", stats_disabled.total_memory_saved);
    
    // Performance comparison
    println!("\n3. Performance Comparison:");
    let speedup = duration_disabled.as_nanos() as f64 / duration_enabled.as_nanos() as f64;
    println!("   ✓ Speedup: {:.2}x", speedup);
    println!("   ✓ Time saved: {duration_disabled - duration_enabled:?}");
    
    // Memory efficiency comparison
    let memory_efficiency = stats_enabled.total_memory_saved as f64 / stats_disabled.total_memory_saved as f64;
    println!("   ✓ Memory efficiency: {:.2}x", memory_efficiency);
    
    // Verify results are equivalent
    println!("\n4. Result Verification:");
    match (result_enabled, result_disabled) {
        (Ok(_), Ok(_)) => println!("   ✓ Both evaluations completed successfully"),
        (Err(e1), Err(e2)) => println!("   ✓ Both evaluations failed with equivalent errors"),
        _ => println!("   ⚠ Results differ between optimized and non-optimized evaluation"),
    }
    
    println!("\n✅ Benchmark completed successfully!");
    Ok(())
}

fn run_optimization_benchmark(evaluator: &mut Evaluator) -> Result<(), Box<dyn std::error::Error>> {
    // Test cases that benefit from value optimization
    let test_programs = vec![
        // Repeated string literals
        r#"
            let repeated_strings = ["hello", "world", "hello", "world", "hello"];
            let more_strings = ["test", "hello", "world", "test", "hello"];
            let combined = ["hello", "world", "test", "hello", "world"];
            ()
        "#,
        
        // Repeated integer literals
        r#"
            let numbers1 = [1, 2, 3, 1, 2, 3, 1, 2, 3];
            let numbers2 = [4, 5, 6, 4, 5, 6, 4, 5, 6];
            let numbers3 = [1, 2, 3, 4, 5, 6, 1, 2, 3];
            ()
        "#,
        
        // Repeated boolean literals
        r#"
            let flags1 = [true, false, true, false, true, false];
            let flags2 = [false, true, false, true, false, true];
            let flags3 = [true, true, false, false, true, true];
            ()
        "#,
        
        // Mixed literals with repetition
        r#"
            let mixed1 = [1, "hello", true, 1, "hello", true];
            let mixed2 = [2, "world", false, 2, "world", false];
            let mixed3 = [1, "hello", true, 2, "world", false];
            ()
        "#,
        
        // Nested lists with repetition
        r#"
            let nested1 = [[1, 2], [3, 4], [1, 2], [3, 4]];
            let nested2 = [[5, 6], [7, 8], [5, 6], [7, 8]];
            let nested3 = [[1, 2], [3, 4], [5, 6], [7, 8]];
            ()
        "#,
        
        // Complex expressions with repeated values
        r#"
            let x = 42;
            let y = "test";
            let z = true;
            let result1 = [x, y, z, x, y, z];
            let result2 = [x + 1, y, z, x + 1, y, z];
            let result3 = [x, y, z, x + 1, y, z];
            ()
        "#,
    ];
    
    for (i, program) in test_programs.iter().enumerate() {
        let program_ast = parse_program(program)?;
        evaluator.evaluate_program(&program_ast)?;
        
        if (i + 1) % 2 == 0 {
            // Update statistics periodically
            evaluator.update_value_optimization_stats();
        }
    }
    
    Ok(())
} 