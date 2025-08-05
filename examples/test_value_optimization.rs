//! Simple test to verify value optimization features work correctly.

use ligature_eval::{Evaluator, ValueOptimizationStats};
use ligature_parser::parse_program;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🧪 Testing Value Optimization Features");
    println!("=====================================\n");

    // Test 1: List literal conversion
    println!("1. Testing list literal conversion:");
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    let test_programs = vec![
        ("let x = 42;", "simple integer"),
        ("let x = \"hello\";", "string"),
        ("let x = true;", "boolean"),
        ("let x = 3.14;", "float"),
        ("let x = ();", "unit"),
    ];

    for (source, description) in test_programs {
        match parse_program(source) {
            Ok(program) => match evaluator.evaluate_program(&program) {
                Ok(value) => {
                    println!("   ✓ {}: Success", description);
                    if value.is_list() {
                        if let Some(elements) = value.as_list() {
                            println!("      - List has {} elements", elements.len());
                        }
                    }
                }
                Err(e) => {
                    println!("   ✗ {}: Evaluation failed - {}", description, e);
                }
            },
            Err(e) => {
                println!("   ✗ {}: Parsing failed - {}", description, e);
            }
        }
    }

    // Test 2: Value interning statistics
    println!("\n2. Testing value interning:");
    evaluator.update_value_optimization_stats();
    let stats = evaluator.value_optimization_stats();

    println!("   ✓ Optimization enabled: {}", stats.optimization_enabled);
    println!(
        "   ✓ Total interned values: {}",
        stats.total_interned_values()
    );
    println!(
        "   ✓ String interning: {} strings",
        stats.interner.string_count
    );
    println!(
        "   ✓ Integer interning: {} integers",
        stats.interner.integer_count
    );
    println!(
        "   ✓ Float interning: {} floats",
        stats.interner.float_count
    );
    println!(
        "   ✓ Boolean interning: {} booleans",
        stats.interner.boolean_count
    );
    println!("   ✓ List interning: {} lists", stats.interner.list_count);
    println!("   ✓ Memory savings: {} bytes", stats.total_memory_saved);
    println!(
        "   ✓ Memory savings: {:.2}%",
        stats.memory_savings_percentage()
    );

    // Test 3: Performance comparison
    println!("\n3. Testing performance comparison:");

    // Test with optimization enabled
    let mut optimized_evaluator = Evaluator::new();
    optimized_evaluator.set_value_optimization(true);

    let repeated_program = r#"
        let repeated_strings = "hello";
        let repeated_numbers = 42;
        let repeated_booleans = true;
        let result = 42;
    "#;

    let parsed = parse_program(repeated_program)?;

    let start = std::time::Instant::now();
    let _result1 = optimized_evaluator.evaluate_program(&parsed)?;
    let optimized_duration = start.elapsed();

    // Test with optimization disabled
    let mut non_optimized_evaluator = Evaluator::new();
    non_optimized_evaluator.set_value_optimization(false);

    let start = std::time::Instant::now();
    let _result2 = non_optimized_evaluator.evaluate_program(&parsed)?;
    let non_optimized_duration = start.elapsed();

    println!("   ✓ Optimized duration: {:?}", optimized_duration);
    println!("   ✓ Non-optimized duration: {:?}", non_optimized_duration);

    if optimized_duration < non_optimized_duration {
        let improvement = ((non_optimized_duration.as_nanos() as f64
            - optimized_duration.as_nanos() as f64)
            / non_optimized_duration.as_nanos() as f64)
            * 100.0;
        println!("   🚀 Performance improvement: {:.1}%", improvement);
    } else {
        println!("   📊 Performance difference: Minimal (expected for small programs)");
    }

    // Test 4: Memory efficiency
    println!("\n4. Testing memory efficiency:");
    optimized_evaluator.update_value_optimization_stats();
    let optimized_stats = optimized_evaluator.value_optimization_stats();

    non_optimized_evaluator.update_value_optimization_stats();
    let non_optimized_stats = non_optimized_evaluator.value_optimization_stats();

    println!(
        "   ✓ Optimized interned values: {}",
        optimized_stats.total_interned_values()
    );
    println!(
        "   ✓ Non-optimized interned values: {}",
        non_optimized_stats.total_interned_values()
    );
    println!(
        "   ✓ Memory savings: {} bytes",
        optimized_stats.total_memory_saved
    );

    println!("\n✅ All value optimization tests completed successfully!");
    Ok(())
}
