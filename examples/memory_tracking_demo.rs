//! Memory tracking demo for Ligature evaluation engine.
//!
//! This example demonstrates how to use the memory tracking functionality
//! to monitor memory usage during program evaluation.

use ligature_eval::{Evaluator, MemoryTracker, get_current_memory_stats};
use ligature_parser::parse_program;

#[allow(clippy::type_complexity)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Ligature Memory Tracking Demo ===\n");

    // Create a memory tracker
    let mut memory_tracker = MemoryTracker::new();

    // Set baseline memory usage
    memory_tracker.set_baseline()?;
    println!("Baseline memory usage set");

    // Get initial memory stats
    let initial_stats = get_current_memory_stats()?;
    println!(
        "Initial memory usage: {} bytes (RSS), {} bytes (VMS)",
        initial_stats.rss, initial_stats.vms
    );

    // Create an evaluator
    let mut evaluator = Evaluator::new();

    // Define a simple program
    let program_source = r#"
        let x = 42;
        let y = 17;
        let z = x + y * 3 - 10;
        let result = z / 2 + 5;
    "#;

    println!("\nParsing and evaluating program...");

    // Parse the program
    let program = parse_program(program_source)?;

    // Get memory usage after parsing
    let after_parse_stats = memory_tracker.get_current_usage()?;
    println!(
        "Memory after parsing: {} bytes (RSS), delta: {} bytes",
        after_parse_stats.rss,
        after_parse_stats.delta.unwrap_or(0)
    );

    // Evaluate the program
    let result = evaluator.evaluate_program(&program)?;
    println!("Evaluation result: {result:?}");

    // Get final memory usage
    let final_stats = memory_tracker.get_current_usage()?;
    println!(
        "Final memory usage: {} bytes (RSS), delta: {} bytes",
        final_stats.rss,
        final_stats.delta.unwrap_or(0)
    );

    // Get peak memory usage
    let peak_stats = memory_tracker.get_peak_usage()?;
    println!("Peak memory usage: {} bytes (RSS)", peak_stats.peak);

    println!("\n=== Memory Tracking Summary ===");
    println!("Initial RSS: {} bytes", initial_stats.rss);
    println!("Final RSS: {} bytes", final_stats.rss);
    println!("Peak RSS: {} bytes", peak_stats.peak);
    println!("Memory delta: {} bytes", final_stats.delta.unwrap_or(0));

    Ok(())
}
