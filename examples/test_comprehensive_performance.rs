use ligature_eval::benchmarks::comprehensive_performance_analysis;

fn main() {
    println!("Running Comprehensive Performance Analysis with Cache Statistics\n");

    match comprehensive_performance_analysis() {
        Ok(()) => println!("✅ Comprehensive performance analysis completed successfully!"),
        Err(e) => println!("❌ Error running performance analysis: {e:?}"),
    }
}
