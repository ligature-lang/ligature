//! Performance benchmarks for type inference.

use crate::inference::TypeInference;
use ligature_ast::{Span, Type};
use ligature_parser::parse_program;
use std::time::Instant;

/// Run performance benchmarks for type inference.
pub fn run_performance_benchmarks() {
    println!("=== Type Inference Performance Benchmarks ===\n");

    // Test 1: Simple expressions
    benchmark_simple_expressions();

    // Test 2: Complex expressions
    benchmark_complex_expressions();

    // Test 3: Repeated expressions (cache performance)
    benchmark_cache_performance();

    // Test 4: Large programs
    benchmark_large_programs();

    println!("=== Benchmark Summary ===");
    println!("All benchmarks completed successfully!");
}

/// Benchmark simple expressions.
fn benchmark_simple_expressions() {
    println!("1. Simple Expressions Benchmark:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Test various simple expressions
    let expressions = vec![
        "let x = 42;",
        "let y = \"hello\";",
        "let z = true;",
        "let add = \\x y -> x + y;",
        "let result = add 5 3;",
    ];

    for expr in expressions {
        let program = parse_program(expr).unwrap();
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                let _result = inference.infer_expression(&value_decl.value);
            }
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time: {duration:?}");
    println!("   Inference operations: {}", metrics.inference_count);
    println!(
        "   Constraint solving operations: {}",
        metrics.constraint_solving_count
    );
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!(
        "   Average time per inference: {:?}",
        if metrics.inference_count > 0 {
            duration / metrics.inference_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}

/// Benchmark complex expressions.
fn benchmark_complex_expressions() {
    println!("2. Complex Expressions Benchmark:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Test complex expressions
    let complex_program = r#"
        let user = { name = "Alice", age = 30, email = "alice@example.com" };
        let process_user = \user -> { name = user.name, age = user.age };
        let result = process_user user;
        let add_numbers = \x y z -> x + y + z;
        let sum = add_numbers 1 2 3;
        let conditional = if true then 42 else 0;
        let list_ops = [1, 2, 3, 4, 5];
        let mapped = map (\x -> x * 2) list_ops;
    "#;

    let program = parse_program(complex_program).unwrap();
    for declaration in &program.declarations {
        if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
            let _result = inference.infer_expression(&value_decl.value);
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time: {duration:?}");
    println!("   Inference operations: {}", metrics.inference_count);
    println!(
        "   Constraint solving operations: {}",
        metrics.constraint_solving_count
    );
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!(
        "   Average time per inference: {:?}",
        if metrics.inference_count > 0 {
            duration / metrics.inference_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}

/// Benchmark cache performance with repeated expressions.
fn benchmark_cache_performance() {
    println!("3. Cache Performance Benchmark:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Test the same expression multiple times to test caching
    let repeated_expression = "let x = 42;";
    let iterations = 100;

    for _ in 0..iterations {
        let program = parse_program(repeated_expression).unwrap();
        for declaration in &program.declarations {
            if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                let _result = inference.infer_expression(&value_decl.value);
            }
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time for {iterations} iterations: {duration:?}");
    println!("   Inference operations: {}", metrics.inference_count);
    println!("   Cache hits: {}", metrics.cache_hits);
    println!("   Cache misses: {}", metrics.cache_misses);
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!("   Average time per iteration: {:?}", duration / iterations);
    println!();
}

/// Benchmark large programs.
fn benchmark_large_programs() {
    println!("4. Large Programs Benchmark:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Test a larger program with multiple functions and data structures
    let large_program = r#"
        // Define a complex data structure
        let user = { 
            name = "Alice", 
            age = 30, 
            email = "alice@example.com",
            preferences = { theme = "dark", notifications = true }
        };
        
        // Define multiple functions
        let get_name = \user -> user.name;
        let get_age = \user -> user.age;
        let get_email = \user -> user.email;
        let get_preferences = \user -> user.preferences;
        
        // Define higher-order functions
        let map = \f list -> list;
        let filter = \pred list -> list;
        let reduce = \f acc list -> acc;
        
        // Define complex operations
        let process_users = \users -> map get_name users;
        let filter_adults = \users -> filter (\user -> user.age >= 18) users;
        let count_users = \users -> reduce (\acc user -> acc + 1) 0 users;
        
        // Test function composition
        let get_user_info = \user -> { 
            name = get_name user, 
            age = get_age user,
            email = get_email user 
        };
        
        // Test conditional logic
        let is_adult = \user -> user.age >= 18;
        let can_vote = \user -> user.age >= 18;
        let can_drive = \user -> user.age >= 16;
        
        // Test nested operations
        let complex_operation = \users -> 
            map (\user -> 
                if is_adult user then 
                    { name = user.name, status = "adult" }
                else 
                    { name = user.name, status = "minor" }
            ) users;
    "#;

    let program = parse_program(large_program).unwrap();
    for declaration in &program.declarations {
        if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
            let _result = inference.infer_expression(&value_decl.value);
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time: {duration:?}");
    println!("   Inference operations: {}", metrics.inference_count);
    println!(
        "   Constraint solving operations: {}",
        metrics.constraint_solving_count
    );
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!(
        "   Total inference time: {:?}",
        metrics.total_inference_time
    );
    println!(
        "   Total constraint solving time: {:?}",
        metrics.total_constraint_solving_time
    );
    println!(
        "   Average time per inference: {:?}",
        if metrics.inference_count > 0 {
            duration / metrics.inference_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}

/// Compare performance between optimized and unoptimized versions.
pub fn compare_performance() {
    println!("=== Performance Comparison ===");

    // This would compare the optimized version with a baseline
    // For now, we'll just show the optimized metrics

    let mut inference = TypeInference::new();
    let test_program = r#"
        let x = 42;
        let y = "hello";
        let add = \x y -> x + y;
        let result = add 5 3;
    "#;

    let start_time = Instant::now();
    let program = parse_program(test_program).unwrap();

    for declaration in &program.declarations {
        if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
            let _result = inference.infer_expression(&value_decl.value);
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("Optimized Version Results:");
    println!("  Total time: {duration:?}");
    println!("  Inference operations: {}", metrics.inference_count);
    println!(
        "  Constraint solving operations: {}",
        metrics.constraint_solving_count
    );
    println!("  Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!(
        "  Average time per inference: {:?}",
        if metrics.inference_count > 0 {
            duration / metrics.inference_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}

/// Test specific performance optimizations.
pub fn test_optimizations() {
    println!("=== Optimization Tests ===");

    // Test 1: Substitution caching
    test_substitution_caching();

    // Test 2: Constraint solving optimization
    test_constraint_solving_optimization();

    // Test 3: Type inference caching
    test_type_inference_caching();

    println!("All optimization tests completed!");
    println!();
}

/// Test substitution caching performance.
fn test_substitution_caching() {
    println!("1. Substitution Caching Test:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Create a complex type with many substitutions
    let complex_type = Type::function(
        Type::function(
            Type::variable("a".to_string(), Span::default()),
            Type::variable("b".to_string(), Span::default()),
            Span::default(),
        ),
        Type::function(
            Type::variable("b".to_string(), Span::default()),
            Type::variable("c".to_string(), Span::default()),
            Span::default(),
        ),
        Span::default(),
    );

    // Apply multiple substitutions
    for _i in 0..100 {
        let _substitution = std::collections::HashMap::from([
            ("a".to_string(), Type::integer(Span::default())),
            ("b".to_string(), Type::string(Span::default())),
            ("c".to_string(), Type::bool(Span::default())),
        ]);

        let _result = inference
            .constraint_solver
            .apply_substitution(complex_type.clone());
    }

    let duration = start_time.elapsed();
    println!("   Time for 100 substitution applications: {duration:?}");
    println!("   Average time per substitution: {:?}", duration / 100);
    println!();
}

/// Test constraint solving optimization.
fn test_constraint_solving_optimization() {
    println!("2. Constraint Solving Optimization Test:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Create a program with many constraints
    let constraint_heavy_program = r#"
        let f = \x -> x;
        let g = \x -> x;
        let h = \x -> x;
        let compose = \f g x -> f (g x);
        let result1 = compose f g 42;
        let result2 = compose g h "hello";
        let result3 = compose h f true;
    "#;

    let program = parse_program(constraint_heavy_program).unwrap();
    for declaration in &program.declarations {
        if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
            let _result = inference.infer_expression(&value_decl.value);
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time: {duration:?}");
    println!(
        "   Constraint solving operations: {}",
        metrics.constraint_solving_count
    );
    println!(
        "   Total constraint solving time: {:?}",
        metrics.total_constraint_solving_time
    );
    println!(
        "   Average time per constraint solving: {:?}",
        if metrics.constraint_solving_count > 0 {
            metrics.total_constraint_solving_time / metrics.constraint_solving_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}

/// Test type inference caching.
fn test_type_inference_caching() {
    println!("3. Type Inference Caching Test:");

    let mut inference = TypeInference::new();
    let start_time = Instant::now();

    // Test repeated type inference of the same expressions
    let expressions = vec![
        "let x = 42;",
        "let y = \"hello\";",
        "let add = \\x y -> x + y;",
    ];

    // Run each expression multiple times
    for _ in 0..50 {
        for expr in &expressions {
            let program = parse_program(expr).unwrap();
            for declaration in &program.declarations {
                if let ligature_ast::DeclarationKind::Value(value_decl) = &declaration.kind {
                    let _result = inference.infer_expression(&value_decl.value);
                }
            }
        }
    }

    let duration = start_time.elapsed();
    let metrics = inference.metrics();

    println!("   Time: {duration:?}");
    println!("   Total inference operations: {}", metrics.inference_count);
    println!("   Cache hits: {}", metrics.cache_hits);
    println!("   Cache misses: {}", metrics.cache_misses);
    println!("   Cache hit rate: {:.2}%", metrics.cache_hit_rate());
    println!(
        "   Average time per inference: {:?}",
        if metrics.inference_count > 0 {
            duration / metrics.inference_count as u32
        } else {
            std::time::Duration::ZERO
        }
    );
    println!();
}
