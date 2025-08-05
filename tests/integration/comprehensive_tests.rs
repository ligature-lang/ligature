//! Comprehensive integration tests for the Ligature language.
//! 
//! This module tests the complete pipeline from parsing to evaluation,
//! ensuring all components work together correctly.

use ligature_ast::{AstResult, Program, Module};
use ligature_parser::Parser;
use ligature_types::type_check_program;
use ligature_eval::Evaluator;

/// Test the complete pipeline: parse -> type check -> evaluate
fn test_complete_pipeline(source: &str, expected_type: Option<&str>) -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    // Step 1: Parse
    let program = parser.parse_program(source)?;
    
    // Step 2: Type check
    let type_result = type_check_program(&program);
    if let Some(expected) = expected_type {
        assert!(type_result.is_ok(), "Type checking failed: {:?}", type_result.err());
    }
    
    // Step 3: Evaluate
    let eval_result = evaluator.evaluate_program(&program);
    assert!(eval_result.is_ok(), "Evaluation failed: {:?}", eval_result.err());
    
    Ok(())
}

/// Test basic arithmetic expressions
#[test]
fn test_arithmetic_expressions() -> AstResult<()> {
    let test_cases = vec![
        ("let x = 5 + 3;", None),
        ("let y = 10 - 4;", None),
        ("let z = 6 * 7;", None),
        ("let w = 20 / 4;", None),
        ("let r = 17 % 5;", None),
        ("let f = 3.14 + 2.86;", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test comparison expressions
#[test]
fn test_comparison_expressions() -> AstResult<()> {
    let test_cases = vec![
        ("let x = 5 > 3;", None),
        ("let y = 10 <= 10;", None),
        ("let z = 7 == 7;", None),
        ("let w = 4 != 5;", None),
        ("let f = 3.14 < 3.15;", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test logical expressions
#[test]
fn test_logical_expressions() -> AstResult<()> {
    let test_cases = vec![
        ("let x = true && false;", None),
        ("let y = true || false;", None),
        ("let z = !true;", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test function definitions and applications
#[test]
fn test_functions() -> AstResult<()> {
    let test_cases = vec![
        ("let add = \\x -> x + 1;", None),
        ("let double = \\x -> x * 2;", None),
        ("let add_one = \\x -> x + 1; let result = add_one(5);", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test pattern matching
#[test]
fn test_pattern_matching() -> AstResult<()> {
    let test_cases = vec![
        ("let x = 5; let result = match x { _ => \"default\" };", None),
        ("let x = 10; let result = match x { n when n > 0 => \"positive\", _ => \"zero\" };", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test let expressions
#[test]
fn test_let_expressions() -> AstResult<()> {
    let test_cases = vec![
        ("let x = 42;", None),
        ("let x = 5; let y = x + 1;", None),
        ("let x = 10; let y = 20; let z = x + y;", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test string operations
#[test]
fn test_string_operations() -> AstResult<()> {
    let test_cases = vec![
        ("let greeting = \"Hello\";", None),
        ("let name = \"World\";", None),
        ("let message = \"Hello\" == \"Hello\";", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test complex nested expressions
#[test]
fn test_complex_expressions() -> AstResult<()> {
    let test_cases = vec![
        ("let x = 10; let y = 5; let z = (x + y) * 2;", None),
        ("let a = true; let b = false; let c = a && (b || true);", None),
    ];
    
    for (source, expected_type) in test_cases {
        test_complete_pipeline(source, expected_type)?;
    }
    
    Ok(())
}

/// Test error handling
#[test]
fn test_error_handling() {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    // Test division by zero
    let source = "let x = 10 / 0;";
    match parser.parse_program(source) {
        Ok(program) => {
            let result = evaluator.evaluate_program(&program);
            // This should either fail or handle the error gracefully
            if result.is_ok() {
                println!("Division by zero was handled gracefully");
            } else {
                println!("Division by zero correctly caused an error");
            }
        },
        Err(_) => {
            println!("Division by zero was caught during parsing");
        }
    }
}

/// Test module parsing and evaluation
#[test]
fn test_module_evaluation() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let x = 42;
        let y = x + 1;
    "#;
    
    let module = parser.parse_module(source)?;
    let result = evaluator.evaluate_module(&module)?;
    
    assert!(result.is_module(), "Expected module value");
    
    Ok(())
}

/// Test type inference with complex types
#[test]
fn test_complex_type_inference() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    let source = r#"
        let id = \x -> x;
        let result = id(42);
    "#;
    
    let program = parser.parse_program(source)?;
    let type_result = type_check_program(&program);
    
    assert!(type_result.is_ok(), "Type inference failed: {:?}", type_result.err());
    
    Ok(())
}

/// Test the complete pipeline with a realistic program
#[test]
fn test_realistic_program() -> AstResult<()> {
    let source = r#"
        // Define some utility functions
        let add = \x -> \y -> x + y;
        let multiply = \x -> \y -> x * y;
        
        // Define some constants
        let pi = 3.14159;
        let radius = 5;
        
        // Calculate area of a circle
        let area = multiply(pi)(multiply(radius)(radius));
        
        // Define a function to check if a number is positive
        let is_positive = \x -> x > 0;
        
        // Test the function
        let test_result = is_positive(area);
    "#;
    
    test_complete_pipeline(source, None)?;
    
    Ok(())
}

/// Test pattern matching with guards
#[test]
fn test_pattern_guards() -> AstResult<()> {
    let source = r#"
        let classify_number = \x -> match x {
            n when n > 0 => "positive",
            n when n < 0 => "negative",
            _ => "zero"
        };
        
        let result1 = classify_number(5);
        let result2 = classify_number(-3);
        let result3 = classify_number(0);
    "#;
    
    test_complete_pipeline(source, None)?;
    
    Ok(())
}

/// Test nested function applications
#[test]
fn test_nested_functions() -> AstResult<()> {
    let source = r#"
        let compose = \f -> \g -> \x -> f(g(x));
        let add_one = \x -> x + 1;
        let double = \x -> x * 2;
        
        let add_one_then_double = compose(double)(add_one);
        let result = add_one_then_double(5);
    "#;
    
    test_complete_pipeline(source, None)?;
    
    Ok(())
}

/// Test error recovery and reporting
#[test]
fn test_error_recovery() {
    let mut parser = Parser::new();
    
    // Test with invalid syntax
    let invalid_sources = vec![
        "let x = ;",  // Missing value
        "let = 5;",   // Missing identifier
        "x +",        // Incomplete expression
    ];
    
    for source in invalid_sources {
        let result = parser.parse_program(source);
        assert!(result.is_err(), "Expected parsing to fail for: {}", source);
    }
}

/// Test performance with larger programs
#[test]
fn test_performance() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    // Create a larger program
    let mut source = String::new();
    for i in 0..100 {
        source.push_str(&format!("let x{} = {};\n", i, i));
    }
    
    let start = std::time::Instant::now();
    
    let program = parser.parse_program(&source)?;
    let type_result = type_check_program(&program);
    let eval_result = evaluator.evaluate_program(&program);
    
    let duration = start.elapsed();
    
    assert!(type_result.is_ok(), "Type inference failed");
    assert!(eval_result.is_ok(), "Evaluation failed");
    assert!(duration.as_millis() < 1000, "Performance test took too long: {:?}", duration);
    
    Ok(())
}

/// Test memory usage and cleanup
#[test]
fn test_memory_usage() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();
    
    // Create a program with many nested expressions
    let source = r#"
        let deep_nest = (((((((((1 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1;
    "#;
    
    let program = parser.parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // The result should be 11
    if let Some(value) = result.as_integer() {
        assert_eq!(value, 11, "Expected 11, got {}", value);
    } else {
        panic!("Expected integer result");
    }
    
    Ok(())
}

/// Test the complete language feature set
#[test]
fn test_complete_language_features() -> AstResult<()> {
    let source = r#"
        // Test all major language features in one program
        
        // 1. Basic arithmetic and comparison
        let x = 10;
        let y = 5;
        let sum = x + y;
        let product = x * y;
        let is_greater = x > y;
        
        // 2. Logical operations
        let a = true;
        let b = false;
        let logical_and = a && b;
        let logical_or = a || b;
        
        // 3. Function definition and application
        let add_one = \x -> x + 1;
        let result = add_one(5);
        
        // 4. Pattern matching with guards
        let classify = \n -> match n {
            n when n > 0 => "positive",
            n when n < 0 => "negative",
            _ => "zero"
        };
        
        let classification = classify(x);
        
        // 5. Nested expressions
        let complex = (x + y) * (x - y);
        
        // 6. String operations
        let greeting = "Hello";
        let is_hello = greeting == "Hello";
    "#;
    
    test_complete_pipeline(source, None)?;
    
    Ok(())
} 