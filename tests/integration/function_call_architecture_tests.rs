//! Tests for the new function call architecture with optimizations.
//! 
//! These tests verify that the environment pooling, stack-based evaluation,
//! and tail call optimization work correctly.

use ligature_eval::{Evaluator, CacheStats};
use ligature_parser::parse_program;
use ligature_ast::AstResult;

#[test]
fn test_environment_pooling() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test that environment pooling reduces memory allocation
    let source = "
        let add = \\x y -> x + y;
        let result1 = add 5 3;
        let result2 = add 10 20;
        let result3 = add 100 200;
        result3
    ";
    
    let program = parse_program(source)?;
    let _result = evaluator.evaluate_program(&program)?;
    
    // Check environment pool statistics
    let (available, total) = evaluator.env_pool_stats();
    assert!(available > 0, "Environment pool should have available environments");
    assert!(total > 0, "Environment pool should have been used");
    
    Ok(())
}

#[test]
fn test_stack_based_evaluation() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    evaluator.set_stack_based_evaluation(true);
    
    // Test simple function that should use stack-based evaluation
    let source = "
        let double = \\x -> x + x;
        let result = double 5;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Check that stack-based evaluation was used
    let stats = evaluator.cache_stats();
    assert!(stats.stack_evals > 0, "Stack-based evaluation should have been used");
    
    // Verify the result is correct
    assert!(matches!(result, ligature_ast::Value::Integer(10)));
    
    Ok(())
}

#[test]
fn test_tail_call_optimization() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    evaluator.set_tail_call_optimization(true);
    
    // Test tail-recursive function
    let source = "
        let factorial = \\n -> 
            if n <= 1 then 1 else n * factorial (n - 1);
        let result = factorial 5;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Check that tail call optimization was used
    let stats = evaluator.cache_stats();
    assert!(stats.tail_calls > 0, "Tail call optimization should have been used");
    
    // Verify the result is correct
    assert!(matches!(result, ligature_ast::Value::Integer(120)));
    
    Ok(())
}

#[test]
fn test_complex_function_application() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test complex nested function applications
    let source = "
        let compose = \\f g x -> f (g x);
        let add_one = \\x -> x + 1;
        let double = \\x -> x * 2;
        let add_one_then_double = compose double add_one;
        let result = add_one_then_double 5;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct: (5 + 1) * 2 = 12
    assert!(matches!(result, ligature_ast::Value::Integer(12)));
    
    Ok(())
}

#[test]
fn test_closure_capturing() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test closure with captured environment
    let source = "
        let make_adder = \\x -> \\y -> x + y;
        let add_five = make_adder 5;
        let result = add_five 3;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct: 5 + 3 = 8
    assert!(matches!(result, ligature_ast::Value::Integer(8)));
    
    Ok(())
}

#[test]
fn test_recursive_functions() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test recursive function with multiple calls
    let source = "
        let fibonacci = \\n ->
            if n <= 1 then n
            else fibonacci (n - 1) + fibonacci (n - 2);
        let result = fibonacci 10;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct (fibonacci(10) = 55)
    assert!(matches!(result, ligature_ast::Value::Integer(55)));
    
    Ok(())
}

#[test]
fn test_optimization_statistics() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    evaluator.set_tail_call_optimization(true);
    evaluator.set_stack_based_evaluation(true);
    
    // Run a program that should trigger multiple optimizations
    let source = "
        let simple_add = \\x y -> x + y;
        let tail_factorial = \\n acc ->
            if n <= 1 then acc
            else tail_factorial (n - 1) (n * acc);
        
        let result1 = simple_add 5 3;
        let result2 = tail_factorial 5 1;
        result2
    ";
    
    let program = parse_program(source)?;
    let _result = evaluator.evaluate_program(&program)?;
    
    let stats = evaluator.cache_stats();
    
    // Check that optimizations were used
    assert!(stats.stack_evals > 0, "Stack-based evaluation should have been used");
    assert!(stats.tail_calls > 0, "Tail call optimization should have been used");
    
    // Check that cache was used
    assert!(stats.hits > 0 || stats.misses > 0, "Cache should have been used");
    
    Ok(())
}

#[test]
fn test_memory_efficiency() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test that environment pooling reduces memory usage
    let source = "
        let make_function = \\n -> \\x -> x + n;
        let f1 = make_function 1;
        let f2 = make_function 2;
        let f3 = make_function 3;
        let f4 = make_function 4;
        let f5 = make_function 5;
        
        let result = f1 (f2 (f3 (f4 (f5 0))));
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct: 0 + 5 + 4 + 3 + 2 + 1 = 15
    assert!(matches!(result, ligature_ast::Value::Integer(15)));
    
    // Check environment pool usage
    let (available, total) = evaluator.env_pool_stats();
    assert!(available > 0, "Environment pool should have available environments");
    assert!(total > 0, "Environment pool should have been used");
    
    Ok(())
}

#[test]
fn test_stack_depth_limiting() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    evaluator.set_max_stack_depth(5); // Set very low limit
    
    // Test that stack depth limiting works
    let source = "
        let deep_nest = \\n ->
            if n <= 0 then 0
            else 1 + deep_nest (n - 1);
        let result = deep_nest 10;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program);
    
    // Should fail due to stack depth limit
    assert!(result.is_err(), "Should fail due to stack depth limit");
    
    Ok(())
}

#[test]
fn test_optimization_disabling() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Disable optimizations
    evaluator.set_tail_call_optimization(false);
    evaluator.set_stack_based_evaluation(false);
    
    let source = "
        let simple_add = \\x y -> x + y;
        let result = simple_add 5 3;
        result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct
    assert!(matches!(result, ligature_ast::Value::Integer(8)));
    
    // Check that no optimizations were used
    let stats = evaluator.cache_stats();
    assert_eq!(stats.stack_evals, 0, "Stack-based evaluation should be disabled");
    assert_eq!(stats.tail_calls, 0, "Tail call optimization should be disabled");
    
    Ok(())
}

#[test]
fn test_mixed_optimizations() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    evaluator.set_tail_call_optimization(true);
    evaluator.set_stack_based_evaluation(true);
    
    // Test a program that uses both optimizations
    let source = "
        let simple_math = \\x y -> x * y + x + y;
        let tail_sum = \\n acc ->
            if n <= 0 then acc
            else tail_sum (n - 1) (acc + n);
        
        let math_result = simple_math 3 4;
        let sum_result = tail_sum 5 0;
        sum_result
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct: sum from 0 to 5 = 15
    assert!(matches!(result, ligature_ast::Value::Integer(15)));
    
    let stats = evaluator.cache_stats();
    
    // Both optimizations should have been used
    assert!(stats.stack_evals > 0, "Stack-based evaluation should have been used");
    assert!(stats.tail_calls > 0, "Tail call optimization should have been used");
    
    Ok(())
}

#[test]
fn test_cache_performance() -> AstResult<()> {
    let mut evaluator = Evaluator::new();
    
    // Test that caching improves performance for repeated evaluations
    let source = "
        let expensive_calc = \\x -> x * x * x;
        let result1 = expensive_calc 5;
        let result2 = expensive_calc 5;
        let result3 = expensive_calc 5;
        result3
    ";
    
    let program = parse_program(source)?;
    let result = evaluator.evaluate_program(&program)?;
    
    // Verify the result is correct: 5^3 = 125
    assert!(matches!(result, ligature_ast::Value::Integer(125)));
    
    let stats = evaluator.cache_stats();
    
    // Should have some cache hits
    assert!(stats.hits > 0, "Should have cache hits for repeated expressions");
    assert!(stats.hit_rate() > 0.0, "Should have a positive hit rate");
    
    Ok(())
} 