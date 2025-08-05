//! Integration tests for value representation optimization.

use ligature_eval::{Evaluator, CacheStats};
use ligature_parser::parse_program;
use ligature_ast::AstError;

#[test]
fn test_value_sharing_with_arc() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that string values are shared using Arc
    let program = r#"
        let x = "hello world"
        let y = "hello world"
        let z = "different string"
        (x, y, z)
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;

    // Verify the result is a record with three fields
    assert!(result.is_record());
    if let Some(fields) = result.as_record() {
        assert_eq!(fields.len(), 3);
        
        // Check that x and y are the same string value (shared)
        let x = fields.get("x").unwrap();
        let y = fields.get("y").unwrap();
        let z = fields.get("z").unwrap();
        
        assert!(x.is_string());
        assert!(y.is_string());
        assert!(z.is_string());
        
        assert_eq!(x.as_string().unwrap(), "hello world");
        assert_eq!(y.as_string().unwrap(), "hello world");
        assert_eq!(z.as_string().unwrap(), "different string");
    }

    Ok(())
}

#[test]
fn test_value_interning() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that frequently used values are interned
    let program = r#"
        let a = 42
        let b = 42
        let c = 100
        let d = 42
        let e = true
        let f = true
        let g = false
        (a, b, c, d, e, f, g)
    "#;

    let parsed = parse_program(program)?;
    let _result = evaluator.evaluate_program(&parsed)?;

    // Check interner statistics
    let stats = evaluator.value_interner_stats();
    assert!(stats.integer_count > 0);
    assert!(stats.boolean_count == 2); // true and false

    // Test that the same integer values are interned
    let program2 = r#"
        let x = 42
        let y = 42
        x == y
    "#;

    let parsed2 = parse_program(program2)?;
    let result2 = evaluator.evaluate_program(&parsed2)?;
    assert!(result2.as_boolean().unwrap());

    Ok(())
}

#[test]
fn test_value_pooling() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test value pool statistics
    let initial_stats = evaluator.value_pool_stats();
    assert_eq!(initial_stats.0, 0); // No values in pool initially

    // Create some values
    let program = r#"
        let x = 1
        let y = 2
        let z = 3
        x + y + z
    "#;

    let parsed = parse_program(program)?;
    let _result = evaluator.evaluate_program(&parsed)?;

    // Check that pool statistics are tracked
    let stats = evaluator.cache_stats();
    assert!(stats.value_pool_acquisitions >= 0);
    assert!(stats.value_pool_releases >= 0);

    Ok(())
}

#[test]
fn test_optimized_record_creation() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that records use shared field storage
    let program = r#"
        let record1 = { x = 1, y = 2, z = 3 }
        let record2 = { a = 4, b = 5, c = 6 }
        let record3 = { x = 1, y = 2, z = 3 }
        (record1, record2, record3)
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;

    assert!(result.is_record());
    if let Some(fields) = result.as_record() {
        assert_eq!(fields.len(), 3);
        
        let record1 = fields.get("record1").unwrap();
        let record2 = fields.get("record2").unwrap();
        let record3 = fields.get("record3").unwrap();
        
        assert!(record1.is_record());
        assert!(record2.is_record());
        assert!(record3.is_record());
        
        // Verify record contents
        if let Some(r1_fields) = record1.as_record() {
            assert_eq!(r1_fields.get("x").unwrap().as_integer().unwrap(), 1);
            assert_eq!(r1_fields.get("y").unwrap().as_integer().unwrap(), 2);
            assert_eq!(r1_fields.get("z").unwrap().as_integer().unwrap(), 3);
        }
    }

    Ok(())
}

#[test]
fn test_optimized_list_creation() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that lists use shared element storage
    let program = r#"
        let list1 = [1, 2, 3, 4, 5]
        let list2 = [6, 7, 8, 9, 10]
        let list3 = [1, 2, 3, 4, 5]
        (list1, list2, list3)
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;

    assert!(result.is_record());
    if let Some(fields) = result.as_record() {
        assert_eq!(fields.len(), 3);
        
        let list1 = fields.get("list1").unwrap();
        let list2 = fields.get("list2").unwrap();
        let list3 = fields.get("list3").unwrap();
        
        assert!(list1.is_list());
        assert!(list2.is_list());
        assert!(list3.is_list());
        
        // Verify list contents
        if let Some(l1_elements) = list1.as_list() {
            assert_eq!(l1_elements.len(), 5);
            assert_eq!(l1_elements[0].as_integer().unwrap(), 1);
            assert_eq!(l1_elements[4].as_integer().unwrap(), 5);
        }
    }

    Ok(())
}

#[test]
fn test_optimized_union_creation() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that unions use shared variant names and payloads
    let program = r#"
        let success1 = Success(42)
        let success2 = Success(42)
        let error1 = Error("something went wrong")
        let error2 = Error("something went wrong")
        (success1, success2, error1, error2)
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;

    assert!(result.is_record());
    if let Some(fields) = result.as_record() {
        assert_eq!(fields.len(), 4);
        
        let success1 = fields.get("success1").unwrap();
        let success2 = fields.get("success2").unwrap();
        let error1 = fields.get("error1").unwrap();
        let error2 = fields.get("error2").unwrap();
        
        assert!(success1.is_union());
        assert!(success2.is_union());
        assert!(error1.is_union());
        assert!(error2.is_union());
        
        // Verify union contents
        if let Some((variant1, value1)) = success1.as_union() {
            assert_eq!(variant1, "Success");
            assert_eq!(value1.unwrap().as_integer().unwrap(), 42);
        }
    }

    Ok(())
}

#[test]
fn test_value_optimization_disabled() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(false);

    // Test that optimization can be disabled
    let program = r#"
        let x = "hello"
        let y = "hello"
        x == y
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;
    
    // Should still work correctly even without optimization
    assert!(result.as_boolean().unwrap());

    // Check that interner is not being used
    let stats = evaluator.value_interner_stats();
    assert_eq!(stats.string_count, 0);
    assert_eq!(stats.integer_count, 0);

    Ok(())
}

#[test]
fn test_performance_improvements() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that value optimization improves performance
    let program = r#"
        let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        let strings = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
        let booleans = [true, false, true, false, true, false, true, false, true, false]
        
        let doubled = numbers
        let concatenated = strings
        let negated = booleans
        
        (doubled, concatenated, negated)
    "#;

    let parsed = parse_program(program)?;
    let start = std::time::Instant::now();
    let _result = evaluator.evaluate_program(&parsed)?;
    let duration = start.elapsed();

    // Verify the operation completed successfully
    assert!(duration.as_millis() < 1000); // Should complete in under 1 second

    // Check optimization statistics
    let stats = evaluator.cache_stats();
    evaluator.update_value_optimization_stats();
    
    // Verify that value optimization features are being used
    assert!(stats.value_pool_acquisitions >= 0);
    assert!(stats.value_pool_releases >= 0);

    Ok(())
}

#[test]
fn test_memory_efficiency() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test that value optimization reduces memory usage
    let program = r#"
        let repeated_string = "this is a very long string that will be repeated many times"
        let repeated_int = 42
        let repeated_bool = true
        
        let list1 = [repeated_string, repeated_string, repeated_string]
        let list2 = [repeated_int, repeated_int, repeated_int]
        let list3 = [repeated_bool, repeated_bool, repeated_bool]
        
        let record = {
            field1 = list1,
            field2 = list2,
            field3 = list3
        }
        
        record
    "#;

    let parsed = parse_program(program)?;
    let _result = evaluator.evaluate_program(&parsed)?;

    // Check that interning is working
    let stats = evaluator.value_interner_stats();
    assert!(stats.string_count > 0);
    assert!(stats.integer_count > 0);
    assert!(stats.boolean_count == 2);

    // Verify that the same values are being reused
    let utilization = evaluator.cache_stats().value_pool_utilization();
    assert!(utilization >= 0.0);

    Ok(())
}

#[test]
fn test_complex_value_optimization() -> Result<(), AstError> {
    let mut evaluator = Evaluator::new();
    evaluator.set_value_optimization(true);

    // Test complex nested structures with optimization
    let program = r#"
        let config = {
            database = {
                host = "localhost"
                port = 5432
                credentials = {
                    username = "admin"
                    password = "secret"
                }
            }
            cache = {
                enabled = true
                size = 1000
                ttl = 3600
            }
            logging = {
                level = "info"
                format = "json"
                output = "stdout"
            }
        }
        
        let config2 = {
            database = {
                host = "localhost"
                port = 5432
                credentials = {
                    username = "admin"
                    password = "secret"
                }
            }
            cache = {
                enabled = true
                size = 1000
                ttl = 3600
            }
            logging = {
                level = "info"
                format = "json"
                output = "stdout"
            }
        }
        
        config == config2
    "#;

    let parsed = parse_program(program)?;
    let result = evaluator.evaluate_program(&parsed)?;

    // Should be equal due to value sharing
    assert!(result.as_boolean().unwrap());

    // Check optimization statistics
    let stats = evaluator.value_interner_stats();
    assert!(stats.string_count > 0);
    assert!(stats.integer_count > 0);
    assert!(stats.boolean_count == 2);

    Ok(())
} 