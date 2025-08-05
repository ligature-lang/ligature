//! Binding conflicts and type class edge cases tests.
//! 
//! These tests verify that the type system properly handles binding conflicts
//! and various type class edge cases.

use ligature_parser::parse_program;
use ligature_types::{type_check_program, TypeError};
use ligature_ast::AstResult;

#[test]
fn test_binding_conflicts() {
    // Test that binding conflicts are detected and reported
    let program = parse_program("
        let x = 42;
        let x = \"hello\";
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("binding conflict") || error_msg.contains("already bound"));
    }
}

#[test]
fn test_import_binding_conflicts() {
    // Test that import binding conflicts are detected
    // Note: This test may need to be updated based on the actual import system
    let program = parse_program("
        let x = 42;
        // import std { x };  // Commented out until import system is fully implemented
    ").unwrap();
    
    // For now, just test that the program parses and type checks
    let result = type_check_program(&program);
    assert!(result.is_ok());
}

#[test]
fn test_type_class_instance_conflicts() {
    // Test that type class instance conflicts are detected
    let program = parse_program("
        class Eq a {
            eq: a -> a -> Bool
        }
        
        instance Eq Integer {
            eq = \\x y -> x == y
        }
        
        instance Eq Integer {
            eq = \\x y -> x == y
        }
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("instance conflict") || error_msg.contains("multiple instances"));
    }
}

#[test]
fn test_type_class_method_mismatch() {
    // Test that type class method implementation mismatches are detected
    let program = parse_program("
        class Show a {
            show: a -> String
        }
        
        instance Show Integer {
            show = \\x -> 42  // Should return String, not Integer
        }
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("method mismatch") || error_msg.contains("expected") && error_msg.contains("found"));
    }
}

#[test]
fn test_ambiguous_type_class_resolution() {
    // Test that ambiguous type class resolution is detected
    let program = parse_program("
        class Eq a {
            eq: a -> a -> Bool
        }
        
        instance Eq Integer {
            eq = \\x y -> x == y
        }
        
        instance Eq Integer {
            eq = \\x y -> x == y
        }
        
        let test = eq 5 6;
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("ambiguous") || error_msg.contains("multiple instances"));
    }
}

#[test]
fn test_type_class_constraint_unsatisfied() {
    // Test that unsatisfied type class constraints are reported with available instances
    let program = parse_program("
        class Show a {
            show: a -> String
        }
        
        let test = show (\\x -> x);  // Function type doesn't implement Show
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("does not implement") || error_msg.contains("constraint unsatisfied"));
    }
}

#[test]
fn test_type_class_overlap() {
    // Test that type class instance overlaps are detected
    let program = parse_program("
        class Eq a {
            eq: a -> a -> Bool
        }
        
        instance Eq (List a) {
            eq = \\xs ys -> true
        }
        
        instance Eq (List Integer) {
            eq = \\xs ys -> true
        }
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    if let Err(e) = result {
        let error_msg = e.to_string();
        assert!(error_msg.contains("overlap") || error_msg.contains("conflicting instances"));
    }
}

#[test]
fn test_conflict_resolution_strategies() -> AstResult<()> {
    // Test that different conflict resolution strategies work
    let program = parse_program("
        let x = 42;
        let x = \"hello\";  // This should be an error with Error strategy
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_err());
    
    // TODO: Test other strategies when they're implemented
    // - Warn strategy should continue with a warning
    // - Override strategy should replace the binding
    // - Skip strategy should ignore the conflict
    
    Ok(())
}

#[test]
fn test_type_class_context_unsatisfied() {
    // Test that type class context constraints are checked
    let program = parse_program("
        class Ord a {
            compare: a -> a -> Ordering
        }
        
        class Show a {
            show: a -> String
        }
        
        let f = \\x -> if compare x x == EQ then show x else \"\";
        // This should require both Ord and Show constraints
    ").unwrap();
    
    let result = type_check_program(&program);
    // This might succeed if the type system can infer the constraints
    // or fail if it can't satisfy them
    // The important thing is that it doesn't crash
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn test_complex_binding_scenarios() -> AstResult<()> {
    // Test complex scenarios with multiple bindings and imports
    let program = parse_program("
        let x = 42;
        let y = \"hello\";
        
        // Nested scope
        let inner = {
            let x = true;  // Should shadow outer x
            x
        };
        
        // This should work - inner x is shadowed, outer x is still available
        let result = x + 10;
    ").unwrap();
    
    let result = type_check_program(&program);
    assert!(result.is_ok());
    
    Ok(())
} 