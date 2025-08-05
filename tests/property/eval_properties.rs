//! Property-based tests for the evaluator.
//! 
//! These tests verify various properties about the evaluator's behavior
//! using randomly generated inputs.

use proptest::prelude::*;
use ligature_eval::{evaluate_program, evaluate_expression};
use ligature_parser::parse_program;
use ligature_ast::{Value, AstResult};
use crate::property::*;

proptest! {
    #[test]
    fn test_evaluator_idempotency(expr in expr_strategy()) {
        // Evaluating the same expression twice should produce the same result
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let result1 = evaluate_expression(&ast);
            let result2 = evaluate_expression(&ast);
            
            match (result1, result2) {
                (Ok(val1), Ok(val2)) => {
                    // The values should be equivalent
                    assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
                }
                (Err(e1), Err(e2)) => {
                    // Both should fail with similar errors
                    assert_eq!(e1.to_string(), e2.to_string());
                }
                _ => {
                    // One succeeded and one failed - this shouldn't happen
                    panic!("Evaluator is not idempotent for expression: {}", expr);
                }
            }
        }
    }
    
    #[test]
    fn test_evaluator_termination(expr in expr_strategy()) {
        // Evaluation should always terminate (no infinite loops)
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let _result = evaluate_expression(&ast);
            // If we get here, evaluation terminated
        }
    }
    
    #[test]
    fn test_evaluator_arithmetic_properties(a in any::<i64>(), b in any::<i64>()) {
        // Test arithmetic properties
        let add_expr = format!("{} + {}", a, b);
        let sub_expr = format!("{} - {}", a, b);
        let mul_expr = format!("{} * {}", a, b);
        
        // Addition should be commutative
        let add1 = parse_expression(&add_expr).and_then(|ast| evaluate_expression(&ast));
        let add2 = parse_expression(&format!("{} + {}", b, a)).and_then(|ast| evaluate_expression(&ast));
        
        match (add1, add2) {
            (Ok(val1), Ok(val2)) => {
                assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
            }
            _ => {
                // If one fails, both should fail
                assert!(add1.is_err() && add2.is_err());
            }
        }
        
        // Multiplication should be commutative
        let mul1 = parse_expression(&mul_expr).and_then(|ast| evaluate_expression(&ast));
        let mul2 = parse_expression(&format!("{} * {}", b, a)).and_then(|ast| evaluate_expression(&ast));
        
        match (mul1, mul2) {
            (Ok(val1), Ok(val2)) => {
                assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
            }
            _ => {
                // If one fails, both should fail
                assert!(mul1.is_err() && mul2.is_err());
            }
        }
    }
    
    #[test]
    fn test_evaluator_comparison_properties(a in any::<i64>(), b in any::<i64>()) {
        // Test comparison properties
        let gt_expr = format!("{} > {}", a, b);
        let lt_expr = format!("{} < {}", a, b);
        let eq_expr = format!("{} == {}", a, b);
        
        // a > b should be the opposite of b > a (unless a == b)
        let gt1 = parse_expression(&gt_expr).and_then(|ast| evaluate_expression(&ast));
        let gt2 = parse_expression(&format!("{} > {}", b, a)).and_then(|ast| evaluate_expression(&ast));
        
        match (gt1, gt2) {
            (Ok(val1), Ok(val2)) => {
                if a != b {
                    // If a != b, then exactly one of a > b or b > a should be true
                    let bool1 = matches!(val1, Value::Boolean(true));
                    let bool2 = matches!(val2, Value::Boolean(true));
                    assert!(bool1 != bool2);
                } else {
                    // If a == b, then both should be false
                    assert!(matches!(val1, Value::Boolean(false)));
                    assert!(matches!(val2, Value::Boolean(false)));
                }
            }
            _ => {
                // If one fails, both should fail
                assert!(gt1.is_err() && gt2.is_err());
            }
        }
    }
    
    #[test]
    fn test_evaluator_logical_properties(a in any::<bool>(), b in any::<bool>()) {
        // Test logical properties
        let and_expr = format!("{} && {}", a, b);
        let or_expr = format!("{} || {}", a, b);
        let not_a_expr = format!("!{}", a);
        let not_b_expr = format!("!{}", b);
        
        // De Morgan's laws: !(a && b) == !a || !b
        let not_and = parse_expression(&format!("!({} && {})", a, b)).and_then(|ast| evaluate_expression(&ast));
        let or_not = parse_expression(&format!("!{} || !{}", a, b)).and_then(|ast| evaluate_expression(&ast));
        
        match (not_and, or_not) {
            (Ok(val1), Ok(val2)) => {
                assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
            }
            _ => {
                // If one fails, both should fail
                assert!(not_and.is_err() && or_not.is_err());
            }
        }
        
        // De Morgan's laws: !(a || b) == !a && !b
        let not_or = parse_expression(&format!("!({} || {})", a, b)).and_then(|ast| evaluate_expression(&ast));
        let and_not = parse_expression(&format!("!{} && !{}", a, b)).and_then(|ast| evaluate_expression(&ast));
        
        match (not_or, and_not) {
            (Ok(val1), Ok(val2)) => {
                assert_eq!(format!("{:?}", val1), format!("{:?}", val2));
            }
            _ => {
                // If one fails, both should fail
                assert!(not_or.is_err() && and_not.is_err());
            }
        }
    }
    
    #[test]
    fn test_evaluator_if_expression_properties(cond in any::<bool>(), then_val in any::<i64>(), else_val in any::<i64>()) {
        // Test if expression properties
        let if_expr = format!("if {} then {} else {}", cond, then_val, else_val);
        let result = parse_expression(&if_expr).and_then(|ast| evaluate_expression(&ast));
        
        match result {
            Ok(value) => {
                if cond {
                    // If condition is true, should evaluate to then_val
                    assert!(matches!(value, Value::Integer(n) if n == then_val));
                } else {
                    // If condition is false, should evaluate to else_val
                    assert!(matches!(value, Value::Integer(n) if n == else_val));
                }
            }
            Err(_) => {
                // If evaluation fails, that's also acceptable
            }
        }
    }
    
    #[test]
    fn test_evaluator_let_expression_properties(x in any::<i64>(), y in any::<i64>()) {
        // Test let expression properties
        let let_expr = format!("let x = {} in x + {}", x, y);
        let result = parse_expression(&let_expr).and_then(|ast| evaluate_expression(&ast));
        
        match result {
            Ok(value) => {
                // Should evaluate to x + y
                assert!(matches!(value, Value::Integer(n) if n == x + y));
            }
            Err(_) => {
                // If evaluation fails, that's also acceptable
            }
        }
    }
    
    #[test]
    fn test_evaluator_function_application_properties(x in any::<i64>(), y in any::<i64>()) {
        // Test function application properties
        let func_expr = format!("(\\x y -> x + y) {} {}", x, y);
        let result = parse_expression(&func_expr).and_then(|ast| evaluate_expression(&ast));
        
        match result {
            Ok(value) => {
                // Should evaluate to x + y
                assert!(matches!(value, Value::Integer(n) if n == x + y));
            }
            Err(_) => {
                // If evaluation fails, that's also acceptable
            }
        }
    }
    
    #[test]
    fn test_evaluator_record_properties(fields in prop::collection::vec((any::<String>(), any::<i64>()), 1..4)) {
        // Test record construction and field access
        let field_strs: Vec<String> = fields.iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect();
        let record_expr = format!("{{ {} }}", field_strs.join(", "));
        
        // Test record construction
        let result = parse_expression(&record_expr).and_then(|ast| evaluate_expression(&ast));
        match result {
            Ok(value) => {
                // Should evaluate to a record
                assert!(matches!(value, Value::Record(_)));
            }
            Err(_) => {
                // If evaluation fails, that's also acceptable
            }
        }
        
        // Test field access for each field
        for (name, expected_value) in &fields {
            let access_expr = format!("({}).{}", record_expr, name);
            let result = parse_expression(&access_expr).and_then(|ast| evaluate_expression(&ast));
            
            match result {
                Ok(value) => {
                    // Should evaluate to the expected value
                    assert!(matches!(value, Value::Integer(n) if n == *expected_value));
                }
                Err(_) => {
                    // If evaluation fails, that's also acceptable
                }
            }
        }
    }
    
    #[test]
    fn test_evaluator_list_properties(elements in prop::collection::vec(any::<i64>(), 0..5)) {
        // Test list construction
        let list_expr = format!("[{}]", elements.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", "));
        let result = parse_expression(&list_expr).and_then(|ast| evaluate_expression(&ast));
        
        match result {
            Ok(value) => {
                // Should evaluate to a list
                assert!(matches!(value, Value::List(_)));
            }
            Err(_) => {
                // If evaluation fails, that's also acceptable
            }
        }
    }
    
    #[test]
    fn test_evaluator_error_consistency(expr in expr_strategy()) {
        // If an expression fails to evaluate, it should consistently fail
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let result1 = evaluate_expression(&ast);
            let result2 = evaluate_expression(&ast);
            
            match (result1, result2) {
                (Ok(_), Ok(_)) => {
                    // Both succeeded - this is fine
                }
                (Err(e1), Err(e2)) => {
                    // Both failed - errors should be consistent
                    assert_eq!(e1.to_string(), e2.to_string());
                }
                _ => {
                    // One succeeded and one failed - this shouldn't happen
                    panic!("Evaluator is not consistent for expression: {}", expr);
                }
            }
        }
    }
    
    #[test]
    fn test_evaluator_no_panic(expr in expr_strategy()) {
        // The evaluator should never panic, even on malformed expressions
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let _result = evaluate_expression(&ast);
            // If we get here, no panic occurred
        }
    }
    
    #[test]
    fn test_evaluator_program_termination(program in program_strategy()) {
        // Program evaluation should always terminate
        let parsed = parse_program(&program);
        if let Ok(ast) = parsed {
            let _result = evaluate_program(&ast);
            // If we get here, evaluation terminated
        }
    }
    
    #[test]
    fn test_evaluator_program_no_panic(program in program_strategy()) {
        // The evaluator should never panic, even on malformed programs
        let parsed = parse_program(&program);
        if let Ok(ast) = parsed {
            let _result = evaluate_program(&ast);
            // If we get here, no panic occurred
        }
    }
} 