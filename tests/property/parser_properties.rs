//! Property-based tests for the parser.
//! 
//! These tests verify various properties about the parser's behavior
//! using randomly generated inputs.

use proptest::prelude::*;
use ligature_parser::{parse_program, parse_expression};
use ligature_ast::AstResult;
use crate::property::*;

proptest! {
    #[test]
    fn test_parser_idempotency(expr in expr_strategy()) {
        // Parsing the same expression twice should produce the same result
        let result1 = parse_expression(&expr);
        let result2 = parse_expression(&expr);
        
        match (result1, result2) {
            (Ok(ast1), Ok(ast2)) => {
                // The ASTs should be equivalent
                assert_eq!(format!("{:?}", ast1), format!("{:?}", ast2));
            }
            (Err(e1), Err(e2)) => {
                // Both should fail with similar errors
                assert_eq!(e1.to_string(), e2.to_string());
            }
            _ => {
                // One succeeded and one failed - this shouldn't happen
                panic!("Parser is not idempotent for expression: {}", expr);
            }
        }
    }
    
    #[test]
    fn test_parser_whitespace_invariance(expr in expr_strategy()) {
        // Adding whitespace should not change parsing behavior
        let expr_with_ws = format!("  {}  ", expr);
        let result1 = parse_expression(&expr);
        let result2 = parse_expression(&expr_with_ws);
        
        match (result1, result2) {
            (Ok(ast1), Ok(ast2)) => {
                // The ASTs should be equivalent
                assert_eq!(format!("{:?}", ast1), format!("{:?}", ast2));
            }
            (Err(e1), Err(e2)) => {
                // Both should fail with similar errors
                assert_eq!(e1.to_string(), e2.to_string());
            }
            _ => {
                panic!("Parser is not whitespace invariant for expression: {}", expr);
            }
        }
    }
    
    #[test]
    fn test_parser_comment_invariance(expr in expr_strategy()) {
        // Adding comments should not change parsing behavior
        let expr_with_comments = format!("// comment\n{} // inline comment", expr);
        let result1 = parse_expression(&expr);
        let result2 = parse_expression(&expr_with_comments);
        
        match (result1, result2) {
            (Ok(ast1), Ok(ast2)) => {
                // The ASTs should be equivalent
                assert_eq!(format!("{:?}", ast1), format!("{:?}", ast2));
            }
            (Err(e1), Err(e2)) => {
                // Both should fail with similar errors
                assert_eq!(e1.to_string(), e2.to_string());
            }
            _ => {
                panic!("Parser is not comment invariant for expression: {}", expr);
            }
        }
    }
    
    #[test]
    fn test_parser_literal_roundtrip(integer in any::<i64>()) {
        // Parsing a literal should produce the expected AST
        let expr = integer.to_string();
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should represent the same integer
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(&integer.to_string()));
            }
            Err(e) => {
                // Integer literals should always parse successfully
                panic!("Failed to parse integer literal {}: {}", integer, e);
            }
        }
    }
    
    #[test]
    fn test_parser_string_literal_roundtrip(s in any::<String>()) {
        // Parsing a string literal should produce the expected AST
        let expr = format!("\"{}\"", s.replace("\"", "\\\""));
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should represent the same string
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(&s));
            }
            Err(e) => {
                // String literals should always parse successfully
                panic!("Failed to parse string literal {}: {}", s, e);
            }
        }
    }
    
    #[test]
    fn test_parser_boolean_literal_roundtrip(b in any::<bool>()) {
        // Parsing a boolean literal should produce the expected AST
        let expr = b.to_string();
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should represent the same boolean
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(&b.to_string()));
            }
            Err(e) => {
                // Boolean literals should always parse successfully
                panic!("Failed to parse boolean literal {}: {}", b, e);
            }
        }
    }
    
    #[test]
    fn test_parser_arithmetic_roundtrip(a in any::<i64>(), b in any::<i64>(), op in ["+", "-", "*", "/"]) {
        // Parsing arithmetic expressions should work correctly
        let expr = format!("{} {} {}", a, op, b);
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the operation
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(op));
            }
            Err(e) => {
                // Basic arithmetic expressions should parse successfully
                panic!("Failed to parse arithmetic expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_comparison_roundtrip(a in any::<i64>(), b in any::<i64>(), op in [">", "<", "==", "!="]) {
        // Parsing comparison expressions should work correctly
        let expr = format!("{} {} {}", a, op, b);
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the operation
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(op));
            }
            Err(e) => {
                // Basic comparison expressions should parse successfully
                panic!("Failed to parse comparison expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_logical_roundtrip(a in any::<bool>(), b in any::<bool>(), op in ["&&", "||"]) {
        // Parsing logical expressions should work correctly
        let expr = format!("{} {} {}", a, op, b);
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the operation
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains(op));
            }
            Err(e) => {
                // Basic logical expressions should parse successfully
                panic!("Failed to parse logical expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_if_expression_roundtrip(cond in any::<bool>(), then_val in any::<i64>(), else_val in any::<i64>()) {
        // Parsing if expressions should work correctly
        let expr = format!("if {} then {} else {}", cond, then_val, else_val);
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the if expression structure
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains("if"));
            }
            Err(e) => {
                // Basic if expressions should parse successfully
                panic!("Failed to parse if expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_record_roundtrip(fields in prop::collection::vec((any::<String>(), any::<i64>()), 1..4)) {
        // Parsing record expressions should work correctly
        let field_strs: Vec<String> = fields.iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect();
        let expr = format!("{{ {} }}", field_strs.join(", "));
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the record structure
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains("record") || ast_str.contains("Record"));
            }
            Err(e) => {
                // Basic record expressions should parse successfully
                panic!("Failed to parse record expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_list_roundtrip(elements in prop::collection::vec(any::<i64>(), 0..5)) {
        // Parsing list expressions should work correctly
        let expr = format!("[{}]", elements.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", "));
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the list structure
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains("list") || ast_str.contains("List"));
            }
            Err(e) => {
                // Basic list expressions should parse successfully
                panic!("Failed to parse list expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_function_roundtrip(param in any::<String>(), body in any::<i64>()) {
        // Parsing function expressions should work correctly
        let expr = format!("\\{} -> {}", param, body);
        let result = parse_expression(&expr);
        
        match result {
            Ok(ast) => {
                // The AST should contain the function structure
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains("lambda") || ast_str.contains("Lambda") || ast_str.contains("function"));
            }
            Err(e) => {
                // Basic function expressions should parse successfully
                panic!("Failed to parse function expression {}: {}", expr, e);
            }
        }
    }
    
    #[test]
    fn test_parser_program_roundtrip(program in program_strategy()) {
        // Parsing programs should work correctly
        let result = parse_program(&program);
        
        match result {
            Ok(ast) => {
                // The AST should contain the program structure
                let ast_str = format!("{:?}", ast);
                assert!(ast_str.contains("program") || ast_str.contains("Program"));
            }
            Err(e) => {
                // Basic programs should parse successfully
                panic!("Failed to parse program {}: {}", program, e);
            }
        }
    }
    
    #[test]
    fn test_parser_error_consistency(expr in expr_strategy()) {
        // If an expression fails to parse, it should consistently fail
        let result1 = parse_expression(&expr);
        let result2 = parse_expression(&expr);
        
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
                panic!("Parser is not consistent for expression: {}", expr);
            }
        }
    }
    
    #[test]
    fn test_parser_no_panic(expr in any::<String>()) {
        // The parser should never panic, even on malformed input
        let _result = parse_expression(&expr);
        // If we get here, no panic occurred
    }
    
    #[test]
    fn test_parser_no_panic_program(program in any::<String>()) {
        // The parser should never panic, even on malformed programs
        let _result = parse_program(&program);
        // If we get here, no panic occurred
    }
} 