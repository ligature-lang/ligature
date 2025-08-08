#![no_main]

use libfuzzer_sys::fuzz_target;
use ligature_parser::{Parser, fuzzing::GrammarFuzzer};

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, handling invalid UTF-8
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Skip invalid UTF-8
    };

    // Use grammar fuzzer to generate structured inputs
    let fuzzer = GrammarFuzzer::new();
    
    // Generate grammar-based inputs
    let grammar_expr = fuzzer.generate_expression();
    let grammar_program = fuzzer.generate_program();
    
    let mut parser = Parser::new();
    
    // Test parser with grammar-generated expressions
    let expr_result = parser.parse_expression(&grammar_expr);
    match expr_result {
        Ok(_) => {
            // Valid parse - grammar should generate mostly valid inputs
        }
        Err(_) => {
            // Invalid parse - should be rare with grammar-based generation
        }
    }
    
    // Test parser with grammar-generated programs
    let program_result = parser.parse_program(&grammar_program);
    match program_result {
        Ok(program) => {
            // Verify program structure
            assert!(program.declarations.len() <= 100); // Grammar should generate reasonable programs
        }
        Err(_) => {
            // Invalid parse - should be rare with grammar-based generation
        }
    }
    
    // Also test the original input
    let _result = parser.parse_expression(input);
}); 