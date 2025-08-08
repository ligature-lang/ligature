#![no_main]

use libfuzzer_sys::fuzz_target;
use ligature_parser::{Parser, fuzzing::test_parser_performance};

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, handling invalid UTF-8
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Skip invalid UTF-8
    };

    // Test expression parsing specifically
    let mut parser = Parser::new();
    let result = parser.parse_expression(input);

    // Ensure parser doesn't crash
    // Result can be Ok or Err, but should never panic
    match result {
        Ok(_) => {
            // Valid parse - verify AST is well-formed
            // Additional validation can be added here
        }
        Err(_) => {
            // Invalid parse - verify error is reasonable
            // Error should have valid span and message
        }
    }

    // Test performance bounds
    let _perf_result = test_parser_performance(input);
}); 