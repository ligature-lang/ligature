#![no_main]

use libfuzzer_sys::fuzz_target;
use ligature_parser::{Parser, fuzzing::MutationFuzzer};

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, handling invalid UTF-8
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Skip invalid UTF-8
    };

    // Use mutation fuzzer to generate inputs
    let mut fuzzer = MutationFuzzer::new();
    
    // Add the input to corpus if it's valid UTF-8
    fuzzer.add_to_corpus(input.to_string());
    
    // Generate mutated inputs
    for _ in 0..5 {
        let mutated_input = fuzzer.generate_input();
        let mut parser = Parser::new();
        
        // Test parser with mutated input
        let result = parser.parse_expression(&mutated_input);
        
        // Ensure parser doesn't crash
        match result {
            Ok(_) => {
                // Valid parse - additional checks can be added
            }
            Err(_) => {
                // Invalid parse - verify error is reasonable
            }
        }
    }
}); 