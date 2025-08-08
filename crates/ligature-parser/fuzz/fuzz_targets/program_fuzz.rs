#![no_main]

use libfuzzer_sys::fuzz_target;
use ligature_parser::Parser;

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, handling invalid UTF-8
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Skip invalid UTF-8
    };

    // Test program parsing
    let mut parser = Parser::new();
    let result = parser.parse_program(input);

    // Test program parsing
    match result {
        Ok(program) => {
            // Verify program structure
            assert!(program.declarations.len() <= 1000); // Reasonable size limit
        }
        Err(error) => {
            // Verify error properties
            assert!(!error.to_string().is_empty());
        }
    }
}); 