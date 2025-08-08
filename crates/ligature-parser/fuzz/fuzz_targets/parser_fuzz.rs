#![no_main]

use libfuzzer_sys::fuzz_target;
use ligature_parser::{Parser, fuzzing::test_parser_robustness};

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, handling invalid UTF-8
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return, // Skip invalid UTF-8
    };

    // Test that parser handles all inputs without crashing
    let _result = test_parser_robustness(input);
    // Should not panic, regardless of success/failure
}); 