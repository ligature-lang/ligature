use ligature_ast::AstResult;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    println!("Debugging union pattern parsing...");

    let mut parser = Parser::new();

    // Test 1: Parse just the pattern "Some(n)" as a pattern
    println!("\n=== Test 1: Parse Some(n) as Pattern ===");
    let pattern_source = "Some(n)";

    // Try to parse it as a pattern by wrapping it in a simple context
    let test_program = format!("let x = match 42 {{ {} => 0 }};", pattern_source);

    match parser.parse_program(&test_program) {
        Ok(program) => {
            println!("✓ Successfully parsed: {:?}", program);
        }
        Err(e) => {
            println!("✗ Failed to parse: {:?}", e);
        }
    }

    // Test 2: Try different pattern variations
    println!("\n=== Test 2: Different Pattern Variations ===");

    let patterns = vec![
        "Some(_)",
        "Some(x)",
        "Some(42)",
        "Some(Some(x))",
        "Some({ name = x })",
    ];

    for pattern in patterns {
        let test_program = format!("let x = match 42 {{ {} => 0 }};", pattern);
        match parser.parse_program(&test_program) {
            Ok(_) => {
                println!("✓ {} - Success", pattern);
            }
            Err(e) => {
                println!("✗ {} - Failed: {}", pattern, e);
            }
        }
    }

    // Test 3: Check if the issue is with the match expression structure
    println!("\n=== Test 3: Match Expression Structure ===");

    let match_tests = vec![
        "let x = match Some(42) { Some => 0 };",
        "let x = match Some(42) { Some(n) => n };",
        "let x = match Some(42) { Some(_) => 0 };",
    ];

    for test in match_tests {
        match parser.parse_program(test) {
            Ok(_) => {
                println!("✓ Success: {}", test);
            }
            Err(e) => {
                println!("✗ Failed: {} - {}", test, e);
            }
        }
    }

    // Test 4: Test individual pattern parsing
    println!("\n=== Test 4: Individual Pattern Parsing ===");

    let simple_patterns = vec!["_", "x", "42", "(x)", "Some"];

    for pattern in simple_patterns {
        let test_program = format!("let x = match 42 {{ {} => 0 }};", pattern);
        match parser.parse_program(&test_program) {
            Ok(_) => {
                println!("✓ {} - Success", pattern);
            }
            Err(e) => {
                println!("✗ {} - Failed: {}", pattern, e);
            }
        }
    }

    // Test 5: Test union pattern specifically
    println!("\n=== Test 5: Union Pattern Specific Tests ===");

    let union_tests = vec![
        "let x = match Some(42) { Some => 0 };",
        "let x = match Some(42) { Some() => 0 };",
        "let x = match Some(42) { Some(x) => x };",
        "let x = match Some(42) { Some(_) => 0 };",
    ];

    for test in union_tests {
        match parser.parse_program(test) {
            Ok(_) => {
                println!("✓ Success: {}", test);
            }
            Err(e) => {
                println!("✗ Failed: {} - {}", test, e);
            }
        }
    }

    println!("\n✓ Debug tests completed!");
    Ok(())
}
