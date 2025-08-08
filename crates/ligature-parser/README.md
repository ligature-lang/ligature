# Ligature Parser

This crate provides the parser for the Ligature language, converting source text into an Abstract Syntax Tree (AST).

## Features

- **Robust Parsing**: Handles all valid Ligature syntax constructs
- **Error Recovery**: Graceful handling of malformed input
- **Performance Optimized**: Fast parsing with reasonable memory usage
- **Comprehensive Testing**: Extensive test suite including property-based testing
- **Fuzzing Support**: Built-in fuzzing infrastructure for robustness testing

## Usage

```rust
use ligature_parser::{Parser, parse_program, parse_expression};

// Parse a complete program
let program = parse_program("let x = 42; let y = x + 1;")?;

// Parse a single expression
let expr = parse_expression("x + y * 2")?;

// Use the parser directly
let mut parser = Parser::new();
let result = parser.parse_program("let x = 42;")?;
```

## Fuzzing Infrastructure

The parser includes comprehensive fuzzing infrastructure to ensure robustness and catch edge cases:

### Features

- **Grammar-based Fuzzing**: Generates structured inputs based on the Ligature grammar
- **Mutation-based Fuzzing**: Mutates existing inputs to find edge cases
- **Property-based Testing**: Uses proptest to verify parser properties
- **Error Recovery Testing**: Tests parser's ability to handle and recover from errors
- **Performance Testing**: Ensures parser performance remains reasonable

### Running Fuzzing Tests

```bash
# Run all fuzzing tests
cargo test --features fuzzing

# Run property-based tests
cargo test --features fuzzing fuzzing::property_tests

# Run specific fuzzing components
cargo test --features fuzzing fuzzing::tests
```

### Fuzzing Components

#### GrammarFuzzer
Generates structured inputs based on the Ligature grammar:
- Expression generation
- Program generation
- Type generation
- Depth and length limits

#### MutationFuzzer
Mutates existing inputs using various strategies:
- Insertion mutations
- Deletion mutations
- Replacement mutations
- Duplication mutations
- Truncation mutations

#### Property Tests
Verify parser properties:
- **Robustness**: Parser handles all inputs without crashing
- **Performance**: Parser completes within reasonable time bounds
- **Memory**: Parser doesn't leak memory or cause OOM
- **Grammar**: Grammar fuzzer generates reasonable inputs
- **Mutation**: Mutation fuzzer generates varied inputs

## Architecture

The parser is built using the Pest parsing library and follows a recursive descent approach:

1. **Lexical Analysis**: Tokenizes input using Pest grammar
2. **Syntax Analysis**: Builds AST from tokens
3. **Error Handling**: Provides detailed error messages with spans
4. **Recovery**: Attempts to recover from syntax errors

## Error Handling

The parser provides detailed error messages with source spans:

```rust
match parse_expression("x +") {
    Ok(expr) => println!("Parsed: {:?}", expr),
    Err(error) => println!("Error: {}", error),
}
```

## Performance

The parser is optimized for:
- **Speed**: Fast parsing of typical Ligature code
- **Memory**: Efficient memory usage
- **Robustness**: Handles edge cases gracefully

## Testing

The parser includes comprehensive testing:

- **Unit Tests**: Test individual parsing functions
- **Integration Tests**: Test complete parsing workflows
- **Property Tests**: Test parser properties with generated inputs
- **Fuzzing Tests**: Test parser robustness with random inputs

## Contributing

When contributing to the parser:

1. Add tests for new functionality
2. Ensure all fuzzing tests pass
3. Update documentation
4. Follow the existing code style

## License

This crate is part of the Ligature project and is licensed under the Apache 2.0 License. 