# Baton - Formal Verification CLI

Baton is a command-line tool for formal verification using the Lean theorem prover. It provides a comprehensive interface for verifying Ligature language semantics, type safety, and operational properties.

## Features

- **Expression Evaluation Verification**: Verify that expressions evaluate to expected values
- **Type Checking Verification**: Verify type checking behavior
- **Differential Testing**: Compare Rust and Lean implementations
- **Type Safety Verification**: Verify type safety properties
- **Termination Verification**: Verify program termination
- **Determinism Verification**: Verify deterministic behavior
- **Specification Management**: Build and validate Lean specifications
- **Test Case Extraction**: Extract test cases from specifications
- **Performance Monitoring**: Track verification performance metrics

## Installation

Baton is part of the Ligature workspace. To build it:

```bash
cargo build --package baton
```

## Usage

### Basic Commands

```bash
# Check if Lean is available
baton ping

# Get Lean version
baton version

# Build specification
baton build
```

### Verification Commands

```bash
# Verify expression evaluation
baton verify-evaluation "1 + 2" "3"

# Verify type checking
baton verify-type-check "x: Int" "Int"

# Run differential test
baton differential-test "test_case" "evaluation"

# Verify type safety
baton verify-type-safety "expression"

# Verify termination
baton verify-termination "expression"

# Verify determinism
baton verify-determinism "expression"
```

### Specification Management

```bash
# List specification files
baton list-files

# Check specification compilation
baton check-spec

# Extract test cases
baton extract-tests "specification.lean"
```

### Batch Verification

```bash
# Run verification suite
baton verify-suite "expr1,expr2,expr3"
```

## Architecture

Baton is built on a modular architecture with the following components:

- **baton-core**: Core types and traits
- **baton-error**: Error handling and types
- **baton-protocol**: Request/response protocol
- **baton-client**: Lean client communication
- **baton-specification**: Specification management
- **baton-verification**: Verification engine

## Configuration

Baton uses configuration files to customize behavior. Key configuration options include:

- Lean executable path
- Specification directory
- Timeout settings
- Retry configuration
- Cache settings
- Performance monitoring

## Examples

### Basic Verification

```bash
# Verify a simple arithmetic expression
baton verify-evaluation "2 * 3" "6"

# Verify type checking
baton verify-type-check "x: String" "String"
```

### Differential Testing

```bash
# Compare Rust and Lean evaluation
baton differential-test "1 + 2 * 3" "evaluation"

# Compare type checking
baton differential-test "x: Int" "typecheck"
```

### Specification Workflow

```bash
# Build and validate specification
baton build
baton check-spec

# Extract and run tests
baton extract-tests "main.lean"
baton verify-suite "test1,test2,test3"
```

## Error Handling

Baton provides comprehensive error handling with:

- Detailed error messages
- Error context information
- Retry logic for transient failures
- Graceful degradation when Lean is unavailable

## Performance

Baton includes performance monitoring features:

- Execution time tracking
- Cache hit rates
- Operation-specific metrics
- Memory usage monitoring

## Contributing

To contribute to Baton:

1. Follow the project's coding standards
2. Add tests for new features
3. Update documentation
4. Ensure all tests pass

## License

Baton is licensed under the Apache 2.0 License.
