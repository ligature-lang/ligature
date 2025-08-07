# Ligature Language Testing Infrastructure

This directory contains a comprehensive testing infrastructure for the Ligature language implementation. The testing framework is designed to ensure correctness, reliability, and compliance with the formal specification.

## Overview

The testing infrastructure consists of three main categories:

1. **Integration Tests** - Test the complete pipeline from parsing through evaluation
2. **Property-Based Tests** - Use randomly generated inputs to verify language properties
3. **Differential Tests** - Compare Rust implementation against the Lean specification

## Directory Structure

```
tests/
├── integration/           # Integration tests
│   ├── mod.rs            # Main integration test module
│   ├── parser_tests.rs   # Parser-specific tests
│   ├── eval_tests.rs     # Evaluation-specific tests
│   ├── type_tests.rs     # Type system tests
│   ├── end_to_end_tests.rs # Complete pipeline tests
│   ├── error_handling_tests.rs # Error handling tests
│   ├── test_parser.rs    # Simple parser test script (moved from root)
│   ├── test_simple.rs    # Simple test script (moved from root)
│   └── test_parse.rs     # Parse test script (moved from root)
├── fixtures/             # Test fixtures and sample files
│   ├── test_simple.lig   # Simple Ligature test file (moved from root)
│   └── test_let.lig      # Let expression test file (moved from root)
├── property/             # Property-based tests
│   ├── mod.rs            # Main property test module
│   ├── parser_properties.rs # Parser property tests
│   ├── eval_properties.rs # Evaluation property tests
│   ├── type_properties.rs # Type system property tests
│   └── roundtrip_properties.rs # Roundtrip property tests
├── differential/         # Differential tests against Lean spec
│   ├── mod.rs            # Main differential test module
│   ├── spec_compliance_tests.rs # Specification compliance tests
│   ├── operational_semantics_tests.rs # Operational semantics tests
│   ├── type_system_tests.rs # Type system differential tests
│   └── configuration_tests.rs # Configuration language tests
├── run_tests.rs          # Test runner and reporting
└── README.md             # This file
```

## Running Tests

### Running All Tests

```bash
# Run all tests (without Lean integration)
cargo test

# Run all tests with Lean integration enabled
cargo test --features lean-integration

# Run tests with output
cargo test -- --nocapture

# Run tests with Lean integration and output
cargo test --features lean-integration -- --nocapture

# Run specific test categories
cargo test integration
cargo test property
cargo test differential

# Run differential tests with Lean integration
cargo test differential --features lean-integration
```

### Running Specific Test Suites

```bash
# Run only integration tests
cargo test --test integration

# Run only property tests
cargo test --test property

# Run only differential tests
cargo test --test differential
```

### Running Individual Tests

```bash
# Run a specific test
cargo test test_parse_literals

# Run tests matching a pattern
cargo test parse

# Run tests with verbose output
cargo test -- --nocapture --test-threads=1
```

## Test Categories

### Integration Tests

Integration tests verify that the different components of the language work together correctly. They test the complete pipeline from parsing through type checking to evaluation.

**Key Features:**

- Complete pipeline testing
- Error handling verification
- End-to-end functionality testing
- Real-world usage scenarios

**Test Coverage:**

- Parser functionality (literals, expressions, programs)
- Evaluation engine (arithmetic, logical, conditional operations)
- Type system (type checking, inference, error handling)
- Error handling (syntax errors, type errors, runtime errors)
- End-to-end scenarios (configuration examples, complex expressions)

### Property-Based Tests

Property-based tests use randomly generated inputs to verify that the language satisfies various properties and invariants. These tests help catch edge cases and ensure robustness.

**Key Features:**

- Random input generation
- Property verification
- Invariant testing
- Edge case discovery

**Test Coverage:**

- Parser properties (idempotency, whitespace invariance, error consistency)
- Evaluation properties (termination, arithmetic properties, logical properties)
- Type system properties (type inference correctness, error handling)
- Roundtrip properties (parse → evaluate → parse consistency)

### Differential Tests

Differential tests compare the Rust implementation against the formal specification written in Lean. This ensures that the implementation correctly follows the formal semantics.

**Key Features:**

- Specification compliance verification
- Formal semantics testing
- Enhanced comparison logic with detailed error reporting
- Mathematical correctness validation
- **Optional Lean Integration**: Available via the `lean-integration` feature flag

**Test Coverage:**

- Specification compliance (literals, operations, expressions)
- Operational semantics (evaluation rules, type rules)
- Type system compliance (type checking, inference)
- Configuration language compliance

**🔧 Feature Flag System:**
The Lean integration is now behind the `lean-integration` feature flag:

```bash
# Run without Lean integration (faster builds)
cargo test

# Run with Lean integration enabled
cargo test --features lean-integration

# Run examples with Lean integration
cargo run --example working_lean_test --features lean-integration
```

**⚠️ Current Implementation Status:**
The differential testing framework includes several stubs and placeholder implementations:

1. **Legacy Function Stubs**: The following functions are currently stubs that return placeholder results:

   - `run_type_check_differential_test()` - Always returns `Ok(true)`
   - `run_operational_semantics_test()` - Always returns `Ok(true)`
   - `run_configuration_test()` - Always returns `Ok(true)`

2. **Lean Integration Placeholders**: The actual Lean process communication is not yet implemented:

   - `run_lean_evaluation()` - Returns placeholder results
   - `run_lean_type_checking()` - Returns placeholder results
   - `run_lean_operational_semantics()` - Returns placeholder results

3. **Enhanced Framework Ready**: The enhanced comparison logic and error reporting infrastructure is complete and ready for integration with the actual Lean specification.

**Next Steps:**

- Implement actual Lean process communication
- Replace stub functions with real Lean integration
- Add comprehensive test cases from the Lean specification

## Test Dependencies

The testing infrastructure uses several Rust crates:

```toml
[dependencies]
proptest = "1.3"           # Property-based testing
criterion = "0.5"          # Benchmarking
test-case = "3.3"          # Parameterized tests
rstest = "0.18"            # Test fixtures
mockall = "0.12"           # Mocking
fake = "2.9"               # Fake data generation
```

## Writing Tests

### Adding Integration Tests

1. Create a new test file in the appropriate subdirectory
2. Import the necessary modules
3. Write test functions with the `#[test]` attribute
4. Use helper functions from the test modules

Example:

```rust
use ligature_parser::parse_expression;
use ligature_ast::AstResult;

#[test]
fn test_my_new_feature() -> AstResult<()> {
    let expr = parse_expression("my_new_syntax")?;
    // Add assertions
    Ok(())
}
```

### Adding Property-Based Tests

1. Use the `proptest!` macro
2. Define input strategies
3. Write property verification logic

Example:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_property(expr in expr_strategy()) {
        // Property verification logic
        assert!(some_property_holds(expr));
    }
}
```

### Adding Differential Tests

1. Use the helper functions from the differential module
2. Write tests that compare Rust and Lean results
3. Ensure specification compliance

Example:

```rust
use crate::differential::run_differential_test;

#[test]
fn test_spec_compliance() {
    let result = run_differential_test("test_expression");
    assert!(result.is_ok());
    assert!(result.unwrap());
}
```

## Test Utilities

### Helper Functions

The test modules provide various helper functions:

- `parse_type_check_and_evaluate()` - Complete pipeline execution
- `create_test_environment()` - Standard test environment setup
- `is_well_formed()` - Check if expression parses correctly
- `type_checks()` - Check if expression type checks
- `evaluates_successfully()` - Check if expression evaluates

### Test Strategies

Property-based tests use strategies for generating test inputs:

- `integer_expr_strategy()` - Generate integer expressions
- `string_expr_strategy()` - Generate string expressions
- `boolean_expr_strategy()` - Generate boolean expressions
- `arithmetic_expr_strategy()` - Generate arithmetic expressions
- `expr_strategy()` - Generate general expressions

## Continuous Integration

The testing infrastructure is designed to work with CI/CD pipelines:

1. **Fast Feedback** - Unit tests run quickly for immediate feedback
2. **Comprehensive Coverage** - Integration tests ensure complete functionality
3. **Property Verification** - Property tests catch edge cases and regressions
4. **Specification Compliance** - Differential tests ensure formal correctness

## Future Enhancements

### Planned Features

1. **Lean Integration** - Direct integration with Lean specification
2. **Performance Testing** - Benchmarking and performance regression tests
3. **Fuzzing** - Advanced fuzzing for security and robustness
4. **Mutation Testing** - Test quality verification
5. **Coverage Reporting** - Code coverage analysis

### Lean Specification Integration

The differential tests currently use placeholder functions for Lean integration. The enhanced framework infrastructure is complete, but the actual Lean integration needs to be implemented:

1. **Lean Process Communication** - Direct communication with Lean processes (stub functions in place)
2. **Specification Extraction** - Automatic test case extraction from Lean files (framework ready)
3. **Result Comparison** - Sophisticated comparison of Rust and Lean results (✅ implemented)
4. **Specification Validation** - Verification against formal semantics (framework ready)

**Current Status:**

- ✅ Enhanced comparison logic and error reporting implemented
- ✅ Detailed difference analysis with severity levels
- ✅ Comprehensive test result structures
- 🔄 Lean process communication (stubs in place, ready for implementation)
- 🔄 Specification test case extraction (framework ready)

## Contributing

When adding new language features:

1. **Add Integration Tests** - Test the complete functionality
2. **Add Property Tests** - Verify important properties
3. **Add Differential Tests** - Ensure specification compliance
4. **Update Documentation** - Document new test cases

### Test Guidelines

1. **Test Names** - Use descriptive test names that explain what is being tested
2. **Test Organization** - Group related tests together
3. **Error Testing** - Always test error conditions and edge cases
4. **Property Testing** - Use property-based tests for complex behaviors
5. **Documentation** - Document complex test logic and assumptions

## Troubleshooting

### Common Issues

1. **Test Failures** - Check that the language implementation matches the test expectations
2. **Property Test Failures** - Property tests may reveal bugs in the implementation
3. **Differential Test Failures** - May indicate divergence from the specification
4. **Performance Issues** - Property tests can be slow; adjust strategy parameters

### Debugging

1. **Verbose Output** - Use `--nocapture` to see test output
2. **Single Thread** - Use `--test-threads=1` for deterministic behavior
3. **Specific Tests** - Run individual tests to isolate issues
4. **Property Test Shrinking** - Property tests automatically shrink failing cases

## Metrics and Reporting

The test runner provides comprehensive reporting:

- **Test Counts** - Total, passed, and failed tests
- **Success Rates** - Percentage of passing tests
- **Duration** - Test execution time
- **Coverage** - Test coverage information (planned)

## Moved Test Files

### Recent Reorganization

The following test files were moved from the project root to the `tests/` directory to improve organization:

#### Moved to `tests/integration/`:

- `test_parser.rs` - Simple parser test script
- `test_simple.rs` - Basic functionality test script
- `test_parse.rs` - Parse expression test script

#### Moved to `tests/fixtures/`:

- `test_simple.lig` - Simple Ligature expression file
- `test_let.lig` - Let expression test file

### References Updated

The following files were updated to reflect the new locations:

- `examples/Cargo.toml` - Updated path for `test_parser` example
- `docs/README.md` - Added note about moved `test_simple.lig` file

### Benefits

This reorganization provides:

- **Better Organization** - All tests are now in a dedicated directory
- **Clearer Structure** - Test files are categorized by type and purpose
- **Easier Maintenance** - Related test files are grouped together
- **Cleaner Root** - Project root is no longer cluttered with test files

## Conclusion

This testing infrastructure provides comprehensive verification of the Ligature language implementation. It ensures correctness, reliability, and compliance with the formal specification while providing fast feedback for development.
