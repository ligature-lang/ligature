# Ligature Parser Fuzzing

This directory contains comprehensive fuzzing infrastructure for the Ligature parser to improve robustness, catch edge cases, and ensure the parser handles all possible inputs gracefully.

## Overview

The fuzzing infrastructure includes:

- **Grammar-based fuzzing**: Generates structured inputs based on the Ligature grammar
- **Mutation-based fuzzing**: Mutates existing inputs to find edge cases
- **Coverage-guided fuzzing**: Uses AFL-style techniques to maximize code coverage
- **Property-based testing**: Uses proptest to verify parser properties
- **Error recovery testing**: Tests parser's ability to handle and recover from errors

## Quick Start

### Prerequisites

Install cargo-fuzz:
```bash
cargo install cargo-fuzz
```

### Running Fuzzers

1. **Basic parser fuzzing**:
```bash
cd crates/ligature-parser/fuzz
cargo fuzz run parser_fuzz
```

2. **Expression-specific fuzzing**:
```bash
cargo fuzz run expression_fuzz
```

3. **Program fuzzing**:
```bash
cargo fuzz run program_fuzz
```

4. **Mutation-based fuzzing**:
```bash
cargo fuzz run mutation_fuzz
```

5. **Grammar-based fuzzing**:
```bash
cargo fuzz run grammar_fuzz
```

### Running Property Tests

```bash
cd crates/ligature-parser
cargo test --features fuzzing property_tests
```

## Fuzzing Targets

### 1. parser_fuzz
Basic robustness testing - ensures the parser doesn't crash on any input.

### 2. expression_fuzz
Tests expression parsing specifically, including performance bounds.

### 3. program_fuzz
Tests program parsing with size limits and error validation.

### 4. mutation_fuzz
Uses mutation strategies to generate varied inputs from a corpus.

### 5. grammar_fuzz
Generates structured inputs based on the Ligature grammar.

## Configuration

### Timeouts
Fuzzers are configured with reasonable timeouts (1 second) to prevent hangs.

### Memory Limits
Memory usage is monitored to prevent OOM conditions.

### Corpus Management
The mutation fuzzer maintains a corpus of interesting inputs that can be saved and reused.

## Advanced Usage

### Custom Corpus
```bash
# Create a corpus directory
mkdir corpus/parser_fuzz

# Add seed inputs
echo "42" > corpus/parser_fuzz/seed1
echo "x + y" > corpus/parser_fuzz/seed2

# Run with corpus
cargo fuzz run parser_fuzz -- corpus/parser_fuzz/
```

### AFL Integration
```bash
# Build AFL instrumented version
cargo fuzz build parser_fuzz

# Run with AFL
afl-fuzz -i input/ -o output/ -- target/debug/parser_fuzz
```

### Custom Configuration
```bash
# Run with specific parameters
cargo fuzz run parser_fuzz -- -max_len=1000 -timeout=30 -max_total_time=300
```

## Fuzzing Infrastructure

### GrammarFuzzer
Generates structured inputs based on the Ligature grammar:
- Expression generation
- Program generation
- Type generation
- Depth and length limits

### MutationFuzzer
Mutates existing inputs using various strategies:
- Insertion mutations
- Deletion mutations
- Replacement mutations
- Duplication mutations
- Truncation mutations

### CoverageTracker
Tracks code coverage for AFL-style fuzzing:
- Edge coverage
- Coverage percentage
- Coverage statistics

### PerformanceFuzzer
Tests parser performance bounds:
- Timeout detection
- Memory usage monitoring
- Performance regression detection

### ErrorRecoveryFuzzer
Tests parser error handling:
- Error pattern detection
- Recovery strategy testing
- Error message validation

## Property-Based Testing

The property tests verify:

1. **Robustness**: Parser handles all inputs without crashing
2. **Performance**: Parser completes within reasonable time bounds
3. **Memory**: Parser doesn't leak memory or cause OOM
4. **Grammar**: Grammar fuzzer generates reasonable inputs
5. **Mutation**: Mutation fuzzer generates varied inputs

## CI Integration

Fuzzing can be integrated into CI/CD pipelines:

```yaml
# .github/workflows/fuzzing.yml
name: Fuzzing
on: [push, pull_request]

jobs:
  fuzzing:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: nightly
      - run: cargo install cargo-fuzz
      - run: |
          cd crates/ligature-parser/fuzz
          cargo fuzz run parser_fuzz -- -max_total_time=300
```

## Troubleshooting

### Common Issues

1. **Fuzzer hangs**: Check timeout settings and input size limits
2. **Memory issues**: Reduce max_length or add memory monitoring
3. **Low coverage**: Add more seed inputs to corpus
4. **False positives**: Review fuzzer findings and adjust assertions

### Debugging

Enable debug output:
```bash
RUST_LOG=debug cargo fuzz run parser_fuzz
```

### Performance Tuning

- Adjust `max_depth` and `max_length` in GrammarFuzzer
- Modify mutation strategy weights
- Tune timeout and memory limits

## Contributing

When adding new fuzzing targets:

1. Add the target to `fuzz/Cargo.toml`
2. Create the target file in `fuzz/fuzz_targets/`
3. Add appropriate tests
4. Update this README

## References

- [LibFuzzer Documentation](https://llvm.org/docs/LibFuzzer.html)
- [AFL Fuzzer](https://github.com/google/AFL)
- [Rust Fuzzing Book](https://rust-fuzz.github.io/book/)
- [Proptest Documentation](https://altsysrq.github.io/proptest-book/) 