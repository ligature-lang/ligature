# Property-Based Testing Proposal

## Overview

This proposal outlines a comprehensive approach to adding property-based testing to Ligature using the `proptest` crate. Property-based testing will help ensure correctness, catch edge cases, and improve the robustness of the language implementation by generating random test cases and verifying that properties hold across a wide range of inputs.

## Problem Statement

### Current Testing Limitations

Ligature's current testing approach has several limitations:

1. **Limited Test Coverage**: Manual test cases only cover known scenarios
2. **Missing Edge Cases**: Unusual inputs and boundary conditions may not be tested
3. **Brittle Tests**: Tests may break when implementation details change
4. **Incomplete Validation**: Properties that should always hold are not systematically verified
5. **Manual Test Generation**: Creating comprehensive test suites is time-consuming

### Areas Needing Property-Based Testing

1. **Parser Robustness**: Ensure parser handles all valid and invalid inputs correctly
2. **Type System Properties**: Verify type inference and checking properties
3. **Evaluation Correctness**: Ensure evaluation preserves semantic properties
4. **Optimization Correctness**: Verify that optimizations don't change semantics
5. **Error Handling**: Ensure errors are consistent and informative

## Design Philosophy

### Core Principles

1. **Property-First**: Focus on properties that should always hold
2. **Comprehensive Coverage**: Generate tests across the full input space
3. **Shrinking**: Automatically find minimal failing test cases
4. **Deterministic**: Tests should be reproducible and deterministic
5. **Performance Conscious**: Tests should run quickly and efficiently

### Property Categories

1. **Invariants**: Properties that should always hold
2. **Equivalences**: Different expressions that should produce the same result
3. **Commutativity**: Operations that should be order-independent
4. **Associativity**: Operations that should be grouping-independent
5. **Idempotence**: Operations that should be repeatable without change

## Proposed Solution

### 1. Parser Properties

#### Grammar Invariants

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_parser_idempotence(input in expression_strategy()) {
        // Parsing and then pretty-printing should produce equivalent code
        let parsed = parse_expression(&input);
        if let Ok(ast) = parsed {
            let printed = pretty_print(&ast);
            let reparsed = parse_expression(&printed);

            assert!(reparsed.is_ok());
            assert_eq!(ast, reparsed.unwrap());
        }
    }

    #[test]
    fn test_parser_preserves_structure(input in expression_strategy()) {
        // Parsing should preserve the structure of valid expressions
        let parsed = parse_expression(&input);
        if let Ok(ast) = parsed {
            // Verify that the AST structure matches the input structure
            assert!(ast_structure_matches_input(&ast, &input));
        }
    }

    #[test]
    fn test_parser_error_consistency(input in arbitrary_string()) {
        // Invalid inputs should always produce parse errors
        let parsed = parse_expression(&input);
        if parsed.is_err() {
            // Verify error is consistent and informative
            let error = parsed.unwrap_err();
            assert!(!error.to_string().is_empty());
            assert!(error.span().is_valid());
        }
    }
}

// Strategy for generating expressions
fn expression_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "42".to_string(),
        "\"hello\"".to_string(),
        "true".to_string(),
        "false".to_string(),
        "()".to_string(),
        "x".to_string(),
        "x + y".to_string(),
        "f x".to_string(),
        "\\x -> x".to_string(),
        "let x = 42 in x".to_string(),
        "if true then 1 else 2".to_string(),
        "{ x = 1, y = 2 }".to_string(),
        "[1, 2, 3]".to_string(),
    ])
}
```

#### Operator Precedence Properties

```rust
proptest! {
    #[test]
    fn test_operator_precedence(a in any::<i64>(), b in any::<i64>(), c in any::<i64>()) {
        // Test that operator precedence is correctly implemented
        let expressions = vec![
            format!("{} + {} * {}", a, b, c),
            format!("{} * {} + {}", a, b, c),
            format!("({} + {}) * {}", a, b, c),
            format!("{} * ({} + {})", a, b, c),
        ];

        for expr in expressions {
            let parsed = parse_expression(&expr);
            assert!(parsed.is_ok(), "Failed to parse: {}", expr);
        }
    }

    #[test]
    fn test_associativity(a in any::<i64>(), b in any::<i64>(), c in any::<i64>()) {
        // Test that addition and multiplication are associative
        let left_assoc = format!("({} + {}) + {}", a, b, c);
        let right_assoc = format!("{} + ({} + {})", a, b, c);

        let left_parsed = parse_expression(&left_assoc);
        let right_parsed = parse_expression(&right_assoc);

        assert!(left_parsed.is_ok());
        assert!(right_parsed.is_ok());

        // Both should evaluate to the same result
        let left_result = evaluate_expression(&left_parsed.unwrap());
        let right_result = evaluate_expression(&right_parsed.unwrap());

        assert_eq!(left_result, right_result);
    }
}
```

### 2. Type System Properties

#### Type Inference Properties

```rust
proptest! {
    #[test]
    fn test_type_inference_consistency(expr in typed_expression_strategy()) {
        // Type inference should be consistent and deterministic
        let (expression, expected_type) = expr;

        let inferred_type = infer_expression_type(&expression);
        assert!(inferred_type.is_ok());

        let inferred = inferred_type.unwrap();
        assert!(types_compatible(&inferred, &expected_type));
    }

    #[test]
    fn test_type_inference_idempotence(expr in expression_strategy()) {
        // Running type inference multiple times should produce the same result
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let type1 = infer_expression_type(&ast);
            let type2 = infer_expression_type(&ast);

            assert_eq!(type1, type2);
        }
    }

    #[test]
    fn test_subtyping_properties(a in type_strategy(), b in type_strategy(), c in type_strategy()) {
        // Test subtyping properties: reflexivity, transitivity, etc.

        // Reflexivity: A <: A
        assert!(is_subtype(&a, &a));

        // Transitivity: if A <: B and B <: C, then A <: C
        if is_subtype(&a, &b) && is_subtype(&b, &c) {
            assert!(is_subtype(&a, &c));
        }
    }
}

// Strategy for generating typed expressions
fn typed_expression_strategy() -> impl Strategy<Value = (Expr, Type)> {
    prop::sample::select(vec![
        (Expr::Literal(Literal::Integer(42)), Type::Integer),
        (Expr::Literal(Literal::String("hello".to_string())), Type::String),
        (Expr::Literal(Literal::Boolean(true)), Type::Boolean),
        // Add more typed expressions
    ])
}

// Strategy for generating types
fn type_strategy() -> impl Strategy<Value = Type> {
    prop::sample::select(vec![
        Type::Integer,
        Type::String,
        Type::Boolean,
        Type::Unit,
        // Add more types
    ])
}
```

#### Type Checking Properties

```rust
proptest! {
    #[test]
    fn test_type_checking_soundness(expr in expression_strategy()) {
        // If type checking passes, evaluation should not fail with type errors
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let type_check = type_check_expression(&ast);

            if type_check.is_ok() {
                // Type checking passed, so evaluation should not fail with type errors
                let evaluation = evaluate_expression(&ast);
                if evaluation.is_err() {
                    let error = evaluation.unwrap_err();
                    assert!(!is_type_error(&error),
                        "Type-checked expression failed with type error: {:?}", error);
                }
            }
        }
    }

    #[test]
    fn test_type_checking_completeness(expr in expression_strategy()) {
        // If evaluation succeeds, type checking should pass
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let evaluation = evaluate_expression(&ast);

            if evaluation.is_ok() {
                // Evaluation succeeded, so type checking should pass
                let type_check = type_check_expression(&ast);
                assert!(type_check.is_ok(),
                    "Successfully evaluated expression failed type checking");
            }
        }
    }
}
```

### 3. Evaluation Properties

#### Semantic Properties

```rust
proptest! {
    #[test]
    fn test_evaluation_determinism(expr in expression_strategy()) {
        // Evaluation should be deterministic
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let result1 = evaluate_expression(&ast);
            let result2 = evaluate_expression(&ast);

            assert_eq!(result1, result2);
        }
    }

    #[test]
    fn test_evaluation_termination(expr in expression_strategy()) {
        // All evaluations should terminate (due to totality)
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let result = evaluate_expression(&ast);
            // If we get here, evaluation terminated
            assert!(result.is_ok() || result.is_err());
        }
    }

    #[test]
    fn test_arithmetic_properties(a in any::<i64>(), b in any::<i64>()) {
        // Test arithmetic properties
        let add_expr = format!("{} + {}", a, b);
        let parsed = parse_expression(&add_expr);
        if let Ok(ast) = parsed {
            let result = evaluate_expression(&ast);
            assert!(result.is_ok());

            // Commutativity: a + b = b + a
            let comm_expr = format!("{} + {}", b, a);
            let comm_parsed = parse_expression(&comm_expr);
            if let Ok(comm_ast) = comm_parsed {
                let comm_result = evaluate_expression(&comm_ast);
                assert_eq!(result, comm_result);
            }
        }
    }

    #[test]
    fn test_function_properties(f in function_strategy(), x in value_strategy()) {
        // Test function application properties
        let app_expr = format!("({}) {}", f, x);
        let parsed = parse_expression(&app_expr);
        if let Ok(ast) = parsed {
            let result = evaluate_expression(&ast);

            // Function application should always produce a value or error
            assert!(result.is_ok() || result.is_err());
        }
    }
}

// Strategy for generating functions
fn function_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "\\x -> x".to_string(),
        "\\x -> x + 1".to_string(),
        "\\x -> x * 2".to_string(),
        "\\x -> if x > 0 then x else -x".to_string(),
    ])
}

// Strategy for generating values
fn value_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "42".to_string(),
        "0".to_string(),
        "-1".to_string(),
        "100".to_string(),
    ])
}
```

### 4. Optimization Properties

#### Optimization Correctness

```rust
proptest! {
    #[test]
    fn test_optimization_preserves_semantics(expr in expression_strategy()) {
        // Optimizations should preserve semantics
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let original_result = evaluate_expression(&ast);

            let optimized = optimize_expression(&ast);
            let optimized_result = evaluate_expression(&optimized);

            assert_eq!(original_result, optimized_result);
        }
    }

    #[test]
    fn test_optimization_idempotence(expr in expression_strategy()) {
        // Applying optimization multiple times should be idempotent
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let optimized1 = optimize_expression(&ast);
            let optimized2 = optimize_expression(&optimized1);

            assert_eq!(optimized1, optimized2);
        }
    }

    #[test]
    fn test_constant_folding(a in any::<i64>(), b in any::<i64>()) {
        // Test constant folding optimizations
        let expr = format!("{} + {}", a, b);
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let optimized = optimize_expression(&ast);

            // Constant expressions should be folded to literals
            if is_constant_expression(&ast) {
                assert!(is_literal(&optimized));
            }
        }
    }
}
```

### 5. Error Handling Properties

#### Error Consistency

```rust
proptest! {
    #[test]
    fn test_error_consistency(expr in expression_strategy()) {
        // Errors should be consistent and informative
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let type_check = type_check_expression(&ast);
            let evaluation = evaluate_expression(&ast);

            // If type checking fails, evaluation should also fail
            if type_check.is_err() {
                assert!(evaluation.is_err());
            }
        }
    }

    #[test]
    fn test_error_messages(expr in expression_strategy()) {
        // Error messages should be non-empty and contain useful information
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let type_check = type_check_expression(&ast);

            if let Err(error) = type_check {
                let message = error.to_string();
                assert!(!message.is_empty());
                assert!(message.len() > 10); // Should be reasonably detailed
            }
        }
    }

    #[test]
    fn test_error_locations(expr in expression_strategy()) {
        // Errors should have valid source locations
        let parsed = parse_expression(&expr);
        if let Ok(ast) = parsed {
            let type_check = type_check_expression(&ast);

            if let Err(error) = type_check {
                let span = error.span();
                assert!(span.is_valid());
                assert!(span.start <= span.end);
            }
        }
    }
}
```

## Implementation Strategy

### Phase 1: Basic Property Tests (Immediate - 2-3 weeks)

#### Goals

- Add proptest dependency
- Implement basic expression generation strategies
- Add fundamental property tests

#### Implementation Tasks

1. **Add Dependencies**

```toml
[dependencies]
proptest = "1.3"
```

2. **Basic Expression Strategies**

```rust
pub mod strategies {
    use proptest::prelude::*;

    pub fn expression_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "42".to_string(),
            "\"hello\"".to_string(),
            "true".to_string(),
            "x + y".to_string(),
            "f x".to_string(),
        ])
    }

    pub fn value_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "42".to_string(),
            "0".to_string(),
            "-1".to_string(),
        ])
    }
}
```

3. **Basic Property Tests**

```rust
#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_parser_idempotence(input in expression_strategy()) {
            // Basic parser property test
        }

        #[test]
        fn test_evaluation_determinism(expr in expression_strategy()) {
            // Basic evaluation property test
        }
    }
}
```

### Phase 2: Advanced Strategies (Short-term - 4-6 weeks)

#### Goals

- Implement complex expression generation strategies
- Add type-aware strategies
- Implement shrinking for better error reporting

#### Implementation Tasks

1. **Complex Expression Strategies**

```rust
pub fn complex_expression_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "let x = 42 in x + 1".to_string(),
        "if true then 1 else 2".to_string(),
        "{ x = 1, y = 2 }".to_string(),
        "[1, 2, 3]".to_string(),
        "\\x -> x + 1".to_string(),
    ])
}

pub fn typed_expression_strategy() -> impl Strategy<Value = (Expr, Type)> {
    // Generate expressions with known types
}
```

2. **Shrinking Implementation**

```rust
impl Arbitrary for Expr {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        expression_strategy()
            .prop_map(|s| parse_expression(&s).unwrap())
            .boxed()
    }
}
```

### Phase 3: Comprehensive Properties (Medium-term - 6-8 weeks)

#### Goals

- Add comprehensive property tests for all language features
- Implement performance property tests
- Add regression property tests

#### Implementation Tasks

1. **Language Feature Properties**

```rust
proptest! {
    #[test]
    fn test_pattern_matching_properties(expr in pattern_expression_strategy()) {
        // Test pattern matching properties
    }

    #[test]
    fn test_type_class_properties(expr in type_class_expression_strategy()) {
        // Test type class properties
    }

    #[test]
    fn test_module_properties(expr in module_expression_strategy()) {
        // Test module system properties
    }
}
```

2. **Performance Properties**

```rust
proptest! {
    #[test]
    fn test_evaluation_performance(expr in large_expression_strategy()) {
        // Test that evaluation completes within reasonable time
        let start = std::time::Instant::now();
        let result = evaluate_expression(&expr);
        let duration = start.elapsed();

        assert!(duration < Duration::from_secs(1));
        assert!(result.is_ok() || result.is_err());
    }
}
```

### Phase 4: Regression Testing (Long-term - 8-12 weeks)

#### Goals

- Implement regression property tests
- Add property-based fuzzing
- Implement continuous property testing

#### Implementation Tasks

1. **Regression Property Tests**

```rust
proptest! {
    #[test]
    fn test_regression_properties(expr in regression_expression_strategy()) {
        // Test properties that have been broken in the past
        // These help prevent regressions
    }
}
```

2. **Property-Based Fuzzing**

```rust
pub struct PropertyFuzzer {
    strategies: Vec<BoxedStrategy<Expr>>,
    properties: Vec<Box<dyn Fn(&Expr) -> bool>>,
}

impl PropertyFuzzer {
    pub fn fuzz(&self) -> Vec<Expr> {
        // Generate expressions and test properties
    }
}
```

## Configuration and Usage

### Basic Usage

```rust
// Run property tests
cargo test property_tests

// Run with specific seed
PROPTEST_REGENERATE=1 cargo test test_parser_idempotence

// Run with custom configuration
#[proptest]
fn test_with_config(#[strategy(expression_strategy())] expr: String) {
    // Test implementation
}
```

### Advanced Usage

```rust
// Custom test configuration
proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn test_comprehensive_properties(expr in complex_expression_strategy()) {
        // Comprehensive property test
    }
}

// Property test with shrinking
proptest! {
    #[test]
    fn test_with_shrinking(#[strategy(expression_strategy())] expr: String) {
        // Test that will shrink on failure
    }
}
```

### CI Integration

```yaml
# .github/workflows/property-tests.yml
name: Property Tests
on: [push, pull_request]

jobs:
  property-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
      - run: cargo test property_tests --release
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_expression_strategy() {
    let strategy = expression_strategy();
    let mut runner = proptest::test_runner::TestRunner::default();

    for _ in 0..100 {
        let expr = strategy.new_tree(&mut runner).unwrap();
        assert!(!expr.current().is_empty());
    }
}
```

### Integration Tests

```rust
#[test]
fn test_property_integration() {
    // Test that properties work with the full language implementation
    proptest!(|(expr in expression_strategy())| {
        let result = parse_and_evaluate(&expr);
        assert!(result.is_ok() || result.is_err());
    });
}
```

### Performance Tests

```rust
#[test]
fn test_property_performance() {
    let start = std::time::Instant::now();

    proptest!(|(expr in expression_strategy())| {
        let _ = parse_expression(&expr);
    });

    let duration = start.elapsed();
    assert!(duration < Duration::from_secs(30));
}
```

## Migration Strategy

### Backward Compatibility

1. **Optional Feature**: Property tests are additive and don't affect existing tests
2. **Gradual Adoption**: Can be enabled/disabled via feature flags
3. **Performance Impact**: Property tests run in separate test suite
4. **CI Integration**: Can be run in parallel with existing tests

### Migration Path

1. **Phase 1**: Add basic property tests alongside existing tests
2. **Phase 2**: Expand property test coverage
3. **Phase 3**: Replace some manual tests with property tests
4. **Phase 4**: Comprehensive property-based testing

### Migration Examples

```rust
// Before: Manual test cases
#[test]
fn test_addition() {
    assert_eq!(evaluate("1 + 2"), Ok(Value::Integer(3)));
    assert_eq!(evaluate("0 + 0"), Ok(Value::Integer(0)));
    assert_eq!(evaluate("-1 + 1"), Ok(Value::Integer(0)));
}

// After: Property-based test
proptest! {
    #[test]
    fn test_addition_properties(a in any::<i64>(), b in any::<i64>()) {
        let expr = format!("{} + {}", a, b);
        let result = evaluate(&expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Value::Integer(a + b));
    }
}
```

## Risks and Mitigations

### 1. Performance Impact

**Risk**: Property tests may slow down the test suite
**Mitigation**:

- Run property tests in separate CI job
- Use reasonable test case limits
- Optimize test strategies for speed
- Parallel test execution

### 2. Flaky Tests

**Risk**: Property tests may be non-deterministic
**Mitigation**:

- Use deterministic random number generators
- Set fixed seeds for CI
- Implement proper test isolation
- Clear test state between runs

### 3. Complex Test Generation

**Risk**: Generating valid test cases may be complex
**Mitigation**:

- Start with simple strategies
- Gradually increase complexity
- Use shrinking to debug failures
- Comprehensive documentation

### 4. Maintenance Overhead

**Risk**: Property tests may require significant maintenance
**Mitigation**:

- Clear documentation of properties
- Automated test generation where possible
- Regular review and cleanup
- Integration with existing test infrastructure

## Success Metrics

### Technical Metrics

1. **Test Coverage**: Percentage of code paths covered by property tests
2. **Bug Detection**: Number of bugs found by property tests
3. **Performance**: Time to run property test suite
4. **Reliability**: Reduction in flaky tests

### Quality Metrics

1. **Bug Prevention**: Reduction in regressions
2. **Code Quality**: Improvement in code robustness
3. **Developer Confidence**: Increased confidence in changes
4. **Documentation**: Properties serve as living documentation

## Conclusion

This proposal provides a comprehensive approach to adding property-based testing to Ligature using proptest. The gradual introduction ensures minimal disruption while providing significant benefits for code quality and reliability.

The key benefits include:

1. **Better Test Coverage**: Automatic generation of test cases
2. **Bug Detection**: Finding edge cases and unexpected behaviors
3. **Documentation**: Properties serve as executable specifications
4. **Maintainability**: Tests that adapt to implementation changes
5. **Confidence**: Increased confidence in code correctness

The implementation strategy provides a clear path forward with measurable milestones and comprehensive testing to ensure reliability and effectiveness.

## References

1. [Proptest Documentation](https://altsysrq.github.io/proptest-book/)
2. [Property-Based Testing](https://en.wikipedia.org/wiki/Property-based_testing)
3. [QuickCheck Paper](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf)
4. [Rust Testing Book](https://doc.rust-lang.org/book/ch11-00-testing.html)
5. [Property-Based Testing with Hypothesis](https://hypothesis.readthedocs.io/)
