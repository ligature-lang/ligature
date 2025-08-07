# Relaxed Totality Guarantees Proposal

## Overview

This proposal outlines a strategic approach to relaxing Ligature's totality guarantees to increase expressiveness while maintaining safety through configurable bounds and monitoring. The current strict totality constraints, while providing strong safety guarantees, limit the language's applicability to complex configuration scenarios that require more sophisticated control flow and data processing.

## Problem Statement

### Current Limitations

Ligature's current totality guarantees, while theoretically sound, create several practical limitations:

1. **Limited Expressiveness**: Complex configuration transformations and validations are difficult to express
2. **Restrictive Recursion**: Only structural recursion is allowed, limiting algorithmic flexibility
3. **No Infinite Data**: Cannot represent or process potentially infinite data structures
4. **Configuration Complexity**: Advanced configuration scenarios require workarounds
5. **Developer Experience**: Error messages for termination issues are often unclear

### Use Cases Affected

- **Complex Data Transformation**: Multi-step configuration processing pipelines
- **Dynamic Configuration Generation**: Runtime configuration based on external data
- **Advanced Validation**: Complex validation logic requiring arbitrary recursion
- **Stream Processing**: Processing of potentially infinite data streams
- **Template Generation**: Complex template systems with recursive patterns

## Design Philosophy

### Core Principles

1. **Gradual Safety**: Provide multiple levels of safety guarantees, from strict to relaxed
2. **Configurable Bounds**: Allow users to set resource limits appropriate for their use case
3. **Explicit Opt-in**: Advanced features require explicit annotations
4. **Runtime Monitoring**: Provide runtime feedback on termination and resource usage
5. **Backward Compatibility**: Existing strict totality remains the default
6. **Clear Error Messages**: Rich error reporting with actionable suggestions

### Safety Levels

1. **Strict Totality** (Current): Guaranteed termination with structural recursion
2. **Bounded Totality**: Termination with configurable resource bounds
3. **Monitored Totality**: Runtime monitoring with warnings and timeouts
4. **Unchecked Totality**: No termination guarantees (explicit opt-in)

## Proposed Solution

### 1. Gradual Totality System

#### Syntax Extensions

```ocaml
// Level 1: Strict totality (current behavior)
let rec factorial = \n ->
  if n <= 1 then 1 else n * (factorial (n - 1));

// Level 2: Bounded recursion with explicit limits
let rec bounded_factorial = \n ->
  if n <= 1 then 1
  else if n > 1000 then error "Input too large"
  else n * (bounded_factorial (n - 1))
  where termination = "bounded", limit = 1000;

// Level 3: Monitored recursion with runtime checks
let rec monitored_factorial = \n ->
  if n <= 1 then 1
  else monitored_factorial (n - 1) |> (*) n
  where termination = "monitored";

// Level 4: Unchecked recursion (explicit opt-out)
let rec arbitrary_recursion = \n ->
  if n <= 0 then 0
  else arbitrary_recursion (n - 1) + 1
  where termination = "unchecked";
```

#### Type System Extensions

```ocaml
// Function type with totality annotation
type BoundedFunction a b = {
    function: a -> b,
    termination: TerminationLevel,
    bounds: Option<EvaluationBounds>
}

type TerminationLevel =
    | Strict      // Current behavior
    | Bounded     // Resource-bounded
    | Monitored   // Runtime monitoring
    | Unchecked   // No guarantees

type EvaluationBounds = {
    max_stack_depth: Int,
    max_recursion_depth: Int,
    max_evaluation_steps: Int,
    max_memory_usage: Int,
    timeout: Option<Float>
}
```

### 2. Resource-Bounded Evaluation

#### Evaluation Context

```rust
pub struct EvaluationBounds {
    pub max_stack_depth: usize,
    pub max_recursion_depth: usize,
    pub max_evaluation_steps: usize,
    pub max_memory_usage: usize,
    pub timeout: Option<std::time::Duration>,
}

pub struct TerminationMonitor {
    pub current_stack_depth: usize,
    pub current_recursion_depth: usize,
    pub evaluation_steps: usize,
    pub memory_usage: usize,
    pub start_time: std::time::Instant,
}

pub enum TerminationReason {
    Normal,
    StackLimitReached,
    RecursionLimitReached,
    StepLimitReached,
    MemoryLimitReached,
    Timeout,
}
```

#### Configuration Examples

```ocaml
// Development environment - relaxed bounds
let dev_config = {
    totality = "monitored",
    bounds = {
        max_stack_depth = 10000,
        max_recursion_depth = 1000,
        max_evaluation_steps = 100000,
        max_memory_usage = 100_000_000,  // 100MB
        timeout = Some(30.0)  // 30 seconds
    },
    warnings = {
        non_structural_recursion = "warn",
        resource_usage = "warn",
        termination_guarantees = "warn"
    }
};

// Production environment - strict bounds
let prod_config = {
    totality = "strict",
    bounds = {
        max_stack_depth = 1000,
        max_recursion_depth = 100,
        max_evaluation_steps = 10000,
        max_memory_usage = 10_000_000,  // 10MB
        timeout = Some(1.0)  // 1 second
    },
    warnings = {
        non_structural_recursion = "error",
        resource_usage = "error",
        termination_guarantees = "error"
    }
};

// Research environment - very relaxed bounds
let research_config = {
    totality = "unchecked",
    bounds = {
        max_stack_depth = 100000,
        max_recursion_depth = 10000,
        max_evaluation_steps = 1000000,
        max_memory_usage = 1_000_000_000,  // 1GB
        timeout = Some(300.0)  // 5 minutes
    },
    warnings = {
        non_structural_recursion = "ignore",
        resource_usage = "warn",
        termination_guarantees = "ignore"
    }
};
```

### 3. Lazy Evaluation with Termination Monitoring

#### Lazy Data Structures

```ocaml
// Lazy infinite list
let infinite_ones = lazy [1, 1, 1, ...];

// Lazy stream type
type Stream a = {
    head: a,
    tail: Lazy (Stream a)
};

// Infinite stream of natural numbers
let naturals = {
    head = 0,
    tail = lazy {
        head = 1,
        tail = lazy {
            head = 2,
            tail = lazy naturals  // Circular reference
        }
    }
};

// Safe operations on infinite streams
let take_stream = \n \stream ->
    if n <= 0 then []
    else [stream.head, ...(take_stream (n - 1) (force stream.tail))];

// Force evaluation of lazy value
let force = \lazy_value ->
    match lazy_value {
        Lazy thunk => thunk(),
        Eager value => value
    };
```

#### Runtime Implementation

```rust
pub enum Value {
    // ... existing variants ...
    Lazy(Box<dyn Fn() -> AstResult<Value>>),
    Stream(StreamValue),
}

pub struct StreamValue {
    pub head: Value,
    pub tail: Box<dyn Fn() -> AstResult<Value>>,
    pub evaluation_count: usize,
}

impl Evaluator {
    pub fn evaluate_lazy(&mut self, lazy_value: &Value) -> AstResult<Value> {
        match lazy_value {
            Value::Lazy(thunk) => {
                self.termination_monitor.check_bounds()?;
                thunk()
            }
            Value::Stream(stream) => {
                self.termination_monitor.check_bounds()?;
                Ok(Value::Record(vec![
                    ("head", stream.head.clone()),
                    ("tail", Value::Lazy(stream.tail.clone()))
                ]))
            }
            _ => Ok(lazy_value.clone())
        }
    }
}
```

### 4. Coinductive Types for Infinite Data

#### Type System Extensions

```ocaml
// Coinductive type definition
type CoList a =
    | Nil
    | Cons a (CoList a)
    coinductive;

// Infinite list of ones
let ones: CoList Int = Cons 1 ones;

// Infinite list of natural numbers
let naturals: CoList Int = Cons 0 (map (+1) naturals);

// Safe operations on coinductive types
let take_colist = \n \colist ->
    if n <= 0 then Nil
    else match colist {
        Nil => Nil,
        Cons head tail => Cons head (take_colist (n - 1) tail)
    };

// Guarded corecursion
let guarded_ones = Cons 1 (guarded_ones)
    where guard = \n -> n > 0;
```

#### Implementation

```rust
pub enum TypeKind {
    // ... existing variants ...
    Coinductive {
        name: String,
        body: Box<Type>,
        guard: Option<Box<Expr>>
    },
}

pub struct CoinductiveChecker {
    pub visited: HashSet<String>,
    pub guards: HashMap<String, Box<Expr>>,
}

impl CoinductiveChecker {
    pub fn check_guarded_corecursion(
        &mut self,
        type_name: &str,
        body: &Type,
        guard: Option<&Expr>
    ) -> AstResult<()> {
        // Check that corecursion is properly guarded
        if let Some(guard_expr) = guard {
            self.check_guard_condition(guard_expr, body)?;
        } else {
            return Err(AstError::UnguardedCorecursion {
                type_name: type_name.to_string(),
                span: body.span(),
            });
        }
        Ok(())
    }
}
```

## Implementation Strategy

### Phase 1: Resource Bounds (Immediate - 2-3 weeks)

#### Goals

- Add configurable resource bounds to the evaluator
- Implement termination monitoring
- Add runtime bounds checking

#### Implementation Tasks

1. **Extend Evaluator Structure**

```rust
pub struct Evaluator {
    // ... existing fields ...
    bounds: EvaluationBounds,
    termination_monitor: TerminationMonitor,
    totality_level: TotalityLevel,
}

pub struct TerminationMonitor {
    current_stack_depth: usize,
    current_recursion_depth: usize,
    evaluation_steps: usize,
    memory_usage: usize,
    start_time: std::time::Instant,
    bounds: EvaluationBounds,
}
```

2. **Add Bounds Checking**

```rust
impl TerminationMonitor {
    pub fn check_bounds(&mut self) -> AstResult<()> {
        if self.current_stack_depth > self.bounds.max_stack_depth {
            return Err(AstError::StackLimitExceeded {
                current: self.current_stack_depth,
                limit: self.bounds.max_stack_depth,
            });
        }

        if self.current_recursion_depth > self.bounds.max_recursion_depth {
            return Err(AstError::RecursionLimitExceeded {
                current: self.current_recursion_depth,
                limit: self.bounds.max_recursion_depth,
            });
        }

        if self.evaluation_steps > self.bounds.max_evaluation_steps {
            return Err(AstError::StepLimitExceeded {
                current: self.evaluation_steps,
                limit: self.bounds.max_evaluation_steps,
            });
        }

        if let Some(timeout) = self.bounds.timeout {
            if self.start_time.elapsed() > timeout {
                return Err(AstError::Timeout {
                    duration: timeout,
                });
            }
        }

        Ok(())
    }
}
```

3. **Update Error Types**

```rust
#[derive(Error, Debug, Clone)]
pub enum AstError {
    // ... existing variants ...
    #[error("Stack limit exceeded: {current} > {limit}")]
    StackLimitExceeded { current: usize, limit: usize },

    #[error("Recursion limit exceeded: {current} > {limit}")]
    RecursionLimitExceeded { current: usize, limit: usize },

    #[error("Evaluation step limit exceeded: {current} > {limit}")]
    StepLimitExceeded { current: usize, limit: usize },

    #[error("Memory limit exceeded: {current} > {limit}")]
    MemoryLimitExceeded { current: usize, limit: usize },

    #[error("Evaluation timeout after {duration:?}")]
    Timeout { duration: std::time::Duration },

    #[error("Unguarded corecursion in type {type_name}")]
    UnguardedCorecursion { type_name: String },
}
```

### Phase 2: Gradual Totality Annotations (Short-term - 4-6 weeks)

#### Goals

- Add syntax for totality annotations
- Implement totality level checking
- Add warning system for termination issues

#### Implementation Tasks

1. **Extend Grammar**

```pest
value_declaration = {
    ("let" ~ "rec")? ~ "let" ~ identifier ~ (":" ~ type_expression)? ~ "=" ~ value_expression ~ totality_annotation? ~ ";"
}

totality_annotation = {
    "where" ~ "termination" ~ "=" ~ termination_level ~ ("," ~ termination_bounds)?
}

termination_level = { "strict" | "bounded" | "monitored" | "unchecked" }

termination_bounds = {
    "limit" ~ "=" ~ integer_literal |
    "timeout" ~ "=" ~ float_literal |
    "max_stack_depth" ~ "=" ~ integer_literal |
    "max_recursion_depth" ~ "=" ~ integer_literal |
    "max_evaluation_steps" ~ "=" ~ integer_literal
}
```

2. **Add AST Extensions**

```rust
pub struct ValueDeclaration {
    // ... existing fields ...
    pub totality_annotation: Option<TotalityAnnotation>,
}

pub struct TotalityAnnotation {
    pub level: TotalityLevel,
    pub bounds: Option<EvaluationBounds>,
    pub span: Span,
}

pub enum TotalityLevel {
    Strict,
    Bounded,
    Monitored,
    Unchecked,
}
```

3. **Implement Totality Checking**

```rust
impl TypeChecker {
    pub fn check_totality_annotation(
        &mut self,
        declaration: &ValueDeclaration,
    ) -> AstResult<()> {
        if let Some(annotation) = &declaration.totality_annotation {
            match annotation.level {
                TotalityLevel::Strict => {
                    self.check_structural_recursion(&declaration.value)?;
                }
                TotalityLevel::Bounded => {
                    self.check_bounded_recursion(&declaration.value, &annotation.bounds)?;
                }
                TotalityLevel::Monitored => {
                    self.warn_non_structural_recursion(&declaration.value);
                }
                TotalityLevel::Unchecked => {
                    self.warn_unchecked_recursion(&declaration.value);
                }
            }
        }
        Ok(())
    }
}
```

### Phase 3: Lazy Evaluation (Medium-term - 6-8 weeks)

#### Goals

- Implement lazy evaluation for infinite data structures
- Add lazy value types to the type system
- Implement safe lazy evaluation with bounds checking

#### Implementation Tasks

1. **Extend Type System**

```rust
pub enum TypeKind {
    // ... existing variants ...
    Lazy(Box<Type>),
    Stream(Box<Type>),
}

pub enum Value {
    // ... existing variants ...
    Lazy(Box<dyn Fn() -> AstResult<Value>>),
    Stream(StreamValue),
}
```

2. **Implement Lazy Evaluation**

```rust
impl Evaluator {
    pub fn evaluate_lazy(&mut self, lazy_value: &Value) -> AstResult<Value> {
        match lazy_value {
            Value::Lazy(thunk) => {
                self.termination_monitor.check_bounds()?;
                thunk()
            }
            Value::Stream(stream) => {
                self.termination_monitor.check_bounds()?;
                Ok(Value::Record(vec![
                    ("head", stream.head.clone()),
                    ("tail", Value::Lazy(stream.tail.clone()))
                ]))
            }
            _ => Ok(lazy_value.clone())
        }
    }
}
```

### Phase 4: Coinductive Types (Long-term - 8-12 weeks)

#### Goals

- Add coinductive type definitions
- Implement guarded corecursion checking
- Add safe operations on infinite data structures

#### Implementation Tasks

1. **Extend Type System**

```rust
pub enum TypeKind {
    // ... existing variants ...
    Coinductive {
        name: String,
        body: Box<Type>,
        guard: Option<Box<Expr>>
    },
}
```

2. **Implement Guarded Corecursion**

```rust
pub struct CoinductiveChecker {
    pub visited: HashSet<String>,
    pub guards: HashMap<String, Box<Expr>>,
}

impl CoinductiveChecker {
    pub fn check_guarded_corecursion(
        &mut self,
        type_name: &str,
        body: &Type,
        guard: Option<&Expr>
    ) -> AstResult<()> {
        if let Some(guard_expr) = guard {
            self.check_guard_condition(guard_expr, body)?;
        } else {
            return Err(AstError::UnguardedCorecursion {
                type_name: type_name.to_string(),
                span: body.span(),
            });
        }
        Ok(())
    }
}
```

## Configuration and Usage

### Environment-Specific Configuration

```ocaml
// Development configuration
let dev_config = {
    totality = "monitored",
    bounds = {
        max_stack_depth = 10000,
        max_recursion_depth = 1000,
        max_evaluation_steps = 100000,
        max_memory_usage = 100_000_000,
        timeout = Some(30.0)
    },
    warnings = {
        non_structural_recursion = "warn",
        resource_usage = "warn",
        termination_guarantees = "warn"
    }
};

// Production configuration
let prod_config = {
    totality = "strict",
    bounds = {
        max_stack_depth = 1000,
        max_recursion_depth = 100,
        max_evaluation_steps = 10000,
        max_memory_usage = 10_000_000,
        timeout = Some(1.0)
    },
    warnings = {
        non_structural_recursion = "error",
        resource_usage = "error",
        termination_guarantees = "error"
    }
};
```

### CLI Integration

```bash
# Run with development configuration
ligature eval --config dev_config.lig --totality monitored program.lig

# Run with production configuration
ligature eval --config prod_config.lig --totality strict program.lig

# Run with custom bounds
ligature eval --max-stack-depth 5000 --max-recursion-depth 500 --timeout 10.0 program.lig
```

### IDE Integration

```json
// .vscode/settings.json
{
  "ligature.totality.level": "monitored",
  "ligature.bounds.maxStackDepth": 10000,
  "ligature.bounds.maxRecursionDepth": 1000,
  "ligature.bounds.timeout": 30.0,
  "ligature.warnings.nonStructuralRecursion": "warn"
}
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_bounded_recursion() {
    let source = "
        let rec bounded_factorial = \\n ->
            if n <= 1 then 1
            else if n > 100 then error \"Input too large\"
            else n * (bounded_factorial (n - 1))
            where termination = \"bounded\", limit = 100;

        bounded_factorial 5
    ";

    let result = parse_type_check_and_evaluate(source);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Value::Integer(120));
}

#[test]
fn test_recursion_limit_exceeded() {
    let source = "
        let rec infinite_recursion = \\n ->
            infinite_recursion (n + 1)
            where termination = \"bounded\", limit = 10;

        infinite_recursion 0
    ";

    let result = parse_type_check_and_evaluate(source);
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), AstError::RecursionLimitExceeded { .. }));
}
```

### Property-Based Tests

```rust
proptest! {
    #[test]
    fn test_termination_monitoring(expr in expr_strategy()) {
        let mut evaluator = Evaluator::with_bounds(EvaluationBounds {
            max_stack_depth: 1000,
            max_recursion_depth: 100,
            max_evaluation_steps: 10000,
            max_memory_usage: 10_000_000,
            timeout: Some(std::time::Duration::from_secs(1)),
        });

        let result = evaluator.evaluate_expression(&expr);
        // Should either succeed or fail with a termination-related error
        match result {
            Ok(_) => {},
            Err(AstError::StackLimitExceeded { .. }) => {},
            Err(AstError::RecursionLimitExceeded { .. }) => {},
            Err(AstError::StepLimitExceeded { .. }) => {},
            Err(AstError::Timeout { .. }) => {},
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}
```

### Integration Tests

```rust
#[test]
fn test_lazy_evaluation() {
    let source = "
        let infinite_ones = lazy [1, 1, 1, ...];
        let take = \\n \\list ->
            if n <= 0 then []
            else match list {
                [] => [],
                [head, ...tail] => [head, ...(take (n - 1) tail)]
            };

        take 5 infinite_ones
    ";

    let result = parse_type_check_and_evaluate(source);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Value::List(vec![
        Value::Integer(1),
        Value::Integer(1),
        Value::Integer(1),
        Value::Integer(1),
        Value::Integer(1),
    ]));
}
```

## Migration Strategy

### Backward Compatibility

1. **Default Behavior**: Existing programs continue to use strict totality by default
2. **Gradual Migration**: Users can opt into relaxed totality features incrementally
3. **Deprecation Warnings**: Clear warnings when using deprecated features
4. **Migration Tools**: Automated tools to help migrate configurations

### Migration Path

1. **Phase 1**: Add resource bounds without changing default behavior
2. **Phase 2**: Add totality annotations as optional features
3. **Phase 3**: Introduce lazy evaluation for specific use cases
4. **Phase 4**: Add coinductive types for advanced scenarios

### Migration Examples

```ocaml
// Before: Strict totality (current)
let rec factorial = \n ->
  if n <= 1 then 1 else n * (factorial (n - 1));

// After: Explicit strict totality
let rec factorial = \n ->
  if n <= 1 then 1 else n * (factorial (n - 1))
  where termination = "strict";

// After: Bounded totality for large inputs
let rec factorial = \n ->
  if n <= 1 then 1
  else if n > 1000 then error "Input too large"
  else n * (factorial (n - 1))
  where termination = "bounded", limit = 1000;
```

## Risks and Mitigations

### 1. Runtime Termination

**Risk**: Programs may not terminate, leading to resource exhaustion
**Mitigation**:

- Configurable resource bounds
- Runtime monitoring and timeouts
- Clear error messages with suggestions

### 2. Performance Degradation

**Risk**: Monitoring overhead may impact performance
**Mitigation**:

- Configurable monitoring levels
- Efficient bounds checking
- Optional monitoring for production

### 3. Complexity Increase

**Risk**: More complex language semantics may confuse users
**Mitigation**:

- Clear documentation and examples
- Gradual introduction of features
- IDE support with helpful error messages

### 4. Error Message Complexity

**Risk**: Termination-related errors may be hard to debug
**Mitigation**:

- Rich error reporting with context
- Actionable suggestions for fixes
- Debugging tools and visualizations

## Success Metrics

### Technical Metrics

1. **Expressiveness**: Number of configuration scenarios that can be expressed
2. **Performance**: Evaluation time and memory usage with bounds
3. **Safety**: Number of termination-related runtime errors
4. **Usability**: Error message clarity and debugging effectiveness

### User Experience Metrics

1. **Adoption**: Number of users adopting relaxed totality features
2. **Satisfaction**: User feedback on expressiveness vs. safety trade-offs
3. **Productivity**: Time saved in configuration development
4. **Error Reduction**: Reduction in workarounds for termination issues

## Conclusion

This proposal provides a comprehensive approach to relaxing Ligature's totality guarantees while maintaining safety through configurable bounds and monitoring. The gradual introduction of features ensures backward compatibility while enabling more expressive configuration scenarios.

The key benefits include:

1. **Increased Expressiveness**: Support for complex configuration transformations
2. **Maintained Safety**: Configurable safety levels appropriate for different use cases
3. **Better Developer Experience**: Clear error messages and debugging tools
4. **Backward Compatibility**: Existing programs continue to work unchanged
5. **Gradual Migration**: Users can adopt features incrementally

The implementation strategy provides a clear path forward with measurable milestones and comprehensive testing to ensure reliability and safety.

## References

1. [Dhall Language Specification](https://github.com/dhall-lang/dhall-lang/blob/master/standard/dhall.abnf)
2. [Cue Language Documentation](https://cuelang.org/docs/)
3. [Lean 4 Type Theory](https://leanprover.github.io/lean4/doc/)
4. [Structural Recursion](https://en.wikipedia.org/wiki/Structural_recursion)
5. [Coinduction](https://en.wikipedia.org/wiki/Coinduction)
