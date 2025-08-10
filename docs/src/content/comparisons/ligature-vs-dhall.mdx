# Ligature vs Dhall: A Comprehensive Comparison

## Overview

This document provides a detailed comparison between Ligature and Dhall, two configuration languages that share some design goals but take fundamentally different approaches to configuration management and type safety.

## Core Philosophy & Design Goals

### Ligature

- **Dependently-typed foundation** based on Lean 4 type theory
- **Configuration-native** design with strong validation focus
- **Correctness over performance** - prioritizes formal verification
- **Accessible to average engineers** - avoids Haskell complexity
- **Verification-ready** - foundation for formal proofs

### Dhall

- **Non-dependent type system** based on System Fω
- **General-purpose configuration** with emphasis on safety
- **Performance-conscious** design
- **Haskell-inspired** syntax and concepts
- **Pragmatic approach** to configuration management

## Type System Differences

### Ligature's Advanced Type System

Ligature provides a sophisticated type system with features typically found in advanced functional programming languages:

```ocaml
// Dependent types (Pi and Sigma)
type Vector n = { length: n, elements: List n }

// Type classes with constraints
typeclass Show a where
  show: a -> String

// Higher-kinded types
typeclass Functor f where
  map: (a -> b) -> f a -> f b

// Union types with complex pattern matching
type Result a b = Success a | Error b

// Pattern matching with guards
let classify = \x -> match x {
  n when n > 0 => "positive",
  n when n < 0 => "negative",
  _ => "zero"
}
```

### Dhall's Simpler Type System

Dhall focuses on a more practical type system suitable for configuration management:

```dhall
-- Basic types only
let Vector = { length: Natural, elements: List Text }

-- Simple union types
let Result = < Success: Text | Error: Text >

-- No type classes or higher-kinded types
-- Limited to basic type system features
```

## Language Features Comparison

| Feature                   | Ligature                   | Dhall            |
| ------------------------- | -------------------------- | ---------------- |
| **Dependent Types**       | ✅ Full support (Pi/Sigma) | ❌ Not supported |
| **Type Classes**          | ✅ Complete implementation | ❌ Not supported |
| **Higher-Kinded Types**   | ✅ Supported               | ❌ Not supported |
| **Pattern Matching**      | ✅ Advanced with guards    | ✅ Basic support |
| **Union Types**           | ✅ Complex with payloads   | ✅ Simple unions |
| **Module System**         | ✅ Imports/exports/aliases | ✅ Import system |
| **Formal Verification**   | ✅ Lean 4 integration      | ❌ Not supported |
| **JSON/YAML Integration** | 🔄 Planned                 | ✅ Primary focus |

## Configuration Focus

### Ligature's Configuration Features

Ligature is designed specifically for configuration with advanced validation capabilities:

```ocaml
// Schema-based validation with constraints
type UserConfig = {
  name: String where length > 0,
  age: Integer where 0 <= age <= 150,
  email: String where isValidEmail
}

// Constraint satisfaction
let config = {
  name = "John",
  age = 25,
  email = "john@example.com"
} : UserConfig

// Configuration merging and inheritance
let baseConfig = { timeout = 30, retries = 3 }
let extendedConfig = { timeout = 60, debug = true }
let finalConfig = merge baseConfig extendedConfig
```

### Dhall's Configuration Features

Dhall focuses on practical configuration management:

```dhall
-- Basic type validation
let UserConfig = { name: Text, age: Natural, email: Text }

-- Configuration with defaults
let defaultConfig = { timeout: Natural = 30, retries: Natural = 3 }

-- No built-in constraint system
-- Relies on external validation
```

## Termination Guarantees

### Ligature

- **Turing-incomplete by design**
- **No arbitrary recursion**
- **Strong normalization** property
- **Formal termination proofs** via Lean 4
- **All programs guaranteed to terminate**

### Dhall

- **Turing-incomplete by design**
- **Limited recursion** patterns
- **Termination via structural recursion**
- **Pragmatic termination guarantees**
- **No formal termination proofs**

## Syntax & Usability

### Ligature's ML-Family Syntax

Ligature uses ML-inspired syntax that's familiar to functional programmers:

```ocaml
// ML-inspired syntax
let add = \x -> \y -> x + y

// Pattern matching with guards
let result = match value {
  Some x when x > 0 => "positive",
  Some x => "non-positive",
  None => "missing"
}

// Type annotations
let processUser: User -> String = \user ->
  match user {
    Admin { name } => "Admin: " ++ name,
    Regular { name, role } => "User: " ++ name ++ " (" ++ role ++ ")"
  }
```

### Dhall's Functional Syntax

Dhall uses Haskell-inspired syntax:

```dhall
-- Haskell-inspired syntax
let add = λ(x : Natural) → λ(y : Natural) → x + y

-- Simple conditional expressions
let result = if value then "true" else "false"

-- Record operations
let user = { name = "John", age = 30 }
let userName = user.name
```

## Integration & Ecosystem

### Ligature

- **Package management** via `keywork` system
- **Client SDKs** via `krox` framework
- **Language server** for IDE support
- **Formal specification** in Lean 4
- **Differential testing** against formal spec
- **Comprehensive test suite** (100+ tests)

### Dhall

- **Direct JSON/YAML integration**
- **Multiple language bindings** (Haskell, Python, Go, etc.)
- **Standard library** of functions
- **Import system** for code reuse
- **CLI tools** for validation
- **Mature ecosystem** with community support

## Error Handling & Safety

### Ligature

- **Comprehensive error reporting** with source locations
- **Type-level error prevention** via dependent types
- **Formal error semantics** defined in Lean 4
- **Pattern matching exhaustiveness** checking
- **Advanced type inference** with constraint solving

### Dhall

- **Good error messages** with type information
- **Type safety** via static typing
- **Import safety** with hash verification
- **Basic error handling** patterns
- **Simple type inference**

## Performance & Scalability

### Ligature

- **Correctness over performance** design
- **Formal verification** overhead
- **Rich type system** complexity
- **Configuration-focused** optimization
- **Early development** stage

### Dhall

- **Performance-conscious** design
- **Efficient evaluation** strategies
- **Optimized for large configurations**
- **Fast parsing and evaluation**
- **Production-ready** performance

## Use Cases

### Ligature Best For

- **Critical configuration** requiring formal verification
- **Complex validation** with dependent types
- **Research and academic** applications
- **Safety-critical systems** where correctness is paramount
- **Advanced type-level programming**
- **Configuration with complex constraints**
- **Systems requiring formal proofs**

### Dhall Best For

- **General configuration** management
- **JSON/YAML replacement** with type safety
- **DevOps and infrastructure** configuration
- **Practical configuration** with good error messages
- **Team adoption** with familiar functional concepts
- **Production environments** requiring reliability
- **Configuration that needs to be human-readable**

## Development Status

### Ligature

- **Early development** stage
- **Core infrastructure** in place
- **Comprehensive test suite** (100+ tests, 100% pass rate)
- **Formal specification** in Lean 4
- **Active development** with clear roadmap

### Dhall

- **Mature and stable** language
- **Production-ready** with extensive usage
- **Well-documented** with tutorials and examples
- **Active community** and ecosystem
- **Multiple language bindings** available

## Learning Curve

### Ligature

- **Steeper learning curve** due to advanced type system
- **Requires understanding** of dependent types
- **Formal verification** concepts may be unfamiliar
- **More powerful** but more complex

### Dhall

- **Gentler learning curve** for functional programmers
- **Familiar concepts** from Haskell/ML
- **Practical focus** makes it easier to get started
- **Good documentation** and examples

## Future Directions

### Ligature

- **Formal verification** integration
- **Advanced type system** features
- **Configuration-specific** optimizations
- **Academic and research** applications
- **Safety-critical** system adoption

### Dhall

- **Ecosystem expansion** with more language bindings
- **Performance improvements**
- **Enhanced tooling** and IDE support
- **Community growth** and adoption
- **Production deployment** optimization

## Summary

**Ligature** represents a more **academically rigorous** approach to configuration languages, with dependent types, type classes, and formal verification capabilities. It's designed for scenarios where **correctness is more important than convenience** and where the advanced type system features provide significant value.

**Dhall** represents a more **pragmatic approach**, focusing on **practical configuration management** with good type safety and error messages. It's designed for **real-world adoption** in production environments where reliability and ease of use are paramount.

### Key Differences

1. **Type System**: Ligature has a much more advanced type system with dependent types and type classes, while Dhall focuses on practical type safety.

2. **Philosophy**: Ligature prioritizes correctness and formal verification, while Dhall prioritizes practicality and adoption.

3. **Complexity**: Ligature is more complex but more powerful, while Dhall is simpler but more accessible.

4. **Maturity**: Dhall is production-ready with a mature ecosystem, while Ligature is in early development with ambitious goals.

5. **Use Cases**: Ligature targets safety-critical and research applications, while Dhall targets general configuration management.

The choice between Ligature and Dhall depends on your specific needs: if you require advanced type system features and formal verification, Ligature is the better choice. If you need a practical, production-ready configuration language with good type safety, Dhall is the better choice.
