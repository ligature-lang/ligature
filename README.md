# Ligature Language

[![Ligature CI](https://img.shields.io/badge/Ligature%20CI-passing-brightgreen)](https://github.com/ligature-lang/ligature/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

A Turing-incomplete configuration and data management language with a dependently-typed foundation.

## Overview

Ligature is a configuration language designed with correctness and safety as primary goals. It provides:

- **Turing-incomplete by design** - All programs are guaranteed to terminate
- **Dependently-typed foundation** - Based on Lean 4 type theory
- **ML-family syntax** - Familiar and accessible syntax inspired by OCaml and Elm
- **Configuration-focused** - Optimized for configuration management and data validation
- **Strong correctness guarantees** - Total functions with comprehensive error reporting
- **Professional-grade IDE integration** - Complete LSP symbol finding and development tools
- **Advanced type-level computation** - Type-level programming with dependent types and subtyping

## Language Philosophy

Ligature is designed to be:

- **Correct over fast** - Prioritizes correctness and good error messages over performance
- **Accessible to average engineers** - Avoids the complexity of Haskell while maintaining power
- **Configuration-native** - Built specifically for configuration management, not general-purpose programming
- **Verification-ready** - Foundation for formal verification and property-based testing
- **Developer-friendly** - Professional-grade IDE integration and development tools

## What Ligature Will NOT Do

- Arbitrary recursion or loops
- I/O operations or side effects
- Concurrency primitives
- Runtime code generation
- High-performance/large-scale data processing
- Arbitrary string manipulation or template engine features
- File system operations or process execution
- Require users to write explicit proofs

## Language Features

### Operator Precedence ✅

Ligature has a complete and correct operator precedence system:

```ocaml
// Arithmetic precedence: multiplication before addition
let result = 2 + 3 * 4;  // Evaluates to 14, not 20

// Unary operator precedence
let negative = -5 + 3;   // Evaluates to -2

// Logical operator precedence
let logical = true && false || true;  // Evaluates to true

// Function application precedence
let applied = f x + y;   // Evaluates as (f x) + y

// Field access precedence
let field = record.field + 5;  // Evaluates as (record.field) + 5
```

### Basic Types

```ocaml
// Basic literals
let answer = 42;
let pi = 3.14159;
let greeting = "Hello, World!";
let is_valid = true;
let nothing = ();

// Type annotations (optional)
let count: Integer = 10;
let message: String = "Hello";
```

### Records

```ocaml
// Record construction
let user = {
    name = "Alice",
    age = 30,
    email = "alice@example.com"
};

// Record field access
let user_name = user.name;

// Record types
type User = {
    name: String,
    age: Integer,
    email: String
};
```

### Functions

```ocaml
// Function definition
let add = \x y -> x + y;

// Function application
let result = add 5 3;

// Function with type annotation
let multiply: Integer -> Integer -> Integer = \x y -> x * y;
```

### Pattern Matching

```ocaml
// Pattern matching on records
let greet = \user -> match user {
    { name = n } => "Hello, " ++ n,
    _ => "Hello, stranger"
};

// Pattern matching on unions
type Result = Success String | Error String;

let handle_result = \result -> match result {
    Success message => "Success: " ++ message,
    Error error => "Error: " ++ error
};
```

### Type System

```ocaml
// Union types
type Option = Some a | None;

// Type aliases
type UserId = Integer;
type Email = String;

// Type classes
class Show a {
    show: a -> String;
}

instance Show Integer {
    show = \n -> toString n;
}
```

### Type-Level Computation

```ocaml
// Type-level functions
type Id 'T = 'T;
type Compose 'F 'G 'A = 'F ('G 'A);

// Type-level pattern matching
type ProjectField 'FieldName 'RecordType;

// Dependent types
type ApplyPi 'F 'A;
type Proj1 'S;
type Proj2 'S;

// Advanced subtyping
type Subtype 'A 'B;
type Equal 'A 'B;
type If 'Cond 'Then 'Else;
```

## Development Tools

### Professional-Grade IDE Integration ✅

- **Cross-File Symbol Finding** - Go to definition and find references across modules
- **Import Resolution** - Automatic module loading and dependency tracking
- **Workspace Symbol Search** - Search symbols across entire workspace
- **Real-time Error Diagnostics** - Immediate feedback with fix suggestions
- **Code Completion** - Context-aware completions with import suggestions
- **Performance Monitoring** - Built-in performance analysis and optimization

### Command Line Interface

The workspace includes a comprehensive `justfile` for streamlined development:

```bash
# Install just (if not already installed)
cargo install just

# Install all Ligature apps
just install

# Run reed CLI
just reed parse --file config.lig
just reed typecheck --file config.lig
just reed eval --file config.lig

# Run cacophony (orchestration)
just cacophony run --config my-config.lig

# Run keywork (package manager)
just keywork init my-register
just keywork install stdlib

# See all available commands
just --list
```

For detailed development workflows, see [Justfile Development Guide](docs/.development/justfile-guide.md).

## Performance

Current performance metrics (after optimizations):

| Operation Type          | Throughput          | Notes                   |
| ----------------------- | ------------------- | ----------------------- |
| **Function Calls**      | **1M+ ops/sec**     | **2.7x improvement**    |
| **Cache Effectiveness** | **99.95% hit rate** | **Expression caching**  |
| **Simple Arithmetic**   | 784K ops/sec        | Basic operations        |
| **Pattern Matching**    | 823K ops/sec        | Conditional expressions |

## Getting Started

1. **Install Ligature**: See [Installation Guide](docs/user-guide/getting-started.md)
2. **Write your first program**: Create a simple configuration
3. **Set up IDE integration**: Install [VS Code Extension](docs/user-guide/ide-integration.md)
4. **Explore examples**: Check out [Examples](docs/user-guide/examples.md)
5. **Learn advanced features**: [Type-Level Computation](docs/user-guide/type-level-computation.md)

## Documentation

- **[User Guide](docs/user-guide/)** - Complete user documentation
- **[Performance Guide](docs/user-guide/performance-guide.md)** - Optimization and monitoring
- **[IDE Integration](docs/user-guide/ide-integration.md)** - Development environment setup
- **[Type-Level Computation](docs/user-guide/type-level-computation.md)** - Advanced type system features
- **[January 2025 Achievements](docs/january-2025-achievements.md)** - Recent major milestones

## Contributing

We welcome contributions! Please see our [Contributing Guide](CONTRIBUTING.md) for details on development setup, code style, and current development priorities.

## License

This project is licensed under the Apache License, Version 2.0 - see the [LICENSE](LICENSE) file or https://www.apache.org/licenses/LICENSE-2.0 for details.

## References and Inspiration

- **Dhall**: For configuration language design patterns
- **Cue**: For syntax ergonomics and constraint-based validation
- **Lean 4**: For type theory foundation
- **Rust Analyzer**: For LSP implementation patterns
- **Elm**: For accessible ML-family syntax design

## Contact

- GitHub Issues: [https://github.com/ligature-lang/ligature/issues](https://github.com/ligature-lang/ligature/issues)
- Discussions: [https://github.com/ligature-lang/ligature/discussions](https://github.com/ligature-lang/ligature/discussions)
