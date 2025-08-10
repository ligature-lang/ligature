# Ligature Language

[![Ligature CI](https://img.shields.io/badge/Ligature%20CI-passing-brightgreen)](https://github.com/ligature-lang/ligature/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

A Turing-incomplete configuration and data management language with a dependently-typed foundation.

## Language Philosophy

Ligature is designed to be:

- **Correct over fast** - Prioritizes correctness and good error messages over performance
- **Configuration-native** - Built specifically for configuration management, not general-purpose programming
- **Verification-ready** - Foundation for formal verification and property-based testing
- **Developer-friendly** - Professional-grade IDE integration and development tools

## Table of Contents

- [Overview](#overview)
- [What Ligature Will NOT Do](#what-ligature-will-not-do)
- [Language Features](#language-features)
  - [Core Features](#core-features-)
  - [Advanced Features](#advanced-features-)
  - [Performance Features](#performance-features-)
  - [Operator Precedence](#operator-precedence-)
  - [Basic Types](#basic-types)
  - [Records](#records)
  - [Functions](#functions)
  - [Pattern Matching](#pattern-matching)
  - [Type System](#type-system)
  - [Type-Level Computation](#type-level-computation)
- [Development Tools](#development-tools)
  - [Professional-Grade IDE Integration](#professional-grade-ide-integration-)
  - [Language Server (LSP)](#language-server-lsp-)
  - [Import Resolution](#import-resolution-)
  - [Type Class System](#type-class-system-)
  - [Command Line Interface](#command-line-interface)
- [Applications](#applications)
  - [Cacophony CLI](#cacophony-cli)
  - [Reed CLI](#reed-cli)
  - [Keywork](#keywork)
- [Performance](#performance)
- [Getting Started](#getting-started)
- [Documentation](#documentation)
  - [User Guides](#user-guides)
  - [Architecture & Development](#architecture--development)
- [Contributing](#contributing)
- [License](#license)
- [References and Inspiration](#references-and-inspiration)
- [Dedication](#dedication)
- [Contact](#contact)

## Overview

Ligature is a configuration language designed with correctness and safety as primary goals. It provides:

- **Turing-incomplete by design** - All programs are guaranteed to terminate
- **Dependently-typed foundation** - Based on Lean 4 type theory
- **ML-family syntax** - Familiar and accessible syntax inspired by OCaml and Elm
- **Configuration-focused** - Optimized for configuration management and data validation
- **Strong correctness guarantees** - Total functions with comprehensive error reporting
- **Professional-grade IDE integration** - Complete LSP symbol finding and development tools
- **Advanced type-level computation** - Type-level programming with dependent types and subtyping

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

### Core Features ✅

- **Type Safety** - Strong static typing prevents runtime errors
- **Pattern Matching** - Powerful pattern matching for data validation
- **Module System** - First-class module support for code organization
- **Import Resolution** - Complete import resolution with cross-module support
- **Termination Guarantee** - All programs are guaranteed to terminate
- **Type Classes** - Advanced type system with type classes and instances
- **Instance Declarations** - Support for constrained and unconstrained instances
- **Constraint-Based Validation** - Refinement types and pattern constraints with runtime validation

### Advanced Features ✅

- **Union Types** - Represent data with multiple variants
- **Pattern Guards** - Conditional pattern matching
- **Type Inference** - Automatic type detection
- **Record Types** - Structured data with named fields
- **Cross-Module Navigation** - Go to definition and find references across modules
- **LSP Integration** - Full language server support with completion and error reporting
- **Import Constraints** - Type class constraints in instance declarations
- **Type-Level Computation** - Advanced type-level programming capabilities

### Performance Features ✅

- **Function Call Optimization** - Multi-tier optimization for function calls (1M+ ops/sec)
- **Environment Lookup Optimization** - Fast reference-based lookups
- **Evaluation Caching** - Framework for expression-level caching (99.95% hit rate)
- **Memory Allocation Optimization** - Reduced allocation overhead
- **Pattern Matching Optimization** - Early termination and efficient binding
- **Advanced Tail Call Detection** - Pattern-based and context-sensitive optimization
- **Function Inlining** - Automatic inlining of small, pure functions
- **Parallel Evaluation** - Multi-threaded expression evaluation
- **Performance Monitoring** - Real-time performance analysis and optimization

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

// Record types with constraints
type User = {
    name: String where length > 0,
    age: Integer where >= 0 && <= 150,
    email: String where contains "@"
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

### Language Server (LSP) ✅

- **Cross-Module Completion** - Intelligent code completion from imported modules
- **Go to Definition** - Navigate to symbol definitions across module boundaries
- **Find References** - Find all references to symbols across the entire workspace
- **Workspace Symbols** - Search for symbols across all loaded modules
- **Real-time Error Reporting** - Immediate feedback on syntax and type errors
- **Module Loading** - Automatic discovery and loading of modules in workspace
- **Code Actions** - Automatic fixes and suggestions for common issues
- **Enhanced Diagnostics** - Detailed error explanations and fix suggestions
- **Advanced Code Actions** - Intelligent refactoring and code generation
- **Symbol Finding** - Professional-grade symbol navigation and search
- **Import Resolution** - Complete module resolution with dependency tracking

### Import Resolution ✅

- **Relative Imports** - Support for `./` and `../` path resolution
- **Register Imports** - Import from Ligature registers (e.g., `std.collections.list`)
- **Workspace Imports** - Automatic resolution of modules within workspace folders
- **Selective Imports** - Import specific symbols from modules
- **Import Aliases** - Alias imported modules for cleaner code
- **Cycle Detection** - Prevents infinite import loops
- **Module Caching** - Efficient caching with file modification detection

### Type Class System ✅

- **Type Class Definitions** - Define type classes with methods and superclasses
- **Instance Declarations** - Implement type classes for specific types
- **Constrained Instances** - Instance declarations with type class constraints
- **Method Implementation** - Complete method implementation checking
- **Type Class Constraints** - Use type classes in function signatures

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

## Applications

### Cacophony CLI

A CLI tool for orchestrating collections of Ligature programs:

- **Purpose-Agnostic**: Not tied to any specific domain but can orchestrate any Ligature-based configuration
- **Register-Centric**: Built around Ligature's register system for dependency management
- **Environment-Aware**: Supports multiple environments (dev, staging, prod)
- **Declarative Operations**: All operations defined declaratively in Ligature
- **Type-Safe Orchestration**: Leverages Ligature's type system for correctness
- **Extensible**: Plugin system for custom operations and integrations

### Reed CLI

A command-line interface for Ligature programs:

- **Parse Ligature files** - Syntax validation and AST generation
- **Type checking** - Static type analysis and error reporting
- **Evaluation** - Execute Ligature programs and view results
- **Performance analysis** - Built-in benchmarking and optimization

### Keywork

Package manager for Ligature registers:

- **Register management** - Install, update, and manage Ligature libraries
- **Dependency resolution** - Automatic dependency management
- **Version control** - Semantic versioning for registers
- **Registry integration** - Centralized package distribution

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

### User Guides

- **[Getting Started](docs/user-guide/getting-started.md)** - Your first steps with Ligature
- **[Language Reference](docs/user-guide/language-reference.md)** - Complete language documentation
- **[Real-world Examples](docs/user-guide/examples.md)** - Practical configuration examples
- **[Error Messages](docs/user-guide/error-messages.md)** - Understanding and debugging errors
- **[FAQ](docs/user-guide/faq.md)** - Frequently asked questions
- **[Cacophony CLI](docs/user-guide/cacophony-cli.md)** - Configuration orchestration and deployment
- **[Performance Guide](docs/user-guide/performance-guide.md)** - Performance optimization and monitoring
- **[IDE Integration](docs/user-guide/ide-integration.md)** - Professional-grade development environment
- **[Type-Level Computation](docs/user-guide/type-level-computation.md)** - Advanced type system features

### Architecture & Development

- **[Architecture Overview](docs/architecture/README.md)** - Complete system design and components
- **[Developer Guide](docs/developer-guide.md)** - Comprehensive guide for contributors and integrators
- **[API Reference](docs/api-reference.md)** - Complete API documentation for all components
- **[Technical Analysis](docs/analysis/)** - Deep technical analysis and project tracking
- **[Contributing Guidelines](CONTRIBUTING.md)** - How to contribute to Ligature

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

## Dedication

This project is dedicated to **Pedro Furlanetto**, whose ideas and vision inspired many of the priorities and design decisions in Ligature. His enthusiasm for well-designed languages and thoughtful approach to programming continue to influence my work.

## Contact

- GitHub Issues: [https://github.com/ligature-lang/ligature/issues](https://github.com/ligature-lang/ligature/issues)
- Discussions: [https://github.com/ligature-lang/ligature/discussions](https://github.com/ligature-lang/ligature/discussions)
