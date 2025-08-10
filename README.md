# Ligature

[![Ligature CI](https://img.shields.io/badge/Ligature%20CI-passing-brightgreen)](https://github.com/ligature-lang/ligature/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

**A Turing-incomplete configuration language with dependently-typed foundations that prioritizes correctness and safety.**

Ligature is built for configuration management with professional-grade IDE integration, comprehensive error reporting, and formal verification capabilities. All programs are guaranteed to terminate with complete type safety.

## Quick Example

```ocaml
// Define a validated user configuration
type User = {
    name: String where length > 0,
    age: Integer where >= 0 && <= 150,
    email: String where contains "@"
};

let config = {
    database = { host = "localhost", port = 5432 },
    users = [
        { name = "Alice", age = 30, email = "alice@company.com" },
        { name = "Bob", age = 25, email = "bob@company.com" }
    ]
};
```

## Why Ligature?

- **Correct by Design**: Turing-incomplete with total functions and termination guarantees
- **Professional Tooling**: Complete LSP integration with cross-module navigation
- **Configuration-Native**: Built specifically for config management, not general programming
- **Type-Level Safety**: Dependent types with constraint-based validation
- **Developer Experience**: ML-family syntax with comprehensive error messages

## Core Features

### ✅ Type System & Safety

- **Dependent Types** - Advanced type-level computation and proofs
- **Constraint-Based Validation** - Runtime validation with refinement types
- **Pattern Matching** - Exhaustive matching with guards
- **Union Types** - Safe data modeling with variants
- **Type Classes** - Principled polymorphism and interfaces

### ✅ Professional Development Experience

- **Language Server (LSP)** - Full IDE integration with VS Code and others
- **Cross-Module Navigation** - Go to definition and find references
- **Real-Time Diagnostics** - Immediate error feedback with fix suggestions
- **Import Resolution** - Automatic dependency tracking and module loading
- **Performance Monitoring** - Built-in optimization analysis

### ✅ Configuration Management

- **Module System** - Clean code organization and reusability
- **Import System** - Relative imports, register imports, and workspace resolution
- **Termination Guarantee** - All programs guaranteed to halt
- **Memory Safety** - No runtime errors or undefined behavior

## What Ligature Won't Do

Ligature is intentionally limited to ensure correctness and focus:

- ❌ Arbitrary recursion or infinite loops
- ❌ I/O operations or side effects
- ❌ Concurrency primitives
- ❌ Runtime code generation
- ❌ File system or process operations

## Getting Started

### Installation

```bash
# Install the Ligature toolchain
cargo install ligature

# Or use our development workflow
git clone https://github.com/ligature-lang/ligature
cd ligature
just install  # Requires 'just' command runner
```

### First Steps

1. **Write a simple config** - Create `config.lig`:

   ```ocaml
   let server_config = {
       host = "localhost",
       port = 8080,
       debug = true
   };
   ```

2. **Parse and validate**:

   ```bash
   just reed parse --file config.lig
   just reed typecheck --file config.lig
   ```

3. **Set up IDE integration** - Install our [VS Code extension](docs/user-guide/ide-integration.md)

## Language Overview

### Basic Types and Literals

```ocaml
// Primitive types
let count: Integer = 42;
let rate: Float = 3.14159;
let name: String = "Ligature";
let enabled: Boolean = true;
let unit: Unit = ();
```

### Records with Constraints

```ocaml
type DatabaseConfig = {
    host: String where length > 0,
    port: Integer where >= 1024 && <= 65535,
    max_connections: Integer where > 0,
    ssl_enabled: Boolean
};

let db = {
    host = "db.example.com",
    port = 5432,
    max_connections = 100,
    ssl_enabled = true
};
```

### Functions and Pattern Matching

```ocaml
type Result = Success String | Error String;

let handle_result = \result -> match result {
    Success msg => "✓ " ++ msg,
    Error err => "✗ " ++ err
};

// Type classes for polymorphism
class Show a {
    show: a -> String;
}

instance Show Integer {
    show = \n -> toString n;
}
```

### Advanced Type-Level Features

```ocaml
// Type-level computation
type If 'Cond 'Then 'Else;
type Equal 'A 'B;
type Subtype 'A 'B;

// Dependent types for complex validation
type ValidatedConfig 'Schema = {
    data: 'Schema,
    validated: Equal (TypeOf data) 'Schema
};
```

## Performance

Current benchmarks show excellent performance for configuration workloads:

| Operation         | Throughput   | Improvement      |
| ----------------- | ------------ | ---------------- |
| Function Calls    | 1M+ ops/sec  | 2.7x faster      |
| Cache Hit Rate    | 99.95%       | Expression-level |
| Pattern Matching  | 823K ops/sec | Optimized        |
| Simple Arithmetic | 784K ops/sec | Baseline         |

## Applications & CLI Tools

### Reed CLI - Core Language Tools

```bash
just reed parse --file config.lig        # Parse and validate syntax
just reed typecheck --file config.lig    # Type checking
just reed eval --file config.lig         # Evaluate expressions
```

### Cacophony CLI - Configuration Orchestration

```bash
just cacophony run --config deploy.lig   # Deploy configurations
just cacophony validate --env production # Validate environments
```

### Keywork - Package Manager

```bash
just keywork install stdlib              # Install standard library
just keywork init my-register           # Create new register
```

## Documentation

### Essential Guides

- **[Getting Started](docs/user-guide/getting-started.md)** - Installation and first programs
- **[Language Reference](docs/user-guide/language-reference.md)** - Complete syntax guide
- **[IDE Integration](docs/user-guide/ide-integration.md)** - Development environment setup
- **[Real-world Examples](docs/user-guide/examples.md)** - Practical configuration patterns

### Advanced Topics

- **[Type-Level Computation](docs/user-guide/type-level-computation.md)** - Advanced type system
- **[Performance Guide](docs/user-guide/performance-guide.md)** - Optimization techniques
- **[Architecture Overview](docs/architecture/README.md)** - System design
- **[API Reference](docs/api-reference.md)** - Complete API documentation

### Development

- **[Contributing Guidelines](CONTRIBUTING.md)** - How to contribute
- **[Developer Guide](docs/developer-guide.md)** - Internal architecture
- **[Justfile Guide](docs/.development/justfile-guide.md)** - Development workflow

## Contributing

We welcome contributions! Ligature is actively developed with clear contribution guidelines:

- **Report Issues** - [GitHub Issues](https://github.com/ligature-lang/ligature/issues)
- **Join Discussions** - [GitHub Discussions](https://github.com/ligature-lang/ligature/discussions)
- **Read the Guide** - [Contributing Guidelines](CONTRIBUTING.md)

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) or https://www.apache.org/licenses/LICENSE-2.0.

## Inspiration & References

Ligature draws inspiration from several excellent projects:

- **Dhall** - Configuration language design patterns
- **Cue** - Constraint-based validation and syntax ergonomics
- **Lean 4** - Type theory and dependent types foundation
- **Rust Analyzer** - Professional LSP implementation
- **Elm** - Accessible ML-family syntax and error messages

## Dedication

This project is dedicated to **Pedro Furlanetto**, whose vision for well-designed programming languages and thoughtful approach to software development continues to inspire Ligature's priorities and design decisions.
