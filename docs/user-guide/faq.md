# Frequently Asked Questions (FAQ)

This FAQ addresses common questions about the Ligature language, its features, and usage.

## Table of Contents

1. [Language Basics](#language-basics)
2. [Type System](#type-system)
3. [Pattern Matching](#pattern-matching)
4. [Modules](#modules)
5. [Performance](#performance)
6. [Tooling](#tooling)
7. [Best Practices](#best-practices)
8. [Troubleshooting](#troubleshooting)

## Language Basics

### What is Ligature?

Ligature is a Turing-incomplete configuration and data management language with a dependently-typed foundation. It's designed to be safe, type-safe, and optimized for configuration management and data validation.

### Why is Ligature Turing-incomplete?

Ligature is Turing-incomplete by design to ensure that all programs terminate. This makes it ideal for configuration management where you want guaranteed termination and predictable behavior.

### What makes Ligature different from other configuration languages?

- **Type Safety**: Strong static typing prevents runtime errors
- **Pattern Matching**: Powerful pattern matching for data validation
- **Module System**: First-class module support for code organization
- **Termination Guarantee**: All programs are guaranteed to terminate
- **ML-family Syntax**: Familiar syntax inspired by OCaml and Elm

### Can I use Ligature for general-purpose programming?

No, Ligature is specifically designed for configuration management and data validation. It lacks features like I/O, recursion, and side effects that would be needed for general-purpose programming.

## Type System

### How does type inference work in Ligature?

Ligature uses Hindley-Milner type inference, which can automatically determine types for most expressions. You can also provide explicit type annotations when needed.

```ocaml
// Type inference
let x = 42; // Inferred as Integer
let add = \x y -> x + y; // Inferred as Integer -> Integer -> Integer

// Explicit type annotation
let multiply: Integer -> Integer -> Integer = \x y -> x * y;
```

### What are union types and how do I use them?

Union types allow you to represent data that can be one of several variants:

```ocaml
type Option = Some a | None;
type Result = Success a | Error String;

let safe_divide = \x y -> match y of
    0 => None,
    _ => Some (x / y);
```

### How do I define custom types?

You can define custom types using type aliases and union types:

```ocaml
// Type alias
type UserId = Integer;
type Email = String;

// Union type
type User = {
    id: UserId,
    name: String,
    email: Email,
    status: UserStatus
};

type UserStatus = Active | Inactive | Suspended;
```

### What's the difference between records and tuples?

Records have named fields, while tuples have positional fields:

```ocaml
// Record
let user = {
    name = "Alice",
    age = 30
};

// Tuple (if supported)
let point = (10, 20);
```

## Pattern Matching

### How does pattern matching work?

Pattern matching allows you to destructure data and handle different cases:

```ocaml
let classify_number = \n -> match n of
    x when x < 0 => "negative",
    x when x == 0 => "zero",
    x when x > 0 => "positive",
    _ => "unknown";
```

### What are pattern guards?

Pattern guards allow you to add conditions to pattern matches:

```ocaml
let validate_age = \age -> match age of
    a when a < 0 => Invalid "Age cannot be negative",
    a when a > 150 => Invalid "Age seems unrealistic",
    _ => Valid;
```

### How do I handle exhaustive pattern matching?

Always include cases for all possible variants or use a wildcard pattern:

```ocaml
type Option = Some a | None;

let get_value = \option -> match option of
    Some value => value,
    None => 0; // Handle all cases
```

### Can I use pattern matching with records?

Yes, you can pattern match on record fields:

```ocaml
let greet_user = \user -> match user of
    { name = n, age = a } when a >= 18 => "Hello, " ++ n,
    { name = n } => "Hello, young " ++ n,
    _ => "Hello, stranger";
```

## Modules

### How do I create a module?

Use the `module` keyword to define a module:

```ocaml
module Math {
    let add = \x y -> x + y;
    let subtract = \x y -> x - y;
    let multiply = \x y -> x * y;

    type Point = {
        x: Integer,
        y: Integer
    };
}
```

### How do I import from a module?

Use the `import` keyword to import modules:

```ocaml
// Import entire module
import Math;

// Import specific items
import Math { add, Point };

// Import with alias
import Math as M;
```

### How do I export items from a module?

Use the `export` keyword to specify what gets exported:

```ocaml
module MyModule {
    let public_function = \x -> x + 1;
    let private_helper = \x -> x * 2; // Not exported

    export { public_function };
}
```

### Can modules have circular dependencies?

No, circular dependencies between modules are not allowed. You need to restructure your code to avoid them.

## Performance

### How fast is Ligature?

Ligature is designed for correctness over speed, but it's still reasonably fast for configuration tasks. The evaluation engine is optimized for typical configuration workloads.

### How can I optimize my Ligature code?

- Use pattern matching instead of nested if-then-else
- Avoid unnecessary type annotations when inference works
- Use appropriate data structures (records vs unions)
- Minimize complex nested expressions

### Does Ligature support lazy evaluation?

No, Ligature uses eager evaluation. All expressions are evaluated immediately when encountered.

### How much memory does Ligature use?

Memory usage depends on the size and complexity of your data structures. Ligature uses garbage collection to manage memory automatically.

## Tooling

### What IDEs support Ligature?

Ligature has a Language Server Protocol (LSP) implementation that provides:

- Syntax highlighting
- Code completion
- Error reporting
- Hover information
- Go to definition

Any IDE that supports LSP can be configured to work with Ligature.

### How do I run Ligature programs?

Use the `reed` CLI tool:

```bash
# Check if a file is valid
cargo run --bin reed -- check config.lig

# Type check a file
cargo run --bin reed -- typecheck config.lig

# Evaluate a file
cargo run --bin reed -- eval config.lig

# Format a file
cargo run --bin reed -- fmt config.lig
```

### How do I run benchmarks?

Use the benchmark command:

```bash
# Quick performance test
cargo run --bin reed -- benchmark quick

# Comprehensive analysis
cargo run --bin reed -- benchmark comprehensive

# Custom benchmark
cargo run --bin reed -- benchmark custom --file my_benchmark.lig
```

### How do I debug Ligature code?

- Use the `trace` function for debugging
- Add explicit type annotations to catch type errors
- Use pattern guards for conditional debugging
- Check error messages for specific line and column information

## Best Practices

### What are the naming conventions in Ligature?

- Use `camelCase` for variables and functions
- Use `PascalCase` for types and modules
- Use descriptive names that explain intent
- Avoid single-letter names except for simple parameters

### How should I organize my Ligature code?

- Group related declarations together
- Use modules to organize code
- Export only what's needed from modules
- Keep functions small and focused

### What's the best way to handle errors?

Use union types for error handling:

```ocaml
type ValidationResult = Valid | Invalid String;

let validate_user = \user -> match user of
    { age = a } when a < 0 => Invalid "Age cannot be negative",
    { age = a } when a > 150 => Invalid "Age seems unrealistic",
    _ => Valid;
```

### How should I structure configuration files?

- Use records for structured configuration
- Use union types for different configuration modes
- Validate configuration with pattern matching
- Use modules to organize related configuration

## Troubleshooting

### My program won't compile. What should I do?

1. Check the error message for the specific line and column
2. Verify all variables are defined before use
3. Ensure all pattern matches are exhaustive
4. Check that record fields match their type definitions
5. Verify module imports and exports

### I'm getting a type error. How do I fix it?

1. Add explicit type annotations to help the type checker
2. Check that function arguments match their expected types
3. Ensure record fields have the correct types
4. Verify that union type variants are used correctly

### My pattern matching isn't working. What's wrong?

1. Check that all cases are covered
2. Verify pattern guard conditions return Boolean values
3. Ensure variable bindings in patterns are unique
4. Check that union patterns have the correct number of arguments

### How do I handle large configuration files?

1. Break them into smaller modules
2. Use imports to organize related configuration
3. Use type aliases to reduce repetition
4. Consider using validation functions to check configuration

### My module imports aren't working. What should I check?

1. Verify the module name is correct
2. Check that imported items are actually exported
3. Ensure there are no circular dependencies
4. Verify the module file exists and is valid

### How do I test my Ligature code?

1. Use the CLI to check syntax and types
2. Write test cases using pattern matching
3. Use validation functions to test data
4. Create example configurations to verify behavior

### What should I do if I find a bug?

1. Create a minimal example that reproduces the bug
2. Check the error messages for clues
3. Look at the documentation for the feature
4. Report the issue with a clear description and example

## Getting Help

### Where can I find more documentation?

- [Getting Started Guide](getting-started.md)
- [Language Reference](language-reference.md)
- [Real-world Examples](examples.md)
- [Error Messages Guide](error-messages.md)

### How can I contribute to Ligature?

1. Report bugs and issues
2. Suggest new features
3. Improve documentation
4. Submit pull requests with fixes or improvements

### Where can I ask questions?

- GitHub Issues: For bug reports and feature requests
- GitHub Discussions: For questions and general discussion
- Project documentation: For detailed guides and examples

### Is Ligature production-ready?

Ligature is currently in development. While the core language features are implemented, it may not be suitable for all production use cases yet. Check the project status and roadmap for current capabilities.
