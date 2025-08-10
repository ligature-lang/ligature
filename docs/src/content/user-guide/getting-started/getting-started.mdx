# Getting Started with Ligature

Welcome to Ligature! This guide will help you get up and running with the Ligature configuration language.

## What is Ligature?

Ligature is a Turing-incomplete configuration and data management language with a dependently-typed foundation. It's designed to be:

- **Safe by design** - All programs are guaranteed to terminate
- **Type-safe** - Strong static typing prevents runtime errors
- **Configuration-focused** - Optimized for configuration management and data validation
- **Accessible** - Familiar ML-family syntax inspired by OCaml and Elm
- **Advanced type system** - Type classes and instance declarations for extensible types

## Installation

### Prerequisites

- Rust 1.70+ (stable)
- Cargo

### Building from Source

```bash
# Clone the repository
git clone https://github.com/ligature-lang/ligature.git
cd ligature

# Build all crates
cargo build

# Build the CLI tool
cargo build --bin reed
```

## Your First Ligature Program

Let's start with a simple example. Create a file called `hello.lig`:

```ocaml
// A simple greeting function
let greet = \name -> "Hello, " ++ name ++ "!";

// Use the function
let message = greet "World";
```

Run it with the CLI:

```bash
cargo run --bin reed -- eval hello.lig
```

## Basic Language Features

### Values and Types

Ligature has a rich type system with several built-in types:

```ocaml
// Basic literals
let answer = 42;                    // Integer
let pi = 3.14159;                  // Float
let greeting = "Hello, World!";    // String
let is_valid = true;               // Boolean
let nothing = ();                  // Unit

// Type annotations (optional)
let count: Integer = 10;
let message: String = "Hello";
```

### Records

Records are collections of named fields:

```ocaml
// Create a record
let user = {
    name = "Alice",
    age = 30,
    email = "alice@example.com"
};

// Access fields
let user_name = user.name;

// Record types
type User = {
    name: String,
    age: Integer,
    email: String
};
```

### Functions

Functions are first-class values in Ligature:

```ocaml
// Function definition
let add = \x y -> x + y;

// Function with type annotation
let multiply: Integer -> Integer -> Integer = \x y -> x * y;

// Higher-order functions
let apply_twice = \f x -> f (f x);
let result = apply_twice (\x -> x * 2) 5;  // 20
```

### Pattern Matching

Pattern matching is a powerful feature for data validation:

```ocaml
// Union types
type Option = Some a | None;

let safe_divide = \x y ->
    if y == 0 then None else Some (x / y);

let handle_result = \result -> match result of
    Some value => "Result: " ++ toString value,
    None => "Division by zero!";
```

### Type Classes

Ligature supports type classes for extensible type systems:

```ocaml
// Define a type class
typeclass Show 'a where
    show : 'a -> String;

// Implement instances
instance Show Int where
    show = \x -> toString x;

instance Show Bool where
    show = \b -> if b then "true" else "false";

// Use the type class
let display : Show 'a => 'a -> String = \x -> "Value: " ++ show x;
```

### Instance Declarations

You can implement type classes for your own types:

```ocaml
// Define a custom type
type Point = { x: Integer, y: Integer };

// Implement Show for Point
instance Show Point where
    show = \p -> "Point(" ++ toString p.x ++ ", " ++ toString p.y ++ ")";

// Now you can use show with Point
let point = { x = 10, y = 20 };
let display = show point;  // "Point(10, 20)"
```

### Constrained Instances

You can create instances that depend on other type class constraints:

```ocaml
// Type class for equality
typeclass Eq 'a where
    eq : 'a -> 'a -> Bool;

// Type class for ordering
typeclass Ord 'a where
    superclass Eq 'a;
    compare : 'a -> 'a -> Ordering;

// Constrained instance
instance (Eq 'a, Eq 'b) => Eq (Pair 'a 'b) where
    eq = \p1 p2 -> eq p1.first p2.first && eq p1.second p2.second;
```

## Module System

### Creating Modules

Organize your code into modules:

```ocaml
// math.lig
module Math;

export let add = \x y -> x + y;
export let multiply = \x y -> x * y;
export type Point = { x: Float, y: Float };

// Private function (not exported)
let internal_helper = \x -> x * 2;
```

### Importing Modules

```ocaml
// Import entire module
import "./math";

// Import specific items
import "./math" { add, Point };

// Import with alias
import "./math" as math;

// Use imported items
let result = add 5 3;
let point = math.Point { x = 1.0, y = 2.0 };
```

### Standard Library Imports

```ocaml
// Import from standard library
import "std.collections.list";
import "std.string" { concat, split };

// Use standard library functions
let numbers = [1, 2, 3, 4, 5];
let doubled = map (\x -> x * 2) numbers;
```

## Development Tools

### Language Server (LSP)

Ligature includes a full-featured language server that provides:

- **Intelligent code completion** - Context-aware suggestions
- **Go to definition** - Navigate to symbol definitions
- **Find references** - Find all uses of a symbol
- **Real-time error reporting** - Immediate feedback on syntax and type errors
- **Cross-module navigation** - Work across multiple files seamlessly
- **Code actions** - Automatic fixes and suggestions

### CLI Tool (reed)

The `reed` command-line tool provides various operations:

```bash
# Evaluate a file
cargo run --bin reed -- eval program.lig

# Type check a file
cargo run --bin reed -- check program.lig

# Format code
cargo run --bin reed -- format program.lig

# Show AST
cargo run --bin reed -- ast program.lig
```

## Advanced Features

### Union Types

Union types allow you to represent data with multiple variants:

```ocaml
type Shape =
    Circle { radius: Float } |
    Rectangle { width: Float, height: Float } |
    Triangle { a: Float, b: Float, c: Float };

let area = \shape -> match shape of
    Circle { radius } => 3.14159 * radius * radius,
    Rectangle { width, height } => width * height,
    Triangle { a, b, c } =>
        // Heron's formula
        let s = (a + b + c) / 2.0;
        sqrt (s * (s - a) * (s - b) * (s - c));
```

### Pattern Guards

Add conditions to pattern matching:

```ocaml
let categorize = \age -> match age of
    a when a < 18 => "Minor",
    a when a < 65 => "Adult",
    _ => "Senior";
```

### Recursive Functions

Define recursive functions with `let rec`:

```ocaml
let rec factorial = \n ->
    if n == 0 then 1 else n * factorial (n - 1);

let rec fibonacci = \n ->
    if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2);
```

## Configuration Examples

### Application Configuration

```ocaml
type Environment = Development | Staging | Production;

type LogLevel = Debug | Info | Warn | Error;

type AppConfig = {
    name: String,
    version: String,
    environment: Environment,
    debug: Boolean,
    log_level: LogLevel,
    port: Integer,
    host: String,
    max_connections: Integer,
    timeout_seconds: Integer
};

let default_config = {
    name = "MyApplication",
    version = "1.0.0",
    environment = Development,
    debug = true,
    log_level = Debug,
    port = 8080,
    host = "localhost",
    max_connections = 100,
    timeout_seconds = 30
};
```

### Data Validation

```ocaml
type ValidationResult = Valid | Invalid String;

let validate_user = \user -> match user of
    { name = n, age = a, email = e } when
        length n > 0 &&
        a >= 0 && a <= 150 &&
        contains "@" e => Valid,
    _ => Invalid "Invalid user data";

let validate_config = \config -> match config of
    { port = p, host = h } when
        p > 0 && p <= 65535 &&
        length h > 0 => Valid,
    _ => Invalid "Invalid configuration";
```

## Next Steps

1. **Explore the language reference** - Learn about all language features
2. **Check out examples** - See real-world usage patterns
3. **Set up your IDE** - Configure LSP for the best development experience
4. **Read the FAQ** - Find answers to common questions
5. **Join the community** - Get help and share your experiences

## IDE Setup

### VS Code

1. Install the Ligature extension (when available)
2. Open a `.lig` file
3. Enjoy syntax highlighting, completion, and error reporting

### Other Editors

The LSP server works with any editor that supports the Language Server Protocol:

- Neovim with nvim-lspconfig
- Emacs with lsp-mode
- Sublime Text with LSP plugin
- And many others

## Getting Help

- **Documentation**: Check the language reference and examples
- **Error messages**: Ligature provides detailed error messages to help debug issues
- **Community**: Join discussions on GitHub
- **Issues**: Report bugs or request features on GitHub

Happy coding with Ligature!
