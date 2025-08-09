# embouchure-checker

Type checker implementation for the Ligature language.

This crate provides type checking, type inference, and type system functionality for the Ligature language. It was extracted from the `ligature-types` crate to provide a dedicated, reusable type checking library.

## Features

- **Type Checking**: Complete type checking for Ligature programs
- **Type Inference**: Automatic type inference for expressions
- **Module Resolution**: Module and import resolution for type checking
- **Constraint Solving**: Type constraint solving for advanced type system features
- **Environment Management**: Type environment management with scoping and conflict resolution

## Usage

```rust
use embouchure_checker::{type_check_program, TypeChecker};
use ligature_ast::Program;
use ligature_parser::parse_program;

// Type check a complete program
let source = "let x = 42; let y = x + 1;";
let program = parse_program(source).unwrap();
let result = type_check_program(&program);

// Use the TypeChecker directly for more control
let mut checker = TypeChecker::new();
checker.bind("x".to_string(), Type::integer(Span::default()));
```

## API

### Main Functions

- `type_check_program(program: &Program) -> StandardResult<()>`: Type check a complete program
- `type_check_program_with_paths(program: &Program, search_paths: &[PathBuf], register_paths: &[PathBuf]) -> StandardResult<()>`: Type check with custom paths
- `type_check_module(module: &Module) -> StandardResult<()>`: Type check a single module
- `infer_expression(expr: &Expr) -> StandardResult<Type>`: Infer the type of an expression

### Core Types

- `TypeChecker`: Main type checker implementation
- `TypeEnvironment`: Type environment with scoping and conflict resolution
- `ConstraintSolver`: Type constraint solving
- `ModuleResolver`: Module and import resolution

## Dependencies

- `ligature-ast`: AST types and structures
- `ligature-error`: Error handling
- `ligature-parser`: Parser integration
- `indexmap`: Efficient indexed maps
- `serde`: Serialization support
- `toml`: TOML parsing for configuration

## Migration from ligature-types

This crate was extracted from `ligature-types` to provide better separation of concerns. The `ligature-types` crate now re-exports the type checking functions from this crate, so existing code should continue to work without changes.

## License

Apache-2.0
