# Library System Decision: Registers

**Status**: Approved  
**Date**: July 2025  
**Decision**: The register-based library system has been approved for implementation in Ligature.

## Overview

This document outlines the approved design and implementation of a library system for Ligature, where libraries are called "registers" to align with the language's configuration-focused philosophy. The system will provide a structured way to organize, distribute, and consume reusable Ligature code.

## Design Philosophy

### Core Principles

1. **Configuration-First**: Registers are designed primarily for configuration management, not general-purpose libraries
2. **Correctness Over Convenience**: Type safety and correctness are prioritized over ease of use
3. **Explicit Dependencies**: All dependencies must be explicitly declared and versioned
4. **Immutable and Reproducible**: Register versions are immutable and builds are reproducible
5. **Minimal Surface Area**: The system introduces minimal new syntax to the core language

### Terminology

- **Register**: A collection of Ligature modules, types, and functions
- **Module**: A single `.lig` file containing declarations
- **Registry**: A collection of registers (local or remote)
- **Dependency**: A register that another register depends on
- **Version**: An immutable snapshot of a register's contents

## System Architecture

### Directory Structure

```
ligature/
├── registers/                    # Standard library registers
│   ├── stdlib/                  # Core standard library
│   │   ├── core/               # Core types and functions
│   │   ├── collections/        # List, Map, Set operations
│   │   ├── validation/         # Data validation utilities
│   │   └── register.toml       # Register manifest
│   ├── config/                 # Configuration utilities
│   │   ├── env/               # Environment variable handling
│   │   ├── file/              # File system operations
│   │   └── register.toml
│   └── crypto/                 # Cryptographic utilities
│       ├── hash/              # Hashing functions
│       ├── encoding/          # Base64, hex encoding
│       └── register.toml
├── docs/
│   └── architecture/
│       └── decisions/
│           └── library-system.md  # This document
└── examples/
    └── registers/              # Example user registers
        ├── my-config/
        └── shared-types/
```

### Register Manifest (`register.toml`)

Each register must include a `register.toml` manifest file:

```toml
[register]
name = "stdlib"
version = "1.0.0"
description = "Ligature Standard Library"
authors = ["Ligature Team <team@ligature.dev>"]
license = "Apache-2.0"
repository = "https://github.com/ligature-lang/ligature"

[dependencies]
# No dependencies for stdlib

[exports]
# Modules that can be imported by other registers
core = "core/mod.rs"
collections = "collections/mod.rs"
validation = "validation/mod.rs"

[metadata]
tags = ["standard-library", "core"]
```

### Module Structure

Each module within a register follows a standard structure:

```ligature
-- core/mod.rs
module Core

-- Re-export commonly used items
export { Bool, Int, String, Unit }
export { List, Map, Option, Result }

-- Core type definitions
type Bool = True | False

type Option<T> = Some(T) | None

type Result<T, E> = Ok(T) | Err(E)

-- Core functions
let not : Bool -> Bool = fun b ->
  match b with
  | True -> False
  | False -> True

let isSome : Option<T> -> Bool = fun opt ->
  match opt with
  | Some(_) -> True
  | None -> False
```

## Language Integration

### Import Syntax

The library system extends Ligature's syntax with import statements:

```ligature
-- Import entire module
import stdlib.core

-- Import specific items
import { List, Map } from stdlib.collections

-- Import with alias
import stdlib.validation as validation

-- Import specific function
import { validateEmail } from stdlib.validation

-- Use imported items
let myList : List<Int> = [1, 2, 3]
let isValid = validation.validateEmail("test@example.com")
```

### Module Declaration

Modules can be declared explicitly:

```ligature
module MyModule

-- Module contents
type MyType = Variant1 | Variant2

let myFunction : Int -> Int = fun x -> x + 1

-- Export specific items
export { MyType, myFunction }
```

## Implementation Plan

### Phase 1: Core Infrastructure

1. **Register Manifest Parser**

   - Parse `register.toml` files
   - Validate manifest structure
   - Handle dependency resolution

2. **Module Resolution**

   - Resolve import statements
   - Handle module paths and aliases
   - Implement module loading

3. **Dependency Management**

   - Dependency graph construction
   - Cycle detection
   - Version conflict resolution

4. **Error Accumulation System**
   - Error collector with context preservation
   - AST-stack mapping infrastructure
   - Non-blocking parsing and type checking
   - Error suggestion engine

### Phase 2: Standard Library

1. **Core Types and Functions**

   - Basic data types (Bool, Int, String, Unit)
   - Option and Result types
   - Basic operations and utilities

2. **Collections**

   - List operations (map, filter, fold)
   - Map and Set implementations
   - Iterator patterns

3. **Validation**
   - Email validation
   - URL validation
   - JSON schema validation

### Phase 3: Tooling

1. **Register CLI Commands**

   ```bash
   ligature register init my-register
   ligature register build
   ligature register publish
   ligature register install stdlib
   ```

2. **Registry Management**
   - Local registry for development
   - Remote registry for distribution
   - Version management and updates

## Type System Integration

### Module Types

The type system will be extended to handle module types:

```ligature
-- Module type definition
type Module = {
  name: String,
  exports: Map<String, Type>,
  dependencies: List<Module>
}

-- Type checking for imports
let importedType : stdlib.core.Option<Int> = Some(42)
```

### Type Resolution

1. **Import Resolution**: Resolve imported types during type checking
2. **Module Type Inference**: Infer types for module exports
3. **Dependency Type Checking**: Ensure imported types are valid

## Error System Implementation

### Error Collector Architecture

The error system is built around a centralized error collector that maintains full context throughout the compilation and evaluation process.

#### Core Components

```rust
// Error collector that accumulates errors without stopping compilation
struct ErrorCollector {
    errors: Vec<ErrorContext>,
    warnings: Vec<ErrorContext>,
    suggestions: Vec<Suggestion>,
    context_stack: Vec<CompilationContext>,
}

// Compilation context that tracks current state
struct CompilationContext {
    register: String,
    module: String,
    function: Option<String>,
    span: Span,
    type_context: TypeContext,
    local_variables: HashMap<String, Type>,
}

// Rich error context with full diagnostic information
struct ErrorContext {
    error_type: ErrorType,
    span: Span,
    message: String,
    severity: ErrorSeverity,
    stack_trace: Vec<StackFrame>,
    type_context: Option<TypeContext>,
    suggestions: Vec<String>,
    related_errors: Vec<ErrorId>,
}
```

#### Error Accumulation Strategy

```rust
impl ErrorCollector {
    // Add error without stopping compilation
    fn add_error(&mut self, error: ErrorContext) {
        self.errors.push(error);
        // Continue compilation with error recovery
        self.recover_from_error(&error);
    }

    // Recover from error and continue compilation
    fn recover_from_error(&mut self, error: &ErrorContext) {
        match error.error_type {
            ErrorType::SyntaxError => {
                // Skip to next valid token and continue parsing
                self.skip_to_recovery_point();
            }
            ErrorType::TypeError => {
                // Infer type as Unknown and continue type checking
                self.infer_unknown_type();
            }
            ErrorType::ImportError => {
                // Mark import as failed and continue with partial module
                self.mark_import_failed();
            }
        }
    }
}
```

### AST-Stack Mapping Implementation

#### Span Tracking

Every AST node maintains precise source location information:

```rust
struct Span {
    start: Position,
    end: Position,
    file: String,
    register: String,
    module: String,
}

struct Position {
    line: usize,
    column: usize,
    offset: usize,
}
```

#### Stack Frame Construction

During evaluation, the system maintains a call stack that maps directly to AST nodes:

```rust
struct StackFrame {
    function_name: String,
    register: String,
    module: String,
    span: Span,
    ast_node: AstNodeRef,
    local_variables: HashMap<String, Value>,
    type_context: TypeContext,
}

impl StackFrame {
    fn from_ast_node(node: &AstNode, context: &CompilationContext) -> Self {
        Self {
            function_name: context.function.clone().unwrap_or_default(),
            register: context.register.clone(),
            module: context.module.clone(),
            span: node.span.clone(),
            ast_node: node.id,
            local_variables: context.local_variables.clone(),
            type_context: context.type_context.clone(),
        }
    }
}
```

### Error Recovery and Suggestions

#### Intelligent Error Recovery

```rust
impl ErrorCollector {
    fn generate_suggestions(&self, error: &ErrorContext) -> Vec<String> {
        match error.error_type {
            ErrorType::TypeError => self.suggest_type_fixes(error),
            ErrorType::ImportError => self.suggest_import_fixes(error),
            ErrorType::DependencyError => self.suggest_dependency_fixes(error),
            ErrorType::ValidationError => self.suggest_validation_fixes(error),
            _ => vec![],
        }
    }

    fn suggest_type_fixes(&self, error: &ErrorContext) -> Vec<String> {
        let mut suggestions = vec![];

        // Analyze type context and suggest similar types
        if let Some(type_context) = &error.type_context {
            let similar_types = self.find_similar_types(type_context);
            for similar_type in similar_types {
                suggestions.push(format!("Use '{}' instead", similar_type));
            }
        }

        // Suggest common patterns
        suggestions.push("Add explicit type annotation".to_string());
        suggestions.push("Check function signature".to_string());

        suggestions
    }
}
```

#### Contextual Error Analysis

```rust
impl ErrorCollector {
    fn analyze_error_context(&self, error: &ErrorContext) -> ErrorAnalysis {
        ErrorAnalysis {
            root_cause: self.find_root_cause(error),
            affected_modules: self.find_affected_modules(error),
            breaking_changes: self.identify_breaking_changes(error),
            compatibility_issues: self.check_compatibility(error),
        }
    }

    fn find_root_cause(&self, error: &ErrorContext) -> Option<ErrorContext> {
        // Trace error chain to find original cause
        let mut current = error;
        while let Some(related) = self.find_related_error(current) {
            if related.severity == ErrorSeverity::Error {
                current = related;
            } else {
                break;
            }
        }
        Some(current.clone())
    }
}
```

### Performance Optimizations

#### Lazy Error Reporting

```rust
impl ErrorCollector {
    // Only generate full error reports when requested
    fn generate_error_report(&self, max_errors: usize) -> ErrorReport {
        let mut report = ErrorReport::new();

        // Group errors by type and location
        let grouped_errors = self.group_errors();

        for (error_group, errors) in grouped_errors {
            if report.error_count() >= max_errors {
                report.add_summary(format!("... and {} more errors",
                    self.errors.len() - max_errors));
                break;
            }

            report.add_error_group(error_group, errors);
        }

        report
    }
}
```

#### Error Caching

```rust
struct ErrorCache {
    cache: HashMap<ErrorKey, CachedError>,
    ttl: Duration,
}

impl ErrorCache {
    fn get_or_compute(&mut self, key: ErrorKey, compute: impl Fn() -> ErrorContext) -> ErrorContext {
        if let Some(cached) = self.cache.get(&key) {
            if cached.is_fresh() {
                return cached.error.clone();
            }
        }

        let error = compute();
        self.cache.insert(key, CachedError::new(error.clone()));
        error
    }
}
```

## Error Handling and Diagnostics

### Error Accumulation Requirements

The register system must accumulate errors to the maximum extent possible, providing comprehensive diagnostics rather than failing fast. This is critical for configuration management where users need to see all issues at once.

#### Error Collection Strategy

1. **Non-Blocking Parsing**: Continue parsing even when encountering syntax errors
2. **Type Error Accumulation**: Collect all type errors across modules before reporting
3. **Dependency Error Batching**: Group related dependency errors together
4. **Import Error Context**: Provide full context for import resolution failures

#### Error Reporting Format

```ligature
-- Example: Multiple errors accumulated and reported together
Error: Multiple issues found in configuration

1. Type Error in stdlib.validation/mod.lig:15:23
   Expected: String -> Bool
   Found: String -> Int
   Context: validateEmail function signature
   Suggestion: Change return type to Bool

2. Import Error in my-config/config.lig:8:12
   Module 'stdlib.validation' not found
   Available modules: ['stdlib.core', 'stdlib.collections']
   Suggestion: Check module name or add to register.toml exports

3. Dependency Error in register.toml
   Circular dependency: A -> B -> C -> A
   Affected registers: ['my-config', 'shared-types', 'utils']
   Suggestion: Remove one of the circular dependencies

4. Validation Error in config.lig:42:15
   Invalid email format: "invalid-email"
   Expected: RFC 5322 compliant email
   Suggestion: Use format like "user@domain.com"
```

### Smart Stack Traversal and AST Mapping

#### Strongly Typed Error System

The register system implements a sophisticated error tracking system that maintains full context between the abstract syntax tree (AST) and runtime stack traces.

##### Error Context Preservation

```rust
// Error context structure (conceptual)
struct ErrorContext {
    span: Span,                    // Source location
    ast_node: AstNode,            // AST node reference
    stack_trace: Vec<StackFrame>,  // Call stack
    register_path: Vec<String>,    // Register/module path
    type_context: TypeContext,     // Type information at error
    suggestions: Vec<String>,      // Suggested fixes
}

struct StackFrame {
    function_name: String,
    register: String,
    module: String,
    span: Span,
    local_vars: HashMap<String, Type>,
}
```

##### AST-Stack Mapping

```ligature
-- Example: Error with full context mapping
let validateUserConfig : UserConfig -> Result<UserConfig, ValidationError> = fun config ->
  let emailResult = validateEmail(config.email)  -- Error occurs here
  let nameResult = validateName(config.name)
  in
  match (emailResult, nameResult) with
  | (Ok(email), Ok(name)) -> Ok({ email, name })
  | (Err(e), _) -> Err(e)
  | (_, Err(e)) -> Err(e)

-- Error report with AST mapping:
Error: Validation failed in validateUserConfig
  ├─ Location: my-config/config.lig:15:45
  ├─ AST Node: Function application (validateEmail)
  ├─ Stack Trace:
  │  ├─ validateUserConfig (my-config/config.lig:12)
  │  ├─ processConfig (my-config/config.lig:8)
  │  └─ main (my-config/config.lig:3)
  ├─ Type Context:
  │  ├─ config.email: String
  │  ├─ validateEmail: String -> Result<String, ValidationError>
  │  └─ Expected: Result<String, ValidationError>
  ├─ Register Path: my-config -> stdlib.validation
  └─ Suggestion: Check email format or handle validation error
```

#### Error Recovery and Suggestions

##### Intelligent Error Recovery

1. **Partial Evaluation**: Continue evaluation where possible, marking failed paths
2. **Type Inference Hints**: Provide suggestions based on type inference
3. **Import Resolution**: Suggest similar module names or alternative imports
4. **Dependency Resolution**: Propose dependency version fixes

##### Contextual Suggestions

```ligature
-- Example: Smart suggestions based on context
Error: Type mismatch in validation function
  ├─ Expected: String -> Bool
  ├─ Found: String -> Int
  ├─ Context: Email validation function
  ├─ Similar functions in scope:
  │  ├─ isValidEmail: String -> Bool
  │  ├─ validateEmail: String -> Result<String, ValidationError>
  │  └─ checkEmail: String -> Option<String>
  └─ Suggestions:
     ├─ Use 'isValidEmail' for boolean result
     ├─ Use 'validateEmail' for detailed validation
     └─ Handle Result type with pattern matching
```

### Import Errors

```ligature
-- Error: Module not found with context
import nonexistent.module  -- Error: Module 'nonexistent.module' not found
  ├─ Available modules: ['stdlib.core', 'stdlib.collections', 'stdlib.validation']
  ├─ Similar modules: ['stdlib.core', 'stdlib.config']
  └─ Suggestion: Check spelling or add module to register.toml

-- Error: Item not exported with full context
import { PrivateFunction } from stdlib.core
  ├─ Error: 'PrivateFunction' not exported by 'stdlib.core'
  ├─ Available exports: ['Bool', 'Unit', 'Option', 'Result', 'not', 'and', 'or']
  ├─ Similar names: ['PublicFunction', 'private_function']
  └─ Suggestion: Use one of the available exports or check module documentation

-- Error: Version conflict with dependency graph
-- register.toml: Dependencies 'stdlib@1.0.0' and 'stdlib@2.0.0' conflict
  ├─ Dependency graph:
  │  ├─ my-config@1.0.0 -> stdlib@1.0.0
  │  ├─ shared-types@2.0.0 -> stdlib@2.0.0
  │  └─ my-config@1.0.0 -> shared-types@2.0.0
  ├─ Breaking changes in stdlib@2.0.0:
  │  ├─ validateEmail signature changed
  │  └─ List type interface updated
  └─ Suggestion: Update my-config to use stdlib@2.0.0 or pin shared-types to compatible version
```

### Dependency Errors

```ligature
-- Error: Circular dependency with full analysis
-- register.toml: Circular dependency detected: A -> B -> C -> A
  ├─ Dependency cycle:
  │  ├─ A@1.0.0 -> B@1.0.0
  │  ├─ B@1.0.0 -> C@1.0.0
  │  └─ C@1.0.0 -> A@1.0.0
  ├─ Affected registers: ['my-config', 'shared-types', 'utils']
  ├─ Cycle analysis:
  │  ├─ A exports: ['Config', 'validateConfig']
  │  ├─ B exports: ['Types', 'UserConfig']
  │  └─ C exports: ['Utils', 'formatConfig']
  └─ Suggestions:
     ├─ Extract shared types to separate register
     ├─ Use dependency injection pattern
     └─ Restructure to remove circular dependency

-- Error: Missing dependency with resolution hints
-- register.toml: Required dependency 'stdlib@1.0.0' not found
  ├─ Available versions: ['0.9.0', '1.1.0', '2.0.0']
  ├─ Compatibility matrix:
  │  ├─ 0.9.0: Breaking changes in type system
  │  ├─ 1.1.0: Compatible, recommended
  │  └─ 2.0.0: Compatible, latest features
  ├─ Registry sources: ['local', 'remote', 'github']
  └─ Suggestion: Update to 'stdlib@1.1.0' or 'stdlib@2.0.0'
```

## Security Considerations

### Sandboxing

1. **No Arbitrary Code Execution**: Registers cannot execute arbitrary code
2. **Type Safety**: All imports are type-checked
3. **Immutable Dependencies**: Dependencies are locked to specific versions

### Validation

1. **Manifest Validation**: All register manifests are validated
2. **Content Validation**: Register contents are validated for correctness
3. **Dependency Validation**: Dependencies are validated for compatibility

## Performance Considerations

### Lazy Loading

1. **Module Loading**: Modules are loaded only when imported
2. **Type Caching**: Resolved types are cached for performance
3. **Dependency Caching**: Dependency graphs are cached

### Compilation

1. **Incremental Compilation**: Only changed modules are recompiled
2. **Parallel Type Checking**: Independent modules can be type-checked in parallel
3. **Optimization**: Dead code elimination for unused imports

## Migration Strategy

### Existing Code

1. **Backward Compatibility**: Existing `.lig` files continue to work
2. **Gradual Migration**: Optional migration to register structure
3. **Tooling Support**: Migration tools to convert existing code

### Documentation

1. **Register Documentation**: Each register includes comprehensive documentation
2. **API Documentation**: Generated documentation for all exported items
3. **Examples**: Example usage for all registers

## Future Extensions

### Advanced Features

1. **Conditional Imports**: Import different modules based on conditions
2. **Plugin System**: Extend language with custom syntax
3. **Remote Registries**: Distributed registry system
4. **Version Constraints**: Flexible version constraints (e.g., `^1.0.0`)

### Tooling Integration

1. **IDE Support**: Language server support for registers
2. **Testing Framework**: Built-in testing for registers
3. **Benchmarking**: Performance benchmarking tools
4. **Documentation Generation**: Automatic documentation generation

## Addressing Jsonnet's Error Handling Weaknesses

### Jsonnet's Error Handling Problems

Jsonnet, while powerful, has significant weaknesses in error handling that the Ligature register system directly addresses:

#### 1. **Fail-Fast Error Handling**

- **Jsonnet Problem**: Stops at the first error, requiring multiple iterations to fix all issues
- **Ligature Solution**: Accumulates all errors and provides comprehensive diagnostics in a single pass

#### 2. **Poor Error Context**

- **Jsonnet Problem**: Error messages often lack sufficient context about where and why errors occur
- **Ligature Solution**: Rich error context with AST-stack mapping, type information, and call traces

#### 3. **Weak Import Error Messages**

- **Jsonnet Problem**: Import errors provide minimal guidance on how to fix issues
- **Ligature Solution**: Intelligent suggestions with available alternatives and dependency analysis

#### 4. **No Type Safety**

- **Jsonnet Problem**: Runtime errors due to type mismatches that could be caught at compile time
- **Ligature Solution**: Strong static typing with dependent types prevents many runtime errors

### Comparative Examples

#### Jsonnet Error Handling

```jsonnet
// Jsonnet: Fails at first error, poor context
{
  local config = import "config.libsonnet",
  local user = config.users[0],  // Error: users is undefined
  // Never reaches this line due to fail-fast
  email: user.email,
  name: user.name
}

// Error output:
// RUNTIME ERROR: Field does not exist: users
// 	config.libsonnet:1:1-1:1	object <anonymous>
```

#### Ligature Error Handling

```ligature
-- Ligature: Accumulates errors, rich context
let config = import "config.lig"
let user = config.users[0]  -- Error: users field not found
let email = user.email      -- Error: user is undefined
let name = user.name        -- Error: user is undefined
in
{ email, name }

-- Error output:
Error: Multiple issues found in configuration

1. Field Error in config.lig:2:15
   Field 'users' not found in config
   Available fields: ['user', 'settings', 'version']
   Suggestion: Use 'config.user' instead of 'config.users'

2. Variable Error in config.lig:3:15
   Variable 'user' is undefined due to previous error
   Context: Accessing email field
   Suggestion: Fix the users field access first

3. Variable Error in config.lig:4:15
   Variable 'user' is undefined due to previous error
   Context: Accessing name field
   Suggestion: Fix the users field access first

4. Type Error in config.lig:5:8
   Expected: { email: String, name: String }
   Found: { email: undefined, name: undefined }
   Suggestion: Ensure all fields are properly defined
```

### Key Improvements Over Jsonnet

#### 1. **Error Accumulation**

- **Jsonnet**: Stops at first error
- **Ligature**: Reports all errors with full context

#### 2. **Type Safety**

- **Jsonnet**: Runtime type errors
- **Ligature**: Compile-time type checking with dependent types

#### 3. **Import Resolution**

- **Jsonnet**: Basic import errors
- **Ligature**: Intelligent suggestions with dependency analysis

#### 4. **Error Recovery**

- **Jsonnet**: No recovery, must fix errors sequentially
- **Ligature**: Continues compilation with error recovery strategies

#### 5. **Context Preservation**

- **Jsonnet**: Minimal error context
- **Ligature**: Full AST-stack mapping with type information

## Conclusion

The register system provides a solid foundation for organizing and distributing Ligature code while maintaining the language's focus on correctness and configuration management. The design prioritizes type safety, explicit dependencies, and minimal complexity while providing the flexibility needed for real-world configuration management scenarios.

The comprehensive error handling system specifically addresses the major weaknesses of Jsonnet and other configuration languages, providing developers with the tools they need to quickly identify and fix issues in their configurations. The error accumulation and smart stack traversal features ensure that users can see all problems at once rather than fixing them one by one.

The implementation plan is structured to deliver value incrementally, starting with core infrastructure and building up to a comprehensive standard library and tooling ecosystem. The error system will be a key differentiator for Ligature, making it significantly more developer-friendly than existing configuration languages.
