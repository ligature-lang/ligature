# Error Messages Guide

This guide helps you understand and debug error messages in Ligature. Each error type includes examples, explanations, and solutions.

## Table of Contents

1. [Parse Errors](#parse-errors)
2. [Type Errors](#type-errors)
3. [Evaluation Errors](#evaluation-errors)
4. [Module Errors](#module-errors)
5. [Pattern Matching Errors](#pattern-matching-errors)
6. [Common Debugging Techniques](#common-debugging-techniques)

## Parse Errors

Parse errors occur when the Ligature parser cannot understand your code syntax.

### Unexpected Token

**Error**: `Unexpected token '}' at line 5, column 10`

**Example**:

```ocaml
let x = 42;
let y = {
    value = x
}; // Missing closing brace
```

**Solution**: Check for missing or mismatched brackets, braces, and parentheses.

### Missing Semicolon

**Error**: `Expected ';' after declaration at line 3, column 15`

**Example**:

```ocaml
let x = 42
let y = x + 1; // Missing semicolon after x declaration
```

**Solution**: Add semicolons after value declarations.

### Invalid Identifier

**Error**: `Invalid identifier '123abc' at line 2, column 5`

**Example**:

```ocaml
let 123abc = 42; // Identifiers cannot start with numbers
```

**Solution**: Use valid identifiers that start with letters or underscores.

### Unterminated String

**Error**: `Unterminated string literal at line 1, column 10`

**Example**:

```ocaml
let message = "Hello, world; // Missing closing quote
```

**Solution**: Ensure all strings are properly closed with matching quotes.

## Type Errors

Type errors occur when the type checker finds inconsistencies in your code.

### Type Mismatch

**Error**: `Type mismatch: expected Integer, found String at line 3, column 15`

**Example**:

```ocaml
let x: Integer = "hello"; // Cannot assign String to Integer
```

**Solution**: Ensure values match their declared types or use type conversion functions.

### Function Type Mismatch

**Error**: `Function expects Integer -> Integer, but received Integer -> String at line 5, column 10`

**Example**:

```ocaml
let add: Integer -> Integer -> Integer = \x y -> x + y;
let result = add 5 "hello"; // Second argument should be Integer
```

**Solution**: Check function signatures and argument types.

### Missing Type Annotation

**Error**: `Cannot infer type for 'complex_expression' at line 10, column 5`

**Example**:

```ocaml
let complex_expression = \x ->
    if x > 0 then "positive"
    else if x < 0 then "negative"
    else "zero"; // Type checker cannot determine return type
```

**Solution**: Add explicit type annotations for complex expressions.

### Record Field Mismatch

**Error**: `Record missing required field 'age' at line 8, column 5`

**Example**:

```ocaml
type User = {
    name: String,
    age: Integer
};

let user = {
    name = "Alice" // Missing age field
};
```

**Solution**: Ensure all required record fields are provided.

## Evaluation Errors

Evaluation errors occur during program execution.

### Division by Zero

**Error**: `Division by zero at line 5, column 15`

**Example**:

```ocaml
let x = 10;
let y = 0;
let result = x / y; // Division by zero
```

**Solution**: Add checks for zero values before division.

### Undefined Variable

**Error**: `Undefined variable 'undefined_var' at line 7, column 10`

**Example**:

```ocaml
let x = 42;
let y = x + undefined_var; // Variable not defined
```

**Solution**: Ensure all variables are defined before use.

### Record Field Access Error

**Error**: `Record has no field 'nonexistent' at line 4, column 10`

**Example**:

```ocaml
let user = {
    name = "Alice",
    age = 30
};
let field = user.nonexistent; // Field doesn't exist
```

**Solution**: Check record field names and ensure they exist.

### Pattern Match Exhaustiveness

**Error**: `Pattern match is not exhaustive at line 8, column 5`

**Example**:

```ocaml
type Option = Some a | None;

let get_value = \option -> match option of
    Some value => value; // Missing None case
```

**Solution**: Add cases for all possible pattern variants.

## Module Errors

Module errors occur when working with imports, exports, and module definitions.

### Module Not Found

**Error**: `Module 'NonExistentModule' not found at line 3, column 8`

**Example**:

```ocaml
import NonExistentModule; // Module doesn't exist
```

**Solution**: Check module names and ensure modules are properly defined.

### Import Error

**Error**: `Cannot import 'private_function' from module 'Math' at line 5, column 8`

**Example**:

```ocaml
import Math { private_function }; // Function not exported
```

**Solution**: Ensure imported items are properly exported from the module.

### Circular Import

**Error**: `Circular import detected: ModuleA -> ModuleB -> ModuleA at line 1, column 1`

**Example**:

```ocaml
// ModuleA.lig
import ModuleB;

// ModuleB.lig
import ModuleA; // Circular dependency
```

**Solution**: Restructure modules to avoid circular dependencies.

### Export Error

**Error**: `Cannot export 'undefined_item' at line 10, column 5`

**Example**:

```ocaml
module MyModule {
    let public_function = \x -> x + 1;
    export { public_function, undefined_item }; // Item not defined
}
```

**Solution**: Ensure all exported items are defined in the module.

## Pattern Matching Errors

Pattern matching errors occur when patterns are invalid or incomplete.

### Pattern Guard Error

**Error**: `Pattern guard must evaluate to Boolean at line 6, column 15`

**Example**:

```ocaml
let classify = \x -> match x of
    n when n + 1 => "positive", // Guard should return Boolean
    _ => "other";
```

**Solution**: Ensure pattern guards return Boolean values.

### Variable Binding Error

**Error**: `Variable 'x' bound multiple times in pattern at line 4, column 10`

**Example**:

```ocaml
let duplicate = \pair -> match pair of
    (x, x) => x, // Variable x bound twice
    _ => 0;
```

**Solution**: Use different variable names for different bindings.

### Union Pattern Error

**Error**: `Union pattern 'Some' expects 1 argument at line 5, column 10`

**Example**:

```ocaml
type Option = Some a | None;

let get_value = \option -> match option of
    Some => 0, // Missing argument
    None => 0;
```

**Solution**: Provide the correct number of arguments for union patterns.

## Common Debugging Techniques

### 1. Use Type Annotations

Add explicit type annotations to help identify type issues:

```ocaml
// Instead of:
let add = \x y -> x + y;

// Use:
let add: Integer -> Integer -> Integer = \x y -> x + y;
```

### 2. Break Down Complex Expressions

Split complex expressions into smaller parts:

```ocaml
// Instead of:
let result = complex_function (another_function (third_function x));

// Use:
let step1 = third_function x;
let step2 = another_function step1;
let result = complex_function step2;
```

### 3. Use Pattern Guards for Debugging

Add pattern guards to understand data flow:

```ocaml
let debug_function = \x -> match x of
    value when trace "Debug value" value => process value,
    _ => default_value;
```

### 4. Check Module Imports

Verify module imports are correct:

```ocaml
// Check that the module exists and exports the function
import Math { add, subtract }; // Ensure add and subtract are exported
```

### 5. Validate Record Structures

Ensure record structures match their types:

```ocaml
type User = {
    name: String,
    age: Integer,
    email: String
};

// Make sure all fields are present and have correct types
let user: User = {
    name = "Alice",
    age = 30,
    email = "alice@example.com"
};
```

### 6. Test Pattern Matching Exhaustiveness

Add wildcard patterns to catch missing cases:

```ocaml
let safe_match = \option -> match option of
    Some value => value,
    None => 0,
    _ => 0; // Catch any unexpected cases during development
```

## Error Message Format

Ligature error messages follow this format:

```
Error Type: Description at line X, column Y
```

Where:

- **Error Type**: The category of error (Parse, Type, Evaluation, etc.)
- **Description**: Human-readable explanation of the problem
- **Line X, column Y**: Exact location of the error in the source code

## Getting Help

If you encounter an error not covered in this guide:

1. **Check the error location**: Look at the line and column numbers
2. **Read the error description**: It often contains hints about the solution
3. **Simplify the code**: Try to reproduce the error with a minimal example
4. **Check the documentation**: Refer to the language reference for syntax rules
5. **Ask for help**: Use the project's issue tracker or discussions

## Common Patterns

### Safe Division

```ocaml
let safe_divide = \x y -> match y of
    0 => None,
    _ => Some (x / y);
```

### Safe Record Access

```ocaml
let get_field = \record field_name -> match field_name of
    "name" => Some record.name,
    "age" => Some record.age,
    _ => None;
```

### Exhaustive Pattern Matching

```ocaml
let handle_result = \result -> match result of
    Success value => "Success: " ++ toString value,
    Error message => "Error: " ++ message,
    _ => "Unknown result"; // Always include catch-all
```

These patterns help prevent common runtime errors and make your code more robust.
