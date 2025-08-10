# Constraint-Based Validation Guide

This guide covers Ligature's constraint-based validation system, which allows you to create types with built-in validation rules to ensure data integrity at the type level.

## Table of Contents

1. [Overview](#overview)
2. [Refinement Types](#refinement-types)
3. [Constraint Types](#constraint-types)
4. [Pattern Constraints](#pattern-constraints)
5. [Value Constraints](#value-constraints)
6. [Custom Validation Functions](#custom-validation-functions)
7. [Runtime Validation](#runtime-validation)
8. [Best Practices](#best-practices)
9. [Examples](#examples)

## Overview

Constraint-based validation in Ligature provides a powerful way to ensure data integrity by embedding validation rules directly into type definitions. This approach offers several benefits:

- **Type Safety**: Invalid data is caught at the type level
- **Runtime Validation**: Values are validated when created or assigned
- **Composability**: Constraints can be combined and reused
- **Performance**: Validation is optimized with caching

## Refinement Types

Refinement types create a subset of an existing type based on a predicate function.

### Basic Refinement Types

```ocaml
// Simple refinement type
type PositiveInt = Integer where x > 0;

// Refinement type with complex predicate
type ValidAge = Integer where x >= 0 && x <= 150;

// Refinement type for non-zero values
type NonZero = Integer where x != 0;
```

### Record Refinement Types

```ocaml
// Custom validation function
let isValidUser = \user ->
    length user.name > 0 &&
    user.age >= 0 &&
    user.age <= 150;

// Refinement type for records
type ValidUser = {
    name: String,
    age: Integer
} where isValidUser x;
```

### Using Refinement Types

```ocaml
// Valid values
let age: ValidAge = 25;  // ✅ Valid
let user: ValidUser = { name = "Alice", age = 30 };  // ✅ Valid

// Invalid values (will cause validation errors)
let invalid_age: ValidAge = -5;  // ❌ Validation error
let invalid_user: ValidUser = { name = "", age = 200 };  // ❌ Validation error
```

## Constraint Types

Constraint types allow you to add multiple validation constraints to a base type.

### Pattern Constraints

Pattern constraints validate strings against regular expressions or simple patterns.

#### Regex Pattern Constraints

```ocaml
// Email validation
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");

// Phone number validation
type ValidPhone = String with regexp("^\\d{3}-\\d{3}-\\d{4}$");

// URL validation
type ValidURL = String with regexp("^https?://[^\\s]+$");
```

#### Simple Pattern Constraints

```ocaml
// Simple pattern for phone numbers
type ValidPhone = String with pattern("\\d{3}-\\d{3}-\\d{4}");

// Simple pattern for postal codes
type ValidPostalCode = String with pattern("[A-Z]{2}\\d{5}");
```

### Value Constraints

Value constraints validate values using boolean expressions.

```ocaml
// Numeric range constraints
type ValidPort = Integer with x > 0 && x <= 65535;
type ValidTimeout = Integer with x > 0 && x <= 3600;

// String length constraints
type NonEmptyString = String with length > 0;
type ShortString = String with length <= 100;

// Complex boolean constraints
type ValidConfig = Integer with x > 0 && x <= 65535 && x % 2 == 0;
```

### Multiple Constraints

You can combine multiple constraints on a single type:

```ocaml
// Multiple pattern constraints
type ValidIdentifier = String with regexp("^[a-zA-Z_][a-zA-Z0-9_]*$") with length > 0;

// Pattern and value constraints
type ValidPassword = String with regexp("^[A-Za-z0-9@#$%^&+=]{8,}$") with length >= 8;

// Multiple value constraints
type ValidScore = Integer with x >= 0 && x <= 100 && x % 5 == 0;
```

## Pattern Constraints

### Regex Pattern Syntax

Regex patterns use standard regular expression syntax with some considerations:

```ocaml
// Basic patterns
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
type ValidPhone = String with regexp("^\\d{3}-\\d{3}-\\d{4}$");

// More complex patterns
type ValidUsername = String with regexp("^[a-zA-Z0-9_]{3,20}$");
type ValidHexColor = String with regexp("^#[0-9A-Fa-f]{6}$");
```

### Common Pattern Examples

```ocaml
// Email addresses
type ValidEmail = String with regexp("^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$");

// URLs
type ValidURL = String with regexp("^https?://[^\\s]+$");

// Credit card numbers (basic)
type ValidCreditCard = String with regexp("^\\d{4}-\\d{4}-\\d{4}-\\d{4}$");

// Date format (YYYY-MM-DD)
type ValidDate = String with regexp("^\\d{4}-\\d{2}-\\d{2}$");
```

## Value Constraints

### Numeric Constraints

```ocaml
// Range constraints
type ValidAge = Integer where x >= 0 && x <= 150;
type ValidPort = Integer with x > 0 && x <= 65535;
type ValidPercentage = Integer with x >= 0 && x <= 100;

// Divisibility constraints
type EvenNumber = Integer with x % 2 == 0;
type MultipleOfFive = Integer with x % 5 == 0;

// Complex numeric constraints
type ValidScore = Integer with x >= 0 && x <= 100 && x % 5 == 0;
```

### String Constraints

```ocaml
// Length constraints
type NonEmptyString = String with length > 0;
type ShortString = String with length <= 100;
type MediumString = String with length > 10 && length <= 500;

// Content constraints
type AlphaString = String with regexp("^[A-Za-z]+$");
type NumericString = String with regexp("^\\d+$");
type AlphanumericString = String with regexp("^[A-Za-z0-9]+$");
```

## Custom Validation Functions

For complex validation logic, you can define custom functions and use them in refinement types.

### Simple Validation Functions

```ocaml
// Basic validation function
let isPositive = \x -> x > 0;

// Use in refinement type
type PositiveInt = Integer where isPositive x;
```

### Complex Validation Functions

```ocaml
// Complex user validation
let isValidUser = \user ->
    length user.name > 0 &&
    length user.name <= 50 &&
    user.age >= 0 &&
    user.age <= 150 &&
    contains user.email "@" &&
    length user.email > 5;

// Use in refinement type
type ValidUser = {
    name: String,
    age: Integer,
    email: String
} where isValidUser x;
```

### Validation with Error Messages

```ocaml
// Validation function that returns detailed errors
let validateUser = \user ->
    case (length user.name == 0) of
        true => "Name cannot be empty",
        false => case (user.age < 0) of
            true => "Age cannot be negative",
            false => case (user.age > 150) of
                true => "Age seems unrealistic",
                false => "Valid";

// Use in refinement type (simplified)
let isValidUser = \user -> validateUser user == "Valid";
type ValidUser = { name: String, age: Integer } where isValidUser x;
```

## Runtime Validation

Constraint-based validation occurs at runtime when values are created or assigned.

### Validation Timing

```ocaml
// Validation happens when the value is used
let process_user = \user: ValidUser ->
    // At this point, user is guaranteed to be valid
    "Processing user: " ++ user.name;

// Invalid values cause runtime errors
let invalid_user = { name = "", age = -5 };  // ❌ This would fail validation
```

### Error Handling

```ocaml
// Validation errors are caught at runtime
let safe_create_user = \name age ->
    case (name, age) of
        (n, a) when length n > 0 && a >= 0 && a <= 150 =>
            Some { name = n, age = a },
        _ => None;

// Use the safe creation function
let user_result = safe_create_user "Alice" 25;
```

## Best Practices

### 1. Start Simple

Begin with basic constraints and add complexity as needed:

```ocaml
// Start with simple constraints
type ValidAge = Integer where x >= 0 && x <= 150;

// Add more constraints as needed
type ValidAge = Integer where x >= 0 && x <= 150 && x % 1 == 0;
```

### 2. Use Descriptive Names

Choose clear, descriptive names for your constrained types:

```ocaml
// Good names
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
type ValidPort = Integer with x > 0 && x <= 65535;

// Avoid generic names
type String = String with regexp("^[^@]+@[^@]+\\.[^@]+$");  // ❌ Too generic
```

### 3. Combine Constraints Appropriately

Use multiple constraints when they serve different purposes:

```ocaml
// Good: Different types of constraints
type ValidPassword = String with regexp("^[A-Za-z0-9@#$%^&+=]+$") with length >= 8;

// Avoid: Redundant constraints
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$") with contains "@";  // ❌ Redundant
```

### 4. Test Your Constraints

Always test your constraints with both valid and invalid data:

```ocaml
// Test cases for your constraints
let test_email_constraint = \email ->
    case email of
        "user@example.com" => true,   // ✅ Should pass
        "invalid-email" => false,     // ❌ Should fail
        "" => false,                  // ❌ Should fail
        "user@" => false;             // ❌ Should fail
```

### 5. Performance Considerations

- Use simple constraints when possible
- Avoid complex regex patterns for frequently validated data
- Consider caching for expensive validation functions

## Examples

### Complete User Management System

```ocaml
// user_management.lig
module UserManagement {
    // Constrained types for user data
    type ValidName = String with length > 0 && length <= 50;
    type ValidAge = Integer where x >= 0 && x <= 150;
    type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
    type ValidUserRole = Admin | User | Guest;

    // Custom validation function
    let isValidUser = \user ->
        length user.name > 0 &&
        user.age >= 0 &&
        user.age <= 150 &&
        contains user.email "@";

    // Refinement type for valid users
    type ValidUser = {
        name: ValidName,
        age: ValidAge,
        email: ValidEmail,
        role: ValidUserRole
    } where isValidUser x;

    // User creation function
    let create_user = \name age email role -> {
        name = name,
        age = age,
        email = email,
        role = role
    };

    // Example usage
    let alice = create_user "Alice" 25 "alice@example.com" User;
    let bob = create_user "Bob" 30 "bob@example.com" Admin;
}
```

### Configuration Management

```ocaml
// config_management.lig
module ConfigManagement {
    // Constrained types for configuration
    type ValidPort = Integer where x > 0 && x <= 65535;
    type ValidHost = String with length > 0;
    type ValidTimeout = Integer where x > 0 && x <= 3600;
    type ValidLogLevel = Debug | Info | Warn | Error;

    // Custom validation for configuration
    let isValidConfig = \config ->
        config.port > 0 &&
        config.port <= 65535 &&
        length config.host > 0 &&
        config.timeout > 0 &&
        config.timeout <= 3600;

    // Refinement type for valid configuration
    type ValidConfig = {
        port: ValidPort,
        host: ValidHost,
        timeout: ValidTimeout,
        log_level: ValidLogLevel
    } where isValidConfig x;

    // Environment-specific configurations
    let development_config = {
        port = 8080,
        host = "localhost",
        timeout = 30,
        log_level = Debug
    };

    let production_config = {
        port = 80,
        host = "api.example.com",
        timeout = 60,
        log_level = Info
    };
}
```

### Data Processing Pipeline

```ocaml
// data_processing.lig
module DataProcessing {
    // Constrained types for data processing
    type ValidInput = String with length > 0;
    type ValidOutput = String with length > 0;
    type ValidThreshold = Integer where x >= 0 && x <= 100;

    // Processing function with constrained types
    let process_data = \input: ValidInput threshold: ValidThreshold ->
        case (length input > threshold) of
            true => "Data exceeds threshold",
            false => "Data within threshold";

    // Example usage
    let result1 = process_data "Hello World" 5;
    let result2 = process_data "Short" 10;
}
```

This guide covers the essential aspects of constraint-based validation in Ligature. By using these features, you can create more robust and type-safe applications with built-in data validation.
