# Ligature Language Reference

This document provides a comprehensive reference for the Ligature language syntax and semantics.

## Table of Contents

1. [Lexical Structure](#lexical-structure)
2. [Types](#types)
3. [Expressions](#expressions)
4. [Patterns](#patterns)
5. [Declarations](#declarations)
6. [Modules](#modules)
7. [Type Classes](#type-classes)
8. [Imports](#imports)
9. [Built-in Functions](#built-in-functions)

## Lexical Structure

### Comments

```ligature
// Single-line comment
/* Multi-line
   comment */
```

### Identifiers

- Start with a letter or underscore
- Can contain letters, digits, and underscores
- Case-sensitive
- Examples: `x`, `user_name`, `_private`

### Keywords

```ligature
let, in, fun, type, data, case, of, if, then, else,
import, export, module, typeclass, instance, where,
match, when, Some, None, true, false
```

### Literals

```ligature
// Integers
42, -17, 0

// Floats
3.14, -2.5, 0.0

// Strings
"Hello, World!", "Multi-line\nstring"

// Booleans
true, false

// Unit
()

// Lists
[1, 2, 3], ["a", "b", "c"]
```

## Types

### Basic Types

```ligature
Integer    // 64-bit signed integers
Float      // 64-bit floating point
String     // UTF-8 strings
Boolean    // true or false
Unit       // Unit type ()
```

### Function Types

```ligature
Integer -> String                    // Function from Integer to String
Integer -> Integer -> Integer        // Curried function
(Integer, String) -> Boolean        // Function taking tuple
```

### Record Types

```ligature
{
    name: String,
    age: Integer,
    email: String
}
```

### Union Types

```ligature
type Option = Some a | None;
type Result = Success a | Error String;
type List = Cons a (List a) | Nil;
```

### Type Aliases

```ligature
type UserId = Integer;
```

### Type Variables

```ligature
'a, 'b, 'c    // Type variables for generic types
```

## Expressions

### Literals

```ligature
42              // Integer literal
3.14            // Float literal
"Hello"         // String literal
true            // Boolean literal
()              // Unit literal
[1, 2, 3]       // List literal
```

### Variables

```ligature
x               // Variable reference
user_name       // Variable with underscore
```

### Function Application

```ligature
f x             // Function application
f x y           // Curried application
f (x, y)        // Tuple application
```

### Lambda Expressions

```ligature
\x -> x + 1                     // Simple lambda
\x y -> x + y                   // Multi-parameter lambda
\x: Integer -> x * 2            // Typed lambda
```

### Let Expressions

```ligature
let x = 42 in x + 1             // Simple let
let x = 42; y = 10 in x + y     // Multiple bindings
let rec fact = \n -> if n == 0 then 1 else n * fact (n - 1) in fact 5  // Recursive
```

### If Expressions

```ligature
if x > 0 then "positive" else "negative"
```

### Match Expressions

```ligature
match value of
    Some x => x + 1,
    None => 0;
```

### Record Expressions

```ligature
{
    name = "Alice",
    age = 30,
    email = "alice@example.com"
}
```

### Field Access

```ligature
user.name       // Access record field
```

### Union Constructors

```ligature
Some 42         // Union constructor with value
None            // Union constructor without value
```

## Patterns

### Variable Patterns

```ligature
x               // Bind to variable
```

### Literal Patterns

```ligature
42              // Match integer literal
"hello"         // Match string literal
true            // Match boolean literal
```

### Constructor Patterns

```ligature
Some x          // Match union constructor with binding
None            // Match union constructor without binding
```

### Record Patterns

```ligature
{ name = n, age = a }   // Match record with field bindings
{ name = n, .. }        // Match record with rest pattern
```

### Guard Patterns

```ligature
x when x > 0    // Pattern with guard condition
```

## Declarations

### Value Declarations

```ligature
let x = 42;                     // Simple value
let x: Integer = 42;            // Typed value
let rec fact = \n -> if n == 0 then 1 else n * fact (n - 1);  // Recursive
```

### Type Aliases

```ligature
type UserId = Integer;
type Point = { x: Float, y: Float };
```

### Type Constructors

```ligature
type Option = Some a | None;
type List = Cons a (List a) | Nil;
```

### Type Classes

```ligature
typeclass Eq 'a where
    eq : 'a -> 'a -> Bool;

typeclass Ord 'a where
    superclass Eq 'a;
    compare : 'a -> 'a -> Ordering;
```

### Instance Declarations

```ligature
// Simple instance
instance Eq Int where
    eq = \x y -> x == y;

// Instance with type arguments
instance Eq(Int) where
    eq = \x y -> x == y;

// Constrained instance
instance (Eq 'a, Eq 'b) => Eq (Pair 'a 'b) where
    eq = \p1 p2 -> eq p1.first p2.first && eq p1.second p2.second;
```

## Modules

### Module Declaration

```ligature
module Math;
```

### Export Declarations

```ligature
export let add = \x y -> x + y;
export type Point = { x: Float, y: Float };
```

## Type Classes

### Type Class Definition

```ligature
typeclass Show 'a where
    show : 'a -> String;
```

### Superclasses

```ligature
typeclass Ord 'a where
    superclass Eq 'a;
    compare : 'a -> 'a -> Ordering;
```

### Method Signatures

```ligature
typeclass Num 'a where
    add : 'a -> 'a -> 'a;
    multiply : 'a -> 'a -> 'a;
    zero : 'a;
```

### Instance Implementation

```ligature
instance Show Int where
    show = \x -> toString x;

instance Show Bool where
    show = \b -> if b then "true" else "false";
```

### Constrained Functions

```ligature
let max : Ord 'a => 'a -> 'a -> 'a = \x y -> 
    if compare x y == GT then x else y;
```

## Imports

### Basic Imports

```ligature
import std.collections.list;
import "./utils";
import "../shared/types";
```

### Aliased Imports

```ligature
import std.collections as collections;
import "./math" as math;
```

### Selective Imports

```ligature
import "std.math" { sqrt, pow, log };
import "./utils" { format, parse };
```

### Import Combinations

```ligature
import "std.collections" as collections { map, filter, fold };
```

## Built-in Functions

### Arithmetic

```ligature
+ : Integer -> Integer -> Integer
- : Integer -> Integer -> Integer
* : Integer -> Integer -> Integer
/ : Integer -> Integer -> Integer
% : Integer -> Integer -> Integer
```

### Comparison

```ligature
== : 'a -> 'a -> Bool
!= : 'a -> 'a -> Bool
< : Integer -> Integer -> Bool
<= : Integer -> Integer -> Bool
> : Integer -> Integer -> Bool
>= : Integer -> Integer -> Bool
```

### Logical

```ligature
&& : Bool -> Bool -> Bool
|| : Bool -> Bool -> Bool
! : Bool -> Bool
```

### String

```ligature
++ : String -> String -> String
toString : Integer -> String
parseInt : String -> Option Integer
```

### List

```ligature
head : List 'a -> Option 'a
tail : List 'a -> Option (List 'a)
length : List 'a -> Integer
append : List 'a -> List 'a -> List 'a
```

### Control Flow

```ligature
if : Bool -> 'a -> 'a -> 'a
```

## Operator Precedence

1. **Function application** (highest)
2. **Unary operators** (`!`, `-`)
3. **Multiplicative** (`*`, `/`, `%`)
4. **Additive** (`+`, `-`)
5. **Comparison** (`<`, `<=`, `>`, `>=`)
6. **Equality** (`==`, `!=`)
7. **Logical AND** (`&&`)
8. **Logical OR** (`||`)
9. **Function arrows** (`->`) (lowest)

## Type Inference

Ligature uses Hindley-Milner type inference with the following features:

- **Automatic type inference** for most expressions
- **Type annotations** for explicit typing
- **Type class constraints** for polymorphic functions
- **Type variable generalization** and instantiation
- **Unification** for type checking

## Module System

### Module Structure

```ligature
module MyModule;

import std.collections.list;

export let my_function = \x -> x + 1;
export type MyType = { name: String, value: Integer };

let internal_function = \x -> x * 2;  // Not exported
```

### Import Resolution

- **Relative imports**: `./` and `../` for local modules
- **Register imports**: `std.collections.list` for standard library
- **Workspace imports**: Automatic discovery of modules in workspace
- **Cycle detection**: Prevents infinite import loops
- **Module caching**: Efficient loading and caching

### Cross-Module Features

- **Go to definition** across module boundaries
- **Find references** across entire workspace
- **Completion** from imported modules
- **Type checking** across module boundaries 