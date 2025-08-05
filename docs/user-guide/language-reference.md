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

```ocaml
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

```ocaml
let, in, fun, type, data, case, of, if, then, else,
import, export, module, typeclass, instance, where,
match, when, Some, None, true, false
```

### Literals

```ocaml
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

```ocaml
Integer    // 64-bit signed integers
Float      // 64-bit floating point
String     // UTF-8 strings
Boolean    // true or false
Unit       // Unit type ()
```

### Function Types

```ocaml
Integer -> String                    // Function from Integer to String
Integer -> Integer -> Integer        // Curried function
(Integer, String) -> Boolean        // Function taking tuple
```

### Record Types

```ocaml
{
    name: String,
    age: Integer,
    email: String
}
```

### Union Types

```ocaml
type Option = Some a | None;
type Result = Success a | Error String;
type List = Cons a (List a) | Nil;
```

### Type Aliases

```ocaml
type UserId = Integer;
```

### Type Variables

```ocaml
'a, 'b, 'c    // Type variables for generic types
```

## Expressions

### Literals

```ocaml
42              // Integer literal
3.14            // Float literal
"Hello"         // String literal
true            // Boolean literal
()              // Unit literal
[1, 2, 3]       // List literal
```

### Variables

```ocaml
x               // Variable reference
user_name       // Variable with underscore
```

### Function Application

```ocaml
f x             // Function application
f x y           // Curried application
f (x, y)        // Tuple application
```

### Lambda Expressions

```ocaml
\x -> x + 1                     // Simple lambda
\x y -> x + y                   // Multi-parameter lambda
\x: Integer -> x * 2            // Typed lambda
```

### Let Expressions

```ocaml
let x = 42 in x + 1             // Simple let
let x = 42; y = 10 in x + y     // Multiple bindings
let rec fact = \n -> if n == 0 then 1 else n * fact (n - 1) in fact 5  // Recursive
```

### If Expressions

```ocaml
if x > 0 then "positive" else "negative"
```

### Match Expressions

```ocaml
match value of
    Some x => x + 1,
    None => 0;
```

### Record Expressions

```ocaml
{
    name = "Alice",
    age = 30,
    email = "alice@example.com"
}
```

### Field Access

```ocaml
user.name       // Access record field
```

### Union Constructors

```ocaml
Some 42         // Union constructor with value
None            // Union constructor without value
```

## Patterns

### Variable Patterns

```ocaml
x               // Bind to variable
```

### Literal Patterns

```ocaml
42              // Match integer literal
"hello"         // Match string literal
true            // Match boolean literal
```

### Constructor Patterns

```ocaml
Some x          // Match union constructor with binding
None            // Match union constructor without binding
```

### Record Patterns

```ocaml
{ name = n, age = a }   // Match record with field bindings
{ name = n, .. }        // Match record with rest pattern
```

### Guard Patterns

```ocaml
x when x > 0    // Pattern with guard condition
```

## Declarations

### Value Declarations

```ocaml
let x = 42;                     // Simple value
let x: Integer = 42;            // Typed value
let rec fact = \n -> if n == 0 then 1 else n * fact (n - 1);  // Recursive
```

### Type Aliases

```ocaml
type UserId = Integer;
type Point = { x: Float, y: Float };
```

### Type Constructors

```ocaml
type Option = Some a | None;
type List = Cons a (List a) | Nil;
```

### Type Classes

```ocaml
typeclass Eq 'a where
    eq : 'a -> 'a -> Bool;

typeclass Ord 'a where
    superclass Eq 'a;
    compare : 'a -> 'a -> Ordering;
```

### Instance Declarations

```ocaml
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

```ocaml
module Math;
```

### Export Declarations

```ocaml
export let add = \x y -> x + y;
export type Point = { x: Float, y: Float };
```

## Type Classes

### Type Class Definition

```ocaml
typeclass Show 'a where
    show : 'a -> String;
```

### Superclasses

```ocaml
typeclass Ord 'a where
    superclass Eq 'a;
    compare : 'a -> 'a -> Ordering;
```

### Method Signatures

```ocaml
typeclass Num 'a where
    add : 'a -> 'a -> 'a;
    multiply : 'a -> 'a -> 'a;
    zero : 'a;
```

### Instance Implementation

```ocaml
instance Show Int where
    show = \x -> toString x;

instance Show Bool where
    show = \b -> if b then "true" else "false";
```

### Constrained Functions

```ocaml
let max : Ord 'a => 'a -> 'a -> 'a = \x y ->
    if compare x y == GT then x else y;
```

## Imports

### Basic Imports

```ocaml
import std.collections.list;
import "./utils";
import "../shared/types";
```

### Aliased Imports

```ocaml
import std.collections as collections;
import "./math" as math;
```

### Selective Imports

```ocaml
import "std.math" { sqrt, pow, log };
import "./utils" { format, parse };
```

### Import Combinations

```ocaml
import "std.collections" as collections { map, filter, fold };
```

## Built-in Functions

### Arithmetic

```ocaml
+ : Integer -> Integer -> Integer
- : Integer -> Integer -> Integer
* : Integer -> Integer -> Integer
/ : Integer -> Integer -> Integer
% : Integer -> Integer -> Integer
```

### Comparison

```ocaml
== : 'a -> 'a -> Bool
!= : 'a -> 'a -> Bool
< : Integer -> Integer -> Bool
<= : Integer -> Integer -> Bool
> : Integer -> Integer -> Bool
>= : Integer -> Integer -> Bool
```

### Logical

```ocaml
&& : Bool -> Bool -> Bool
|| : Bool -> Bool -> Bool
! : Bool -> Bool
```

### String

```ocaml
++ : String -> String -> String
toString : Integer -> String
parseInt : String -> Option Integer
```

### List

```ocaml
head : List 'a -> Option 'a
tail : List 'a -> Option (List 'a)
length : List 'a -> Integer
append : List 'a -> List 'a -> List 'a
```

### Control Flow

```ocaml
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

```ocaml
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
