# Ligature Language Specification

This directory contains the formal specification of the Ligature language in Lean 4.

## Overview

Ligature is a dependently-typed configuration language designed with correctness and safety as primary goals. This specification provides a formal foundation for the language, ensuring type safety, termination, and correctness.

## Specification Files

### Core Specification

- **`Ligature.lean`** - Main specification file containing:
  - Syntax definitions (expressions, types, patterns)
  - Type system and type checking rules
  - Operational semantics and evaluation
  - Type safety theorems
  - Basic examples and test cases

### Type System

- **`TypeSystem.lean`** - Detailed type system specification including:
  - Type inference rules
  - Subtyping relations
  - Dependent types (Pi and Sigma types)
  - Type-level computation
  - Type safety properties

### Operational Semantics

- **`OperationalSemantics.lean`** - Operational semantics specification including:
  - Step-by-step reduction rules
  - Environment-based evaluation
  - Evaluation contexts
  - Termination and determinism properties
  - Multi-step reduction

### Configuration Language

- **`ConfigurationLanguage.lean`** - Configuration-specific features including:
  - Configuration validation rules
  - Constraint satisfaction
  - Schema definitions
  - Configuration merging and inheritance
  - Environment variable substitution

## Key Features

### Type Safety
- Strong static typing with type inference
- Dependent types for precise specifications
- Subtyping for records and unions
- Type-level computation capabilities

### Termination
- All well-typed expressions are guaranteed to terminate
- No arbitrary recursion or loops
- Strong normalization property

### Configuration Focus
- Rich validation and constraint system
- Schema-based configuration validation
- Configuration merging and inheritance
- Environment variable substitution

### Correctness Guarantees
- Formal proofs of type safety
- Deterministic evaluation
- Sound type inference
- Complete error reporting

## Using the Specification

### Prerequisites

To work with this specification, you need:

1. **Lean 4** - Install from [leanprover.github.io](https://leanprover.github.io/)
2. **Mathlib** - The Lean 4 mathematical library
3. **A Lean 4 IDE** - VS Code with the Lean extension or similar

### Building the Specification

```bash
# Navigate to the spec directory
cd spec

# Build the specification
lake build

# Check all files
lake check
```

### Running Examples

```bash
# Run specific examples
lake exe Ligature
lake exe TypeSystem
lake exe OperationalSemantics
lake exe ConfigurationLanguage
```

### Interactive Development

```bash
# Start Lean server
lake serve

# Open in VS Code with Lean extension
code .
```

## Specification Structure

### Syntax Definitions

The specification defines the abstract syntax of Ligature:

```lean
inductive Expr where
  | literal : Literal → Expr
  | variable : Name → Expr
  | application : Expr → Expr → Expr
  | abstraction : Name → Option Type → Expr → Expr
  | let : Name → Expr → Expr → Expr
  | record : List (Name × Expr) → Expr
  | fieldAccess : Expr → Name → Expr
  | union : Name → Option Expr → Expr
  | match : Expr → List (Pattern × Expr) → Expr
  | if : Expr → Expr → Expr → Expr
  | binaryOp : BinaryOperator → Expr → Expr → Expr
  | unaryOp : UnaryOperator → Expr → Expr
  | annotated : Expr → Type → Expr
```

### Type System

The type system includes:

- Basic types (unit, bool, string, integer, float)
- Function types
- Record types
- Union types
- Dependent types (Pi and Sigma types)
- Universal and existential quantification

### Operational Semantics

The operational semantics defines:

- Small-step reduction rules
- Environment-based evaluation
- Pattern matching
- Function application (beta reduction)
- Record and union operations

### Configuration Features

Configuration-specific features include:

- Schema validation
- Constraint satisfaction
- Configuration merging
- Environment variable substitution
- Error reporting

## Theorems and Properties

### Type Safety

```lean
theorem typeSafety (e : Expr) (τ : Type) (h : TypeCheck [] e τ) : 
  ∃ v, Eval e v
```

### Termination

```lean
theorem termination (e : Expr) (τ : Type) (h : TypeCheck [] e τ) : 
  ∃ v, Eval e v
```

### Determinism

```lean
theorem determinism (e : Expr) (v₁ v₂ : Value) (h₁ : Eval e v₁) (h₂ : Eval e v₂) : 
  v₁ = v₂
```

## Examples

### Simple Addition

```lean
def exampleAdd : Expr := 
  Expr.binaryOp BinaryOperator.add 
    (Expr.literal (Literal.integer 5)) 
    (Expr.literal (Literal.integer 3))

theorem exampleAddType : TypeCheck [] exampleAdd Type.integer
theorem exampleAddEval : Eval exampleAdd (Value.literal (Literal.integer 8))
```

### Record Construction

```lean
def exampleRecord : Expr := 
  Expr.record [
    ("name", Expr.literal (Literal.string "Alice")),
    ("age", Expr.literal (Literal.integer 30))
  ]

theorem exampleRecordType : TypeCheck [] exampleRecord (Type.record [
  ("name", Type.string),
  ("age", Type.integer)
])
```

### Configuration Validation

```lean
def serverSchema : Schema := {
  fields := [
    ("host", { type := Type.string, required := true, ... }),
    ("port", { type := Type.integer, required := true, ... }),
    ("timeout", { type := Type.integer, required := false, ... })
  ]
}

theorem validServerConfigValidates : SchemaValidate [] validServerConfig serverSchema
```

## Contributing

When contributing to the specification:

1. **Follow Lean 4 conventions** - Use standard Lean 4 syntax and style
2. **Add proofs** - Provide formal proofs for all theorems
3. **Include examples** - Add concrete examples demonstrating features
4. **Update documentation** - Keep this README and comments up to date
5. **Test thoroughly** - Ensure all examples and theorems check successfully

## Relationship to Implementation

This specification serves as the formal foundation for the Rust implementation in the `crates/` directory. The implementation should:

1. **Follow the specification** - Implement the semantics defined here
2. **Maintain correctness** - Ensure type safety and termination properties
3. **Provide good error messages** - Help users understand type errors
4. **Support incremental development** - Allow for gradual feature implementation

## Future Work

Areas for future development:

1. **Complete proofs** - Fill in the `sorry` placeholders with formal proofs
2. **Extended examples** - Add more comprehensive examples
3. **Performance properties** - Formalize complexity bounds
4. **Language extensions** - Specify additional features
5. **Tool integration** - Formalize IDE and tooling semantics

## References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Type Theory and Formal Proof](https://www.cis.upenn.edu/~bcpierce/tapl/)
- [Dependent Types at Work](https://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf) 