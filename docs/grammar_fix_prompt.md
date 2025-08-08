# Grammar Fix Prompt: Resolve Constraint Type Parsing Issues

## Problem Statement

The constraint-based validation system has been successfully implemented with a working runtime validation engine, but there are **4 failing parser tests** due to grammar conflicts in the Pest grammar. The core validation functionality works correctly, but the syntax parsing for constraint types needs to be fixed.

## Current Status

### ✅ **Working Components**

- Runtime validation engine (Phase 3) - 50 tests passing
- Type system integration (Phase 1) - 85 tests passing
- Integration tests (Phase 4) - 20 tests passing
- Runtime validation example - Working perfectly

### ❌ **Failing Tests**

```bash
cargo test -p ligature-parser --lib
# Result: 21 passed, 4 failed

Failed Tests:
- test_constraint_type_parsing
- test_multiple_constraints_parsing
- test_range_constraint_parsing
- test_custom_constraint_parsing
```

## Error Analysis

### Error Patterns

All failing tests show similar parsing errors:

```
ParseError { message: "Parse error: --> 1:XX\n  |\n1 | type ValidEmail = String with regexp(\"...\");\n  |                                      ^---\n  |\n  = expected type_expression", span: ... }
```

### Root Cause

The grammar rule `constraint_type` is not being recognized in the `type_expression` rule, causing the parser to fail when encountering constraint syntax.

## Current Grammar Structure

### Relevant Grammar Rules

```pest
// Type expressions
type_expression = {
    refinement_type |
    constraint_type |  // ← This should work but isn't
    constrained_type |
    function_type |
    union_type |
    record_type |
    list_type |
    basic_type |
    type_variable |
    parenthesized_type
}

// Constraint type: type T = BaseType with constraint
constraint_type = {
    (basic_type | record_type) ~ "with" ~ WHITESPACE+ ~ constraint_expression
}

// Constraint expressions for constraint types
constraint_expression = {
    range_constraint |
    pattern_constraint |
    custom_constraint |
    value_constraint
}
```

## Test Cases to Fix

### 1. Basic Constraint Type Parsing

```ligature
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
```

**Expected**: Parse as `ConstraintType` with `PatternConstraint`

### 2. Range Constraint Parsing

```ligature
type ValidAge = Int with >= 0 with <= 150;
```

**Expected**: Parse as `ConstraintType` with two `RangeConstraint`s

### 3. Custom Constraint Parsing

```ligature
type ValidEmail = String with isValidEmail(x);
```

**Expected**: Parse as `ConstraintType` with `CustomConstraint`

### 4. Multiple Constraints Parsing

```ligature
type NonEmptyAlpha = String with regexp("^[A-Za-z]+$") with length(x) > 0;
```

**Expected**: Parse as `ConstraintType` with `PatternConstraint` and `ValueConstraint`

## Required Fixes

### 1. **Grammar Rule Conflicts**

The main issue is that the `constraint_type` rule is not being properly recognized. This could be due to:

- **Operator precedence conflicts** with `value_expression`
- **Ambiguous parsing** between constraint syntax and other expressions
- **Missing whitespace handling** in constraint rules

### 2. **Multiple Constraints Support**

The current grammar only supports single constraints:

```pest
constraint_type = {
    (basic_type | record_type) ~ "with" ~ WHITESPACE+ ~ constraint_expression
}
```

**Needs to support**:

```pest
constraint_type = {
    (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
}
```

### 3. **Constraint Expression Parsing**

The constraint expressions need to be more specific to avoid conflicts:

- **Range constraints**: `>= value` and `<= value`
- **Pattern constraints**: `regexp("pattern")` and `pattern("pattern")`
- **Custom constraints**: `function_name(arguments)`
- **Value constraints**: Any boolean expression

## Implementation Tasks

### Task 1: Fix Grammar Rule Conflicts

1. **Analyze operator precedence** in `value_expression` vs `constraint_expression`
2. **Resolve ambiguous parsing** between constraint syntax and expressions
3. **Add proper whitespace handling** in constraint rules
4. **Ensure constraint_type is properly recognized** in type_expression

### Task 2: Support Multiple Constraints

1. **Update constraint_type rule** to support multiple constraints:
   ```pest
   constraint_type = {
       (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
   }
   ```

### Task 3: Fix Constraint Expression Parsing

1. **Make constraint expressions more specific** to avoid conflicts
2. **Ensure proper parsing** of each constraint type:
   - Range constraints with `>=` and `<=`
   - Pattern constraints with `regexp()` and `pattern()`
   - Custom constraints with function calls
   - Value constraints with boolean expressions

### Task 4: Update Parser Implementation

1. **Update parse_constraint_type()** method to handle multiple constraints
2. **Fix parse_constraint_expression()** to properly parse each constraint type
3. **Update parse_range_constraint()** and parse_pattern_constraint() methods
4. **Ensure proper error handling** for malformed constraint syntax

### Task 5: Verify Test Fixes

1. **Run the failing tests** to verify they now pass
2. **Add additional test cases** for edge cases
3. **Ensure no regressions** in existing functionality

## Expected Grammar Changes

### Updated Constraint Type Rule

```pest
// Constraint type: type T = BaseType with constraint1 with constraint2 ...
constraint_type = {
    (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
}

// Constraint expressions for constraint types
constraint_expression = {
    range_constraint |
    pattern_constraint |
    custom_constraint |
    value_constraint
}

// Range constraint: >= value, <= value
range_constraint = {
    (">=" ~ WHITESPACE* ~ value_expression) |
    ("<=" ~ WHITESPACE* ~ value_expression)
}

// Pattern constraint: regexp("pattern") or pattern("pattern")
pattern_constraint = {
    ("regexp" | "pattern") ~ "(" ~ string_literal ~ ")"
}

// Custom constraint: function_name(arg1, arg2, ...)
custom_constraint = {
    identifier ~ "(" ~ value_expression ~ ("," ~ value_expression)* ~ ")"
}

// Value constraint: any expression that evaluates to a boolean
value_constraint = {
    value_expression
}
```

## Success Criteria

### ✅ **All Tests Passing**

```bash
cargo test -p ligature-parser --lib
# Expected: 25 tests passed, 0 failed
```

### ✅ **Runtime Validation Working**

```bash
cargo run --example runtime_validation_example
# Expected: All validation examples working
```

### ✅ **Integration Tests Passing**

```bash
cargo test -p ligature-eval --lib
# Expected: 50 tests passed, 0 failed
```

## Implementation Notes

### Priority Order

1. **Fix basic constraint_type recognition** in type_expression
2. **Support multiple constraints** with "with" syntax
3. **Fix individual constraint expression parsing**
4. **Update parser implementation** to handle new grammar
5. **Verify all tests pass**

### Testing Strategy

1. **Start with simple constraint types** (single constraint)
2. **Add multiple constraints** support
3. **Test each constraint type** individually
4. **Test complex combinations** of constraints
5. **Verify no regressions** in existing functionality

### Error Handling

- **Graceful parsing errors** for malformed constraint syntax
- **Clear error messages** indicating what was expected
- **Proper span information** for error reporting

## Expected Outcome

After implementing these fixes, the constraint-based validation system will have:

- ✅ **Complete syntax support** for all constraint types
- ✅ **Multiple constraint support** with "with" syntax
- ✅ **All parser tests passing**
- ✅ **Full integration** with runtime validation engine
- ✅ **Production-ready** constraint-based validation system

This will complete the implementation and resolve the only remaining issue in the constraint-based validation system.
