# Fix Four Failing Constraint Tests - Focused Prompt

## Problem Summary

**4 specific tests are failing** in the `ligature-parser` crate due to grammar parsing issues with constraint types. The core validation engine works perfectly, but the syntax parsing for constraint types needs immediate fixes.

## Failing Tests

```bash
cargo test -p ligature-parser --lib
# Result: 21 passed, 4 failed

Failed Tests:
1. tests::test_constraint_type_parsing
2. tests::test_custom_constraint_parsing
3. tests::test_multiple_constraints_parsing
4. tests::test_range_constraint_parsing
```

## Error Analysis

### Error Pattern

All failing tests show the same parsing error:

```
ParseError { message: "Parse error: --> 1:XX\n  |\n1 | type ValidEmail = String with regexp(\"...\");\n  |                                      ^---\n  |\n  = expected type_expression", span: ... }
```

**Root Cause**: The `constraint_type` rule is not being recognized in the `type_expression` rule.

## Test Cases to Fix

### Test 1: `test_constraint_type_parsing`

```ligature
type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
```

**Expected**: Parse as `ConstraintType` with `PatternConstraint`
**Error**: Fails at `with` keyword - parser expects `type_expression`

### Test 2: `test_custom_constraint_parsing`

```ligature
type ValidEmail = String with isValidEmail(x);
```

**Expected**: Parse as `ConstraintType` with `CustomConstraint`
**Error**: Fails at `with` keyword - parser expects `type_expression`

### Test 3: `test_range_constraint_parsing`

```ligature
type ValidAge = Int with >= 0 with <= 150;
```

**Expected**: Parse as `ConstraintType` with two `RangeConstraint`s
**Error**: Fails at first `with` keyword - parser expects `type_expression`

### Test 4: `test_multiple_constraints_parsing`

```ligature
type NonEmptyAlpha = String with regexp("^[A-Za-z]+$") with length(x) > 0;
```

**Expected**: Parse as `ConstraintType` with `PatternConstraint` and `ValueConstraint`
**Error**: Fails at first `with` keyword - parser expects `type_expression`

## Current Grammar Issues

### Problem 1: Grammar Rule Not Recognized

```pest
// Current grammar
type_expression = {
    refinement_type |
    constraint_type |  // ← This rule exists but isn't being matched
    constrained_type |
    function_type |
    union_type |
    record_type |
    list_type |
    basic_type |
    type_variable |
    parenthesized_type
}

constraint_type = {
    (basic_type | record_type) ~ "with" ~ WHITESPACE+ ~ constraint_expression
}
```

**Issue**: The `constraint_type` rule is defined but not being matched during parsing.

### Problem 2: Missing Multiple Constraints Support

```pest
// Current: Single constraint only
constraint_type = {
    (basic_type | record_type) ~ "with" ~ WHITESPACE+ ~ constraint_expression
}

// Needed: Multiple constraints
constraint_type = {
    (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
}
```

### Problem 3: Constraint Expression Conflicts

The constraint expressions may be conflicting with `value_expression` rules.

## Required Fixes

### Fix 1: Debug Grammar Rule Recognition

1. **Add debug output** to see which rules are being attempted
2. **Check rule precedence** in `type_expression`
3. **Verify constraint_type rule** is properly defined
4. **Test with minimal constraint syntax**

### Fix 2: Update Grammar for Multiple Constraints

```pest
// Update constraint_type rule
constraint_type = {
    (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
}
```

### Fix 3: Fix Constraint Expression Parsing

```pest
// Make constraint expressions more specific
constraint_expression = {
    range_constraint |
    pattern_constraint |
    custom_constraint |
    value_constraint
}

range_constraint = {
    (">=" ~ WHITESPACE* ~ value_expression) |
    ("<=" ~ WHITESPACE* ~ value_expression)
}

pattern_constraint = {
    ("regexp" | "pattern") ~ "(" ~ string_literal ~ ")"
}

custom_constraint = {
    identifier ~ "(" ~ value_expression ~ ("," ~ value_expression)* ~ ")"
}

value_constraint = {
    value_expression
}
```

### Fix 4: Update Parser Implementation

1. **Update `parse_constraint_type()`** to handle multiple constraints
2. **Fix `parse_constraint_expression()`** to properly parse each type
3. **Update constraint parsing methods** to handle new grammar
4. **Add proper error handling**

## Implementation Steps

### Step 1: Debug Grammar Recognition

```rust
// Add debug output to parser
println!("Attempting to parse: {}", source);
// Check which rules are being attempted
```

### Step 2: Test Minimal Constraint Syntax

```ligature
// Start with simplest possible constraint
type Test = String with regexp("test");
```

### Step 3: Fix Grammar Rule Order

Ensure `constraint_type` is properly ordered in `type_expression`:

```pest
type_expression = {
    refinement_type |
    constraint_type |  // Make sure this is recognized
    constrained_type |
    // ... other rules
}
```

### Step 4: Update Parser Methods

```rust
fn parse_constraint_type(&mut self, pairs: Pairs<Rule>) -> AstResult<Type> {
    // Handle multiple constraints
    let mut constraints = Vec::new();
    // Parse each constraint
    // Return ConstraintType
}
```

### Step 5: Test Each Constraint Type

1. **Pattern constraints**: `regexp("pattern")`
2. **Range constraints**: `>= value`, `<= value`
3. **Custom constraints**: `function(args)`
4. **Value constraints**: `expression`

## Expected Grammar Changes

### Updated Grammar Rules

```pest
// Constraint type with multiple constraints
constraint_type = {
    (basic_type | record_type) ~ ("with" ~ WHITESPACE+ ~ constraint_expression)+
}

// Constraint expressions
constraint_expression = {
    range_constraint |
    pattern_constraint |
    custom_constraint |
    value_constraint
}

// Range constraints
range_constraint = {
    (">=" ~ WHITESPACE* ~ value_expression) |
    ("<=" ~ WHITESPACE* ~ value_expression)
}

// Pattern constraints
pattern_constraint = {
    ("regexp" | "pattern") ~ "(" ~ string_literal ~ ")"
}

// Custom constraints
custom_constraint = {
    identifier ~ "(" ~ value_expression ~ ("," ~ value_expression)* ~ ")"
}

// Value constraints
value_constraint = {
    value_expression
}
```

## Success Criteria

### ✅ **All 4 Tests Passing**

```bash
cargo test -p ligature-parser --lib
# Expected: 25 tests passed, 0 failed
```

### ✅ **Individual Test Results**

```bash
cargo test -p ligature-parser --lib tests::test_constraint_type_parsing
cargo test -p ligature-parser --lib tests::test_custom_constraint_parsing
cargo test -p ligature-parser --lib tests::test_range_constraint_parsing
cargo test -p ligature-parser --lib tests::test_multiple_constraints_parsing
# All should pass
```

### ✅ **No Regressions**

```bash
cargo test -p ligature-parser --lib
# All existing tests should still pass
```

## Debugging Strategy

### 1. **Add Debug Output**

```rust
// In parser.rs, add debug output
println!("Parsing constraint type: {}", source);
println!("Available rules: {:?}", pairs.as_str());
```

### 2. **Test Minimal Cases**

```ligature
// Start with simplest possible syntax
type Test = String with regexp("test");
```

### 3. **Check Rule Precedence**

Ensure `constraint_type` is matched before other rules that might conflict.

### 4. **Verify Grammar Generation**

Check that the Pest grammar is being generated correctly and the `constraint_type` rule is included.

## Implementation Priority

1. **Fix basic constraint_type recognition** (highest priority)
2. **Support multiple constraints** with "with" syntax
3. **Fix individual constraint expression parsing**
4. **Update parser implementation** to handle new grammar
5. **Verify all tests pass**

## Expected Outcome

After implementing these fixes:

- ✅ **All 4 failing tests pass**
- ✅ **Constraint syntax fully supported**
- ✅ **Multiple constraints working**
- ✅ **No regressions in existing functionality**
- ✅ **Complete constraint-based validation system**

This will resolve the only remaining issue in the constraint-based validation implementation and achieve a fully functional system.
