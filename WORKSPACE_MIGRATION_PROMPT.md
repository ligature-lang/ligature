# Workspace Migration Error Resolution Prompt

## Overview

The `ligature-types` crate has been successfully migrated to use the new AST structure and error handling standardization. However, several workspace crates still have compilation errors due to the AST changes. This prompt provides a systematic approach to resolve these remaining issues.

## Current Error Status

✅ **ligature-types**: Successfully migrated and compiles without errors  
❌ **cacophony**: 6 compilation errors - AST structure access issues  
❌ **keywork**: 1 compilation error - type mismatch in module checking  
❌ **krox**: 2 compilation errors - error type mismatches

## Error Categories and Solutions

### 1. AST Structure Access Issues (cacophony)

**Problem**: The `cacophony` app is still using the old `ligature_ast::Declaration` structure directly instead of the new API.

**Errors**:

- `use of unresolved module or unlinked crate 'ligature_ast'`
- Incorrect pattern matching on `Declaration::Let`

**Solution**:

1. **Update imports**: Replace `ligature_ast` imports with `ligature_parser` where appropriate
2. **Update Declaration access**: Change from direct `Declaration` pattern matching to using the new `DeclarationKind` API
3. **Update pattern matching**: Replace `Declaration::Let { name, .. }` with `DeclarationKind::Value` patterns

**Required Changes**:

```rust
// Before
use ligature_ast::Declaration;
match decl {
    ligature_ast::Declaration::Let { name, .. } => { ... }
}

// After
use ligature_parser::Declaration;
match &decl.kind {
    ligature_ast::DeclarationKind::Value { name, .. } => { ... }
}
```

### 2. Type Mismatch Issues (keywork)

**Problem**: The `keywork` app is passing a `Program` to a method expecting a `Module`.

**Error**: `expected &Module, found &Program`

**Solution**:

1. **Check the API**: Verify what the `check_module` method expects
2. **Convert or extract**: Either convert `Program` to `Module` or extract the module from the program
3. **Update method call**: Use the correct method or data structure

### 3. Error Type Mismatches (krox)

**Problem**: The `krox` crate has error type mismatches between `StandardError` and `LigatureError`.

**Errors**:

- `expected function signature fn(StandardError) -> _, found function signature fn(LigatureError) -> _`

**Solution**:

1. **Update error handling**: Ensure consistent use of `StandardError` throughout
2. **Fix map_err calls**: Update error conversion in `map_err` calls
3. **Update error types**: Align error types with the standardized error handling

## Implementation Steps

### Step 1: Fix cacophony AST Issues

**File**: `apps/cacophony/src/main.rs`

**Changes needed**:

1. Update imports to use `ligature_parser` instead of `ligature_ast` where appropriate
2. Update function signatures to use correct types
3. Update pattern matching to use `DeclarationKind` API
4. Fix all `Declaration::Let` patterns to use `DeclarationKind::Value`

**Specific fixes**:

```rust
// Line 125: Update function signature
fn validate_configuration(program: &ligature_parser::Program) -> Result<()> {

// Line 133: Update function signature
fn validate_declaration(decl: &ligature_parser::Declaration) -> Result<()> {

// Line 136: Update pattern matching
match &decl.kind {
    ligature_ast::DeclarationKind::Value { name, .. } => {

// Line 146: Update function signature
fn apply_configuration(program: &ligature_parser::Program) -> Result<()> {

// Line 154: Update function signature
fn apply_declaration(decl: &ligature_parser::Declaration) -> Result<()> {

// Line 157: Update pattern matching
match &decl.kind {
    ligature_ast::DeclarationKind::Value { name, value, .. } => {
```

### Step 2: Fix keywork Type Mismatch

**File**: `apps/keywork/src/register.rs`

**Issue**: Line 249 - passing `Program` to `check_module` expecting `Module`

**Solution**: Either:

1. Extract the module from the program, or
2. Use a different method that accepts `Program`, or
3. Convert the `Program` to a `Module` structure

### Step 3: Fix krox Error Type Issues

**File**: `krox/src/executor.rs`

**Issues**: Lines 245 and 251 - error type mismatches

**Changes needed**:

```rust
// Line 245: Fix error conversion
let program = parse_program(source).map_err(|e| Error::Parse(e.into()))?;

// Line 251: Fix error conversion
ligature_eval::evaluate_program(program).map_err(|e| Error::Parse(e.into()))
```

### Step 4: Clean Up Warnings

**General cleanup needed**:

1. Remove unused imports across all crates
2. Fix unused variable warnings by prefixing with underscore
3. Remove dead code warnings
4. Fix `for_loops_over_fallibles` warnings

## Verification Steps

After implementing the fixes:

1. **Run workspace check**: `cargo check --workspace`
2. **Verify no compilation errors**: All crates should compile successfully
3. **Check for warnings**: Address any remaining warnings
4. **Run tests**: `cargo test --workspace` to ensure functionality is preserved
5. **Verify error handling**: Ensure all error handling uses `StandardResult<T>` and `StandardError`

## Key Principles

1. **Consistency**: All error handling should use the standardized approach
2. **AST Compatibility**: Use the new `DeclarationKind` API instead of direct `Declaration` access
3. **Type Safety**: Ensure proper type conversions and method signatures
4. **Backward Compatibility**: Maintain existing functionality while updating to new APIs

## Expected Outcome

After completing these fixes:

- ✅ All workspace crates compile without errors
- ✅ Error handling is standardized across the workspace
- ✅ AST structure access uses the new API consistently
- ✅ No breaking changes to existing functionality
- ✅ Clean compilation with minimal warnings

## Notes

- The `ligature-types` crate is already successfully migrated and serves as a reference
- Focus on the specific error patterns identified above
- Use the existing working code in `ligature-types` as a guide for correct patterns
- Test incrementally to ensure each fix doesn't introduce new issues
