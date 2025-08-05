# Error Tests

This directory contains tests that are designed to produce specific errors in the Ligature language.

## Test Files

### Type Errors
- **`type_errors.lig`** - Comprehensive type error examples
- **`simple_type_error.lig`** - Simple type mismatch
- **`type_error_test.lig`** - Basic type error test

### Function Errors
- **`function_error_test.lig`** - Function-related errors

### Record Errors
- **`record_error_test.lig`** - Record field access errors

## Purpose

These tests are designed to verify that the Ligature compiler and type checker correctly identify and report errors. All tests in this directory should fail with appropriate error messages when processed by the Ligature toolchain.

The errors include:
- Type mismatches (e.g., adding string and integer)
- Invalid function type annotations
- Accessing non-existent record fields
- Pattern matching with incorrect types 