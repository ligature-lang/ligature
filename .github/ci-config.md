# Ligature CI Configuration

This document describes the configuration for the Ligature project's continuous integration setup.

## Overview

The CI system uses GitHub Actions to ensure code quality, run tests, and verify builds across all crates in the workspace.

## Workflows

### Main CI Workflow (`ci.yml`)

The main CI workflow runs the following jobs:

1. **Code Quality**

   - Formatting checks with `rustfmt`
   - Linting with `clippy`
   - Ensures consistent code style

2. **Unit Tests**

   - Runs all unit tests across all crates
   - Tests individual crate functionality

3. **Integration Tests**

   - Runs integration tests
   - Runs property-based tests
   - Runs differential tests against Lean specifications

4. **Build Verification**

   - Builds all crates in debug mode
   - Builds all crates in release mode
   - Ensures no compilation errors

5. **Examples**

   - Builds all examples
   - Runs example programs to verify they work

6. **LSP Tests**

   - Tests the Language Server Protocol implementation
   - Ensures IDE integration works correctly

7. **Documentation**

   - Verifies documentation builds correctly
   - Checks for broken links or missing docs

8. **Security Audit**
   - Runs `cargo audit` to check for known vulnerabilities
   - Ensures dependencies are secure

### Test Scripts Workflow (`test-scripts.yml`)

Runs the existing test scripts to ensure they work in the CI environment:

- `.github/scripts/run_tests.sh`
- `.github/scripts/run_integration_tests.sh`
- `.github/scripts/test_lsp.sh`

### Status Badge Workflow (`status-badge.yml`)

Generates dynamic status badges based on CI results.

## Configuration

### Supported Rust Versions

- stable
- 1.70

### Workspace Crates

- ligature-ast
- ligature-parser
- ligature-types
- ligature-eval
- ligature-lsp
- krox
- reed (apps/reed)
- keywork (apps/keywork)
- cacophony (apps/cacophony)

### Test Categories

- unit
- integration
- property
- differential

### Examples

- test_core
- test_parser
- test_type_inference
- test_evaluation

### Environment Variables

- `CARGO_TERM_COLOR=always`
- `RUST_BACKTRACE=1`

### Cache Configuration

Caches the following paths:

- `~/.cargo/registry`
- `~/.cargo/git`
- `target`

### GitHub Actions Versions

- checkout: v4
- cache: v3
- rust-toolchain: stable

### Clippy Configuration

- Flags: `--all-targets --all-features`
- Deny: `-D warnings`

### Security Audit Configuration

- Flags: `--deny warnings`

## Local Development

To run the same checks locally that the CI performs:

```bash
# Code quality checks
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings

# Run all tests
cargo test

# Build all crates
cargo build --all

# Security audit
cargo install cargo-audit
cargo audit --deny warnings

# Documentation
cargo doc --no-deps --all
```

## Troubleshooting

### Common Issues

1. **Formatting Errors**: Run `cargo fmt` to fix formatting issues
2. **Clippy Warnings**: Address all clippy warnings before submitting PRs
3. **Test Failures**: Ensure all tests pass locally before pushing
4. **Build Errors**: Check that all crates build successfully

### Performance

- The CI uses caching to speed up builds
- Tests run in parallel where possible
- Consider running only specific test categories locally for faster feedback

## Contributing

When contributing to the project:

1. Ensure all CI checks pass before submitting a PR
2. Add tests for new functionality
3. Update documentation as needed
4. Follow the established code style
5. Address any security audit warnings
