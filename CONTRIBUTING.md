# Contributing to Ligature

Thank you for your interest in contributing to Ligature! This guide will help you get started with development.

## Table of Contents

- [Development Setup](#development-setup)
- [Project Structure](#project-structure)
- [Building and Testing](#building-and-testing)
- [Code Style](#code-style)
- [Development Status](#development-status)
- [Continuous Integration](#continuous-integration)
- [Tools and Commands](#tools-and-commands)

## Development Setup

### Prerequisites

- Rust 1.70+ (stable)
- Cargo

### Initial Setup

1. Fork and clone the repository
2. Install Rust toolchain
3. Run `cargo build` to see current compilation status
4. Run `cargo test` to see test status
5. Make your changes
6. Add tests for new functionality
7. Submit a pull request

## Project Structure

```
ligature/
├── crates/
│   ├── ligature-ast/          # AST definitions and utilities
│   ├── ligature-parser/       # Parsing (using pest)
│   ├── ligature-types/        # Type system implementation
│   ├── ligature-eval/         # Evaluation engine
│   ├── ligature-lsp/          # Language server
│   ├── ligature-xdg/          # XDG base directory support
│   ├── cacophony-core/        # Core types and traits for Cacophony
│   ├── cacophony-config/      # Configuration management for Cacophony
│   └── cacophony-plugin/      # Plugin system for Cacophony
├── apps/
│   ├── reed/                  # Command-line interface
│   ├── keywork/               # Package manager for registers
│   ├── performance-monitor/   # Performance monitoring tool
│   └── cacophony/             # CLI orchestration tool (simplified)
├── engines/lean/spec/         # Lean specifications
├── tests/
│   ├── property/              # Property-based tests
│   ├── differential/          # Tests against Lean reference
│   └── integration/           # End-to-end tests
├── examples/                  # Example configurations
├── registers/                 # Standard library and examples
└── docs/
    └── architecture/          # Architecture documentation
```

## Building and Testing

### Quick Start with Justfile (Recommended)

The workspace includes a comprehensive `justfile` for streamlined development workflows:

```bash
# Install just (if not already installed)
cargo install just

# See all available commands
just --list

# Install all apps
just install

# Run development setup
just dev-setup

# Quick development cycle
just dev
```

For detailed justfile documentation, see [Justfile Development Guide](docs/.development/justfile-guide.md).

### Manual Building

```bash
# Clone the repository
git clone https://github.com/ligature-lang/ligature.git
cd ligature

# Build all crates (compiles successfully)
cargo build

# Run tests (comprehensive test suite)
cargo test

# Build the CLI
cargo build --bin reed

# Build the package manager
cargo build --bin keywork

# Build the client SDK
cargo build --bin krox
```

**Note**: The project compiles successfully and has comprehensive test coverage. All core language features are working correctly.

### Local Development Checks

To run the same checks locally that the CI performs:

```bash
# Using justfile (recommended)
just check-all

# Manual commands
cargo +nightly fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test

# Build all crates
cargo build --all

# Security audit
cargo install cargo-audit
cargo audit --deny warnings

# Documentation
cargo doc --no-deps --all
```

## Code Style

- Follow Rust conventions
- Use `cargo +nightly fmt` for formatting
- Use `cargo clippy` for linting
- Write comprehensive documentation
- Add tests for new features

## Continuous Integration

This project uses GitHub Actions for continuous integration. The following workflows run on every pull request and push to main:

### CI Workflow (`.github/workflows/ci.yml`)

- **Code Quality**: Formatting checks with `rustfmt` and linting with `clippy`
- **Unit Tests**: Runs all unit tests across all crates
- **Integration Tests**: Runs integration, property, and differential tests
- **Build Verification**: Ensures all crates build successfully in both debug and release modes
- **Examples**: Builds and runs all examples
- **LSP Tests**: Tests the Language Server Protocol implementation
- **Documentation**: Verifies that documentation builds correctly
- **Security Audit**: Runs `cargo audit` to check for known vulnerabilities

### Test Scripts Workflow (`.github/workflows/test-scripts.yml`)

- Runs the existing test scripts to ensure they work in the CI environment
- Executes `.github/scripts/run_tests.sh`, `.github/scripts/run_integration_tests.sh`, and `.github/scripts/test_lsp.sh`

### Status Badge Workflow (`.github/workflows/status-badge.yml`)

- Generates dynamic status badges based on CI results

## Tools and Commands

### Using the CLI Tools (Recommended)

The workspace includes several CLI tools. You can run them using the justfile:

```bash
# Run reed (Ligature language CLI)
just reed parse --file examples/basic.lig
just reed typecheck --file examples/basic.lig
just reed eval --file examples/basic.lig

# Run cacophony (orchestration CLI)
just cacophony run --config my-config.lig

# Run keywork (package manager)
just keywork init my-register
just keywork install stdlib
just keywork list

# Run performance monitor
just perf-monitor --benchmark
```

### Manual CLI Usage

You can also run the CLI tools directly:

```bash
# Reed CLI
cargo run --bin reed -- parse --file examples/basic.lig
cargo run --bin reed -- typecheck --file examples/basic.lig
cargo run --bin reed -- eval --file examples/basic.lig

# Keywork CLI
cargo run --bin keywork -- init my-register
cargo run --bin keywork -- install stdlib
cargo run --bin keywork -- list

# Cacophony CLI
cargo run --bin cacophony -- run --config my-config.lig
```

### Client SDK (krox)

The `krox` crate provides client SDKs for invoking Ligature programs as side effects:

```bash
# Build the krox CLI
cargo build --bin krox

# Run krox commands (see krox --help for details)
cargo run --bin krox -- --help
```

## Roadmap

### Phase 1: Foundation ✅ COMPLETED

- [x] Project scaffolding
- [x] AST and type definitions
- [x] Parser infrastructure (fully implemented)
- [x] CLI interface (reed)
- [x] Package management (keywork)
- [x] Client SDK framework (krox)
- [x] Language server infrastructure
- [x] Core type inference and checking
- [x] Evaluation engine
- [x] Comprehensive test suite

### Phase 2: Core Implementation ✅ COMPLETED

- [x] Full type inference (core functionality)
- [x] Evaluation engine (complete)
- [x] Property-based testing
- [x] Union types and pattern matching
- [x] Module system
- [x] Advanced language features

### Phase 3: Polish and Optimization 🔄 IN PROGRESS

- [ ] Code quality improvements (warnings, unused code)
- [ ] Type system completion (import resolution, module loading)
- [x] Parser refinements (operator precedence) ✅ COMPLETED
- [ ] Performance optimization
- [ ] Documentation updates

### Phase 4: Ecosystem and Tooling 🔄 IN PROGRESS

- [ ] Language server completion
- [ ] IDE integration
- [ ] Enhanced documentation
- [ ] Community tools
- [ ] Performance benchmarking

## Contact

- GitHub Issues: [https://github.com/ligature-lang/ligature/issues](https://github.com/ligature-lang/ligature/issues)
- Discussions: [https://github.com/ligature-lang/ligature/discussions](https://github.com/ligature-lang/ligature/discussions)
