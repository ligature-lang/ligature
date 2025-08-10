# Justfile for Ligature workspace
# Run with: just <command>

# Default target - shows common commands and test suites
default:
    @echo "Ligature Workspace - Common Commands"
    @echo "===================================="
    @echo ""
    @echo "🏗️  BUILD & INSTALL:"
    @echo "  just build              # Build all binaries in release mode"
    @echo "  just build-debug        # Build all binaries in debug mode"
    @echo "  just install            # Install all apps to system PATH"
    @echo "  just build-install      # Build and install all apps"
    @echo ""
    @echo "🧪 TESTING:"
    @echo "  just test               # Run tests for all core crates"
    @echo "  just test-all           # Run all tests across workspace"
    @echo "  just test-apps          # Run tests for CLI applications"
    @echo "  just test-examples      # Run integration tests"
    @echo ""
    @echo "🔧 DEVELOPMENT:"
    @echo "  just check              # Check code compilation"
    @echo "  just fmt                # Format code using rustfmt"
    @echo "  just lint               # Lint code using clippy"
    @echo "  just check-all          # Run all quality checks"
    @echo "  just dev-setup          # Set up development environment"
    @echo ""
    @echo "🚀 CLI APPLICATIONS:"
    @echo "  just reed [args]        # Run reed CLI"
    @echo "  just cacophony [args]   # Run cacophony CLI"
    @echo "  just keywork [args]     # Run keywork CLI"
    @echo "  just baton [args]       # Run baton CLI"
    @echo "  just perf-monitor [args] # Run performance monitor"
    @echo ""
    @echo "📊 SPECIFIC TEST SUITES:"
    @echo "  just test-ligature-ast  # Test AST crate"
    @echo "  just test-ligature-parser # Test parser crate"
    @echo "  just test-ligature-types # Test types crate"
    @echo "  just test-ligature-eval # Test evaluation crate"
    @echo "  just test-ligature-lsp  # Test LSP crate"
    @echo "  just test-module-system # Test module system"
    @echo "  just test-error-handling # Test error handling"
    @echo "  just test-type-inference # Test type inference"
    @echo "  just test-union-patterns # Test union patterns"
    @echo "  just test-performance-benchmark # Test performance"
    @echo ""
    @echo "ℹ️  INFORMATION:"
    @echo "  just help               # Show CLI app help"
    @echo "  just --list             # Show ALL available commands"
    @echo ""
    @echo "💡 Tip: Use 'just --list' to see all available commands with descriptions!"

# Build all binaries in release mode with optimizations
build:
    cargo build --release --bins

# Build all binaries in debug mode for development
build-debug:
    cargo build --bins

# Install all Ligature apps to system PATH
install:
    @echo "Installing all Ligature apps..."
    cargo install --path apps/reed --force
    cargo install --path apps/cacophony --force
    cargo install --path apps/keywork --force
    cargo install --path apps/performance-monitor --force
    cargo install --path apps/baton --force
    @echo "Installation complete!"

# Install reed CLI app to system
install-reed:
    cargo install --path apps/reed --force

# Install cacophony CLI app to system
install-cacophony:
    cargo install --path apps/cacophony --force

# Install keywork CLI app to system
install-keywork:
    cargo install --path apps/keywork --force

# Install performance monitor CLI app to system
install-performance-monitor:
    cargo install --path apps/performance-monitor --force

# Install baton CLI app to system
install-baton:
    cargo install --path apps/baton --force

# Run tests for all core crates (AST, parser, types, eval, LSP, etc.)
test:
    cargo test --all-features \
        --package ligature-ast \
        --package ligature-parser \
        --package ligature-types \
        --package ligature-eval \
        --package ligature-lsp \
        --package ligature-error \
        --package embouchure-xdg \
        --package embouchure-checker \
        --package cacophony-core \
        --package cacophony-config \
        --package cacophony-plugin \
        --package baton-client \
        --package baton-core \
        --package baton-engine-plugin \
        --package baton-error \
        --package baton-protocol \
        --package baton-specification \
        --package baton-verification \
        --package ligature-performance-validation

# Run tests for all CLI applications
test-apps:
    cargo test --all-features \
        --package reed \
        --package cacophony \
        --package keywork \
        --package performance-monitor \
        --package baton

# Run tests for examples package (includes integration tests)
test-examples:
    cargo test --package ligature-examples --all-features

# Run tests for krox crate (requires Node.js runtime)
test-krox:
    cargo test --package krox --all-features

# Run tests for lean engine
test-lean:
    cargo test --package lean --all-features

# Run all tests across the entire workspace
test-all:
    cargo test --workspace --all-features

# Run tests with verbose output showing all test results
test-verbose:
    cargo test -- --nocapture

# Run module system integration tests
test-module-system:
    cargo test --package ligature-examples --example test_module_system

# Run error handling integration tests
test-error-handling:
    cargo test --package ligature-examples --example test_error_handling

# Run pattern guards integration tests
test-pattern-guards:
    cargo test --package ligature-examples --example test_pattern_guards

# Run type inference integration tests
test-type-inference:
    cargo test --package ligature-examples --example test_type_inference

# Run evaluation integration tests
test-evaluation:
    cargo test --package ligature-examples --example test_evaluation

# Run parser integration tests
test-parser:
    cargo test --package ligature-examples --example test_parser

# Run union pattern matching tests
test-union-patterns:
    cargo test --package ligature-examples --bin test_union_pattern_matching

# Run advanced union pattern tests
test-advanced-union-patterns:
    cargo test --package ligature-examples --bin test_advanced_union_patterns

# Run union evaluation tests
test-union-evaluation:
    cargo test --package ligature-examples --bin test_union_evaluation

# Run performance benchmark tests
test-performance-benchmark:
    cargo test --package ligature-examples --bin performance_benchmark

# Run function call benchmark tests
test-function-call-benchmark:
    cargo test --package ligature-examples --bin function_call_benchmark

# Run comprehensive performance tests
test-comprehensive-performance:
    cargo test --package ligature-examples --bin test_comprehensive_performance

# Run ligature-ast crate tests
test-ligature-ast:
    cargo test --package ligature-ast --all-features

# Run ligature-parser crate tests
test-ligature-parser:
    cargo test --package ligature-parser --all-features

# Run ligature-types crate tests
test-ligature-types:
    cargo test --package ligature-types --all-features

# Run ligature-eval crate tests
test-ligature-eval:
    cargo test --package ligature-eval --all-features

# Run ligature-lsp crate tests
test-ligature-lsp:
    cargo test --package ligature-lsp --all-features

# Run embouchure-checker crate tests
test-embouchure-checker:
    cargo test --package embouchure-checker --all-features

# Run embouchure-xdg crate tests
test-embouchure-xdg:
    cargo test --package embouchure-xdg --all-features

# Check code compilation without building binaries
check:
    cargo check --workspace --all-targets --all-features

# Format all code using rustfmt
fmt:
    cargo +nightly fmt

# Lint code using clippy with warnings as errors
lint:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

# Clean all build artifacts and target directories
clean:
    cargo clean

# Run all benchmarks
bench:
    cargo bench

# Run reed CLI with optional arguments
reed *args:
    cargo run --bin reed -- {{args}}

# Run cacophony CLI with optional arguments
cacophony *args:
    cargo run --bin cacophony -- {{args}}

# Run keywork CLI with optional arguments
keywork *args:
    cargo run --bin keywork -- {{args}}

# Run performance monitor CLI with optional arguments
perf-monitor *args:
    cargo run --bin ligature-performance-monitor -- {{args}}

# Run baton CLI with optional arguments
baton *args:
    cargo run --bin baton -- {{args}}

# Show help information for all CLI applications
help:
    @echo "Ligature CLI Help:"
    @echo ""
    @echo "reed:"
    cargo run --bin reed -- --help
    @echo ""
    @echo "cacophony:"
    cargo run --bin cacophony -- --help
    @echo ""
    @echo "keywork:"
    cargo run --bin keywork -- --help
    @echo ""
    @echo "performance-monitor:"
    cargo run --bin ligature-performance-monitor -- --help
    @echo ""
    @echo "baton:"
    cargo run --bin baton -- --help

# Set up development environment (check + test)
dev-setup:
    @echo "Setting up development environment..."
    cargo check
    cargo test
    @echo "Development setup complete!"

# Quick development cycle (build + test)
dev: build test

# Show comprehensive workspace information
workspace-info:
    @echo "Ligature Workspace Information:"
    @echo "================================"
    @echo "Apps:"
    @echo "  - reed: Ligature language CLI"
    @echo "  - cacophony: Collection orchestration CLI"
    @echo "  - keywork: Package management CLI"
    @echo "  - performance-monitor: Performance monitoring tool"
    @echo "  - baton: Baton orchestration tool"
    @echo ""
    @echo "Core Crates:"
    @echo "  - ligature-ast: Abstract syntax tree"
    @echo "  - ligature-parser: Program parsing"
    @echo "  - ligature-types: Type system"
    @echo "  - ligature-eval: Program evaluation"
    @echo "  - ligature-lsp: Language server protocol"
    @echo "  - ligature-error: Error handling"
    @echo "  - embouchure-xdg: XDG configuration"
    @echo "  - embouchure-checker: Constraint checking"
    @echo "  - cacophony-core: Core orchestration"
    @echo "  - cacophony-config: Configuration management"
    @echo "  - cacophony-plugin: Plugin system"
    @echo "  - baton-*: Baton orchestration system"
    @echo ""
    @echo "Test Categories:"
    @echo "  - Core crate tests: Unit tests for individual crates"
    @echo "  - App tests: Tests for CLI applications"
    @echo "  - Integration tests: End-to-end functionality tests (in examples package)"
    @echo "  - Performance tests: Performance regression tests"
    @echo "  - Property tests: Property-based testing"
    @echo "  - Differential tests: Specification compliance tests"

# Update all dependencies to latest compatible versions
update:
    cargo update

# Show outdated dependencies
outdated:
    cargo outdated

# Run all quality checks (check, test, lint, fmt)
check-all: check test lint fmt

# Build and install all apps in one command
build-install: build install

# Show all available just commands
list:
    @just --list 