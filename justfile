# Justfile for Ligature workspace
# Run with: just <command>

# Default target
default:
    @just --list

# Build all binaries in release mode
build:
    cargo build --release --bins

# Build all binaries in debug mode
build-debug:
    cargo build --bins

# Install all apps to system
install:
    @echo "Installing all Ligature apps..."
    cargo install --path apps/reed --force
    cargo install --path apps/cacophony --force
    cargo install --path apps/keywork --force
    cargo install --path apps/performance-monitor --force
    @echo "Installation complete!"

# Install specific app
install-reed:
    cargo install --path apps/reed --force

install-cacophony:
    cargo install --path apps/cacophony --force

install-keywork:
    cargo install --path apps/keywork --force

install-performance-monitor:
    cargo install --path apps/performance-monitor --force

# Run tests
test:
    cargo test --all-features \
        --package ligature-ast \
        --package ligature-parser \
        --package ligature-types \
        --package ligature-eval \
        --package ligature-lsp \
        --package embouchure-xdg \
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

# Run tests with output
test-verbose:
    cargo test -- --nocapture

# Run specific test suite
test-integration:
    cargo test --test integration

test-performance:
    cargo test --test performance_regression_tests

# Test krox crate (requires Node.js runtime)
test-krox:
    cargo test --package krox --all-features

# Test all crates including krox (requires Node.js runtime)
test-all:
    cargo test --all-features

# Check code without building
check:
    cargo check --package ligature-ast --package ligature-parser --package ligature-types --package ligature-eval --package ligature-lsp --package embouchure-xdg --package cacophony-core --package cacophony-config --package cacophony-plugin --package baton-client --package baton-core --package baton-engine-plugin --package baton-error --package baton-protocol --package baton-specification --package baton-verification --package ligature-performance-validation --all-targets --all-features

# Format code
fmt:
    cargo +nightly fmt

# Lint code
lint:
    cargo clippy --all-targets --all-features -- -D warnings

# Clean build artifacts
clean:
    cargo clean

# Run benchmarks
bench:
    cargo bench

# Run reed CLI
reed *args:
    cargo run --bin reed -- {{args}}

# Run cacophony CLI
cacophony *args:
    cargo run --bin cacophony -- {{args}}

# Run keywork CLI
keywork *args:
    cargo run --bin keywork -- {{args}}

# Run performance monitor
perf-monitor *args:
    cargo run --bin ligature-performance-monitor -- {{args}}

# Show help for all apps
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

# Development workflow
dev-setup:
    @echo "Setting up development environment..."
    cargo check
    cargo test
    @echo "Development setup complete!"

# Quick development cycle
dev: build test

# Show workspace info
workspace-info:
    @echo "Ligature Workspace Information:"
    @echo "================================"
    @echo "Apps:"
    @echo "  - reed: Ligature language CLI"
    @echo "  - cacophony: Collection orchestration CLI"
    @echo "  - keywork: Package management CLI"
    @echo "  - performance-monitor: Performance monitoring tool"
    @echo ""
    @echo "Crates:"
    @echo "  - ligature-ast: Abstract syntax tree"
    @echo "  - ligature-parser: Program parsing"
    @echo "  - ligature-types: Type system"
    @echo "  - ligature-eval: Program evaluation"
    @echo "  - ligature-lsp: Language server protocol"
    @echo "  - ligature-xdg: XDG configuration"
    @echo "  - cacophony-core: Core orchestration"
    @echo "  - cacophony-config: Configuration management"
    @echo "  - cacophony-plugin: Plugin system"

# Update dependencies
update:
    cargo update

# Show outdated dependencies
outdated:
    cargo outdated

# Run all checks (check, test, lint, fmt)
check-all: check test lint fmt

# Build and install in one command
build-install: build install

# Show available commands
list:
    @just --list 