# Justfile Development Guide

The Ligature workspace uses a `justfile` for streamlined development workflows. This guide covers all available commands and best practices.

## Quick Start

```bash
# Install just (if not already installed)
cargo install just

# See all available commands
just --list

# Install all apps
just install

# Run reed CLI
just reed --help
```

## Core Commands

### Building

```bash
just build              # Build all binaries in release mode
just build-debug        # Build all binaries in debug mode
just build-install      # Build and install all apps
```

### Installation

```bash
just install                    # Install all apps to system
just install-reed              # Install reed CLI only
just install-cacophony         # Install cacophony CLI only
just install-keywork           # Install keywork CLI only
just install-performance-monitor # Install performance monitor only
```

### Development Workflow

```bash
just dev-setup         # Set up development environment (check + test)
just dev               # Quick development cycle (build + test)
just check-all         # Run all checks (check + test + lint)
```

### Testing

```bash
just test              # Run all tests
just test-verbose      # Run tests with output
just test-integration  # Run integration tests only
just test-performance  # Run performance tests only
```

### Code Quality

```bash
just check             # Check code without building
just fmt               # Format code
just lint              # Lint code with clippy
just clean             # Clean build artifacts
```

### Running CLIs

```bash
just reed *args        # Run reed CLI with arguments
just cacophony *args   # Run cacophony CLI with arguments
just keywork *args     # Run keywork CLI with arguments
just perf-monitor *args # Run performance monitor with arguments
```

### Examples

```bash
# Parse a Ligature file
just reed parse --file examples/test.lig

# Run cacophony with a configuration
just cacophony run --config my-config.lig

# Check package dependencies
just keywork check --register stdlib

# Monitor performance
just perf-monitor --benchmark
```

## Workspace Management

### Information

```bash
just workspace-info    # Show workspace structure and components
just help             # Show help for all CLI apps
just list             # Show all available just commands
```

### Dependencies

```bash
just update           # Update dependencies
just outdated         # Show outdated dependencies
```

### Benchmarks

```bash
just bench            # Run all benchmarks
```

## Development Best Practices

### Daily Workflow

1. **Start of day:**
   ```bash
   just dev-setup      # Ensure everything is working
   ```

2. **During development:**
   ```bash
   just check          # Quick syntax check
   just test           # Run tests
   just reed --help    # Test CLI functionality
   ```

3. **Before committing:**
   ```bash
   just check-all      # Run all quality checks
   just fmt            # Format code
   ```

### Debugging

```bash
# Build in debug mode for faster iteration
just build-debug

# Run with verbose output
just test-verbose

# Check specific components
just check
```

### Performance Testing

```bash
# Run performance benchmarks
just bench

# Test specific performance scenarios
just perf-monitor --benchmark function-calls
```

## CLI App Reference

### Reed (Ligature Language CLI)

```bash
just reed parse --file <file>      # Parse and validate
just reed typecheck --file <file>  # Type check
just reed eval --file <file>       # Evaluate
just reed run --file <file>        # Complete pipeline
```

### Cacophony (Orchestration CLI)

```bash
just cacophony run --config <file>     # Run configuration
just cacophony validate --config <file> # Validate configuration
just cacophony deploy --config <file>   # Deploy configuration
```

### Keywork (Package Manager)

```bash
just keywork install <package>     # Install package
just keywork check --register <name> # Check register
just keywork update <package>      # Update package
```

### Performance Monitor

```bash
just perf-monitor --benchmark      # Run benchmarks
just perf-monitor --profile <file> # Profile specific file
just perf-monitor --report         # Generate performance report
```

## Troubleshooting

### Common Issues

1. **Command not found:**
   ```bash
   # Install just
   cargo install just
   ```

2. **Build failures:**
   ```bash
   just clean          # Clean build artifacts
   just build-debug    # Try debug build first
   ```

3. **Test failures:**
   ```bash
   just test-verbose   # See detailed test output
   ```

4. **Installation conflicts:**
   ```bash
   # The install commands use --force to overwrite existing binaries
   just install
   ```

### Getting Help

```bash
just --list           # See all commands
just help             # Get help for CLI apps
just workspace-info   # Understand workspace structure
```

## Integration with IDEs

### VS Code

Add to your VS Code settings:

```json
{
    "just.runOnSave": true,
    "just.command": "just"
}
```

### Other IDEs

Most IDEs can integrate with just by:
1. Adding just to your PATH
2. Using `just <command>` as a build task
3. Setting up just commands as custom run configurations

## Contributing

When adding new commands to the justfile:

1. Follow the existing naming conventions
2. Add helpful comments
3. Test the command thoroughly
4. Update this documentation
5. Consider adding the command to the default workflow

### Adding New Commands

Example of adding a new command:

```makefile
# Format and lint code
fmt-lint:
    cargo fmt
    cargo clippy
```

This follows the existing pattern and provides a clear, descriptive name. 