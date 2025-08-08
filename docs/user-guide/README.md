# Ligature User Guide

Welcome to the Ligature user guide! This guide provides comprehensive documentation for using Ligature, a Turing-incomplete configuration and data management language.

## Getting Started

- **[Getting Started](getting-started.md)** - Learn the basics of Ligature, installation, and your first program
- **[Language Reference](language-reference.md)** - Complete reference for Ligature syntax and features
- **[Constraint-Based Validation](constraint-validation.md)** - Create types with built-in validation rules
- **[Examples](examples.md)** - Practical examples and use cases
- **[Performance Guide](performance-guide.md)** - Performance optimization and monitoring

## Development Tools

- **[IDE Integration](ide-integration.md)** - Professional-grade development environment with LSP
- **[Type-Level Computation](type-level-computation.md)** - Advanced type system features
- **[Enhanced LSP Features](enhanced-lsp-features.md)** - Advanced language server capabilities
- **[Language Server Completion](language-server-completion.md)** - Complete LSP implementation

## Configuration and System Integration

- **[XDG Integration](xdg-integration.md)** - Complete guide to Ligature's XDG Base Directory integration
- **[XDG Integration Quick Reference](xdg-integration-quick-reference.md)** - Quick reference for developers
- **[Cacophony CLI](cacophony-cli.md)** - Configuration orchestration and deployment tool
- **[Evaluator Configuration](evaluator-configuration.md)** - Performance and behavior configuration

## Troubleshooting and Support

- **[Error Messages](error-messages.md)** - Understanding and resolving common errors
- **[Enhanced Error Reporting](enhanced-error-reporting.md)** - Advanced error diagnostics and fixes
- **[FAQ](faq.md)** - Frequently asked questions and answers

## What is Ligature?

Ligature is a Turing-incomplete configuration and data management language designed with correctness and safety as primary goals. It provides:

- **Turing-incomplete by design** - All programs are guaranteed to terminate
- **Dependently-typed foundation** - Based on Lean 4 type theory
- **ML-family syntax** - Familiar and accessible syntax inspired by OCaml and Elm
- **Configuration-focused** - Optimized for configuration management and data validation
- **Strong correctness guarantees** - Total functions with comprehensive error reporting

## Key Features

### Language Features

- **Union types** with full evaluation and pattern matching
- **Advanced pattern matching** with guards and variable binding
- **Complete module system** with imports and exports
- **Type inference** and constraint solving
- **Operator precedence** system
- **Import resolution** and module loading
- **Type-level computation** with advanced subtyping and dependent types
- **Constraint-based validation** with refinement types and pattern constraints

### System Integration

- **XDG Base Directory compliance** - Follows Linux/Unix standards
- **Cross-platform support** - Works on Linux, macOS, and Windows
- **Multiple configuration formats** - JSON, YAML, and TOML support
- **Component isolation** - Each component gets its own subdirectory

### Development Tools

- **Language Server Protocol (LSP)** - Professional-grade IDE integration with advanced features
- **Command-line interface** - Comprehensive CLI tools
- **Package management** - Keywork package manager
- **Client SDKs** - Krox client framework
- **Performance monitoring** - Built-in performance analysis tools
- **Cacophony CLI** - Configuration orchestration and deployment
- **Symbol Finding** - Cross-file navigation and workspace search
- **Import Resolution** - Complete module resolution with dependency tracking

## Quick Start

1. **Install Ligature** - See [Getting Started](getting-started.md)
2. **Write your first program** - Create a simple configuration
3. **Explore examples** - Check out [Examples](examples.md)
4. **Configure your environment** - Set up [XDG Integration](xdg-integration.md)
5. **Set up IDE integration** - Install [IDE Integration](ide-integration.md)
6. **Explore advanced features** - Learn [Type-Level Computation](type-level-computation.md)

## Documentation Structure

This user guide is organized to help you learn Ligature effectively:

1. **Start with Getting Started** - Learn the basics and install Ligature
2. **Read the Language Reference** - Understand syntax and features
3. **Explore Examples** - See practical use cases
4. **Configure XDG Integration** - Set up system integration
5. **Set up IDE Integration** - Configure your development environment
6. **Learn Advanced Features** - Explore type-level computation and advanced LSP features
7. **Troubleshoot Issues** - Use error messages and FAQ for help

## Recent Achievements (January 2025)

- ✅ **Professional-Grade IDE Integration** - Complete LSP symbol finding with cross-file navigation
- ✅ **Type-Level Computation System** - Advanced type-level programming with dependent types
- ✅ **Constraint-Based Validation** - Refinement types and pattern constraints with runtime validation
- ✅ **Performance Optimization** - 2.7x function call improvement with 1M+ ops/sec
- ✅ **Configuration Management** - Schema-based validation and hot-reloading
- ✅ **Performance Monitoring** - Real-time metrics and adaptive optimization

## Contributing

If you find issues with the documentation or have suggestions for improvements:

1. Check the [FAQ](faq.md) for common questions
2. Look at [Error Messages](error-messages.md) for troubleshooting
3. File an issue on the [Ligature GitHub repository](https://github.com/ligature-lang/ligature)

## Additional Resources

- **[Project README](../../README.md)** - Main project documentation
- **[Architecture Documentation](../architecture/)** - Technical architecture details
- **[Specification](../../engines/lean/spec/)** - Formal language specification
- **[Contributing Guide](../../CONTRIBUTING.md)** - How to contribute to Ligature
