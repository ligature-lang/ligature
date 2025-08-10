# Ligature Project Guide for LLMs

Welcome to the Ligature project! This guide is specifically designed for LLMs to quickly understand the project structure, language syntax, and available resources.

## 🚀 Quick Start

**Ligature** is a Turing-incomplete configuration language with dependently-typed foundations, designed for safe configuration management and data validation.

## 📚 Essential Resources

### Language Reference

- **[LLM Language Reference](docs/llm-language-reference.md)** - Complete syntax guide and patterns for generating Ligature code
- **[User Guide](docs/user-guide/)** - Comprehensive documentation for human users
- **[API Reference](docs/api-reference.md)** - Technical API documentation

### Project Tracking & Context

- **[`.rhema` Directory](.rhema/)** - Project tracking, context, and development history
- **[Architecture Docs](docs/architecture/)** - System design and implementation details
- **[Developer Guide](docs/developer-guide.md)** - Development workflow and guidelines

## 🏗️ Project Structure

```
ligature/
├── apps/                    # Application binaries
│   ├── keywork/            # Package manager CLI
│   ├── cacophony/          # Configuration management
│   ├── reed/               # Main CLI tool
│   └── editor-plugins/     # IDE integrations
├── crates/                 # Core libraries
│   ├── ligature-*/         # Language implementation
│   ├── embouchure-*/       # Shared libraries
│   └── baton-*/           # Protocol and verification
├── docs/                   # Documentation
│   ├── llm-language-reference.md  # ← LLM Language Guide
│   ├── user-guide/         # User documentation
│   └── architecture/       # System architecture
├── examples/               # Code examples
├── tests/                  # Test suites
├── registers/              # Standard library
└── .rhema/                 # ← Project tracking & context
```

## 💡 Key Language Features

### Core Characteristics

- **Turing-incomplete** - All programs terminate
- **Strongly typed** - Complete type safety
- **ML-family syntax** - Familiar functional programming style
- **Constraint-based validation** - Runtime validation with refinement types
- **Configuration-native** - Designed for config management

### Quick Syntax Example

```ocaml
// Define validated configuration
type User = {
    name: String where length > 0,
    age: Integer where x >= 0 && x <= 150,
    email: String with regexp("^[^@]+@[^@]+\\.[^@]+$")
};

let config = {
    database = { host = "localhost", port = 5432 },
    users = [
        { name = "Alice", age = 30, email = "alice@company.com" },
        { name = "Bob", age = 25, email = "bob@company.com" }
    ]
};
```

## 🎯 Common Tasks

### When Working with Ligature Code:

1. **Read the [LLM Language Reference](docs/llm-language-reference.md)** for syntax and patterns
2. **Check [examples/](examples/)** for working code samples
3. **Review [tests/](tests/)** for edge cases and validation

### When Contributing to the Project:

1. **Check [.rhema/](.rhema/)** for current development context and priorities
2. **Review [docs/architecture/](docs/architecture/)** for system design
3. **Follow [docs/developer-guide.md](docs/developer-guide.md)** for workflow

### When Building Applications:

1. **Use [apps/keywork/](apps/keywork/)** for package management
2. **Leverage [apps/cacophony/](apps/cacophony/)** for configuration management
3. **Integrate with [apps/reed/](apps/reed/)** for CLI operations

## 🔧 Development Tools

### Core Tools

- **`keywork`** - Package manager and registry tools
- **`cacophony`** - Configuration management system
- **`reed`** - Main CLI for evaluation and validation
- **`baton`** - Protocol and verification framework

### IDE Support

- **VS Code Extension** - Full language support in [apps/editor-plugins/vscode-ligature/](apps/editor-plugins/vscode-ligature/)
- **Language Server** - LSP implementation in [crates/ligature-lsp/](crates/ligature-lsp/)

## 📖 Documentation Hierarchy

### For LLMs:

1. **[LLM Language Reference](docs/llm-language-reference.md)** - Start here for syntax
2. **[.rhema/](.rhema/)** - Project context and tracking
3. **[Examples](examples/)** - Working code samples
4. **[Tests](tests/)** - Edge cases and validation

### For Human Developers:

1. **[User Guide](docs/user-guide/)** - Getting started and tutorials
2. **[API Reference](docs/api-reference.md)** - Technical documentation
3. **[Architecture](docs/architecture/)** - System design
4. **[Developer Guide](docs/developer-guide.md)** - Contribution guidelines

## 🎨 Language Patterns

### Configuration Management

```ocaml
type AppConfig = {
    database: DatabaseConfig,
    server: ServerConfig,
    logging: LogConfig
};
```

### Data Validation

```ocaml
type ValidUser = {
    name: String where length > 0,
    age: Integer where x >= 0 && x <= 150,
    email: String with regexp("^[^@]+@[^@]+\\.[^@]+$")
};
```

### Error Handling

```ocaml
type Result = Success a | Error String;

let safeDivide = \x y ->
    if y == 0 then Error "Division by zero"
    else Success (x / y);
```

## 🚨 Important Notes

### Language Constraints

- **No recursion without termination** - All functions must terminate
- **No side effects** - Pure functional programming
- **Strong typing** - All types must be explicit or inferrable
- **Validation at runtime** - Constraint types enforce validation

### Project Conventions

- **Shared libraries** prefixed with `embouchure-`
- **Service crates** use descriptive names
- **Conventional commits** for version control
- **Comprehensive testing** for all features

## 🔗 Quick Links

- **[Language Reference](docs/llm-language-reference.md)** - Complete syntax guide
- **[Project Context](.rhema/)** - Development tracking and priorities
- **[Examples](examples/)** - Working code samples
- **[Tests](tests/)** - Validation and edge cases
- **[Architecture](docs/architecture/)** - System design
- **[User Guide](docs/user-guide/)** - Human-readable documentation

---

**Remember**: When generating Ligature code, always refer to the [LLM Language Reference](docs/llm-language-reference.md) for correct syntax and patterns. For project context and current priorities, check the [.rhema/](.rhema/) directory.
