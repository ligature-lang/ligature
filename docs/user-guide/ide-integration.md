# IDE Integration Guide

Ligature provides comprehensive IDE integration through the Language Server Protocol (LSP), enabling a professional-grade development experience in any LSP-compatible editor.

## Overview

The IDE integration includes:

- **VS Code Extension**: Complete extension with professional-grade features
- **Language Server**: LSP-compatible server for any editor
- **Syntax Highlighting**: Full syntax support for Ligature code
- **IntelliSense**: Intelligent code completion and suggestions
- **Error Diagnostics**: Real-time error reporting and analysis
- **Code Navigation**: Go to definition, find references, symbol search
- **Code Actions**: Quick fixes, refactoring, and code generation
- **Formatting**: Automatic code formatting and style enforcement
- **Cross-Module Support**: Full support for multi-file projects
- **Import Resolution**: Automatic module loading and symbol resolution
- **Performance Monitoring**: Built-in performance analysis tools
- **Symbol Finding**: Professional-grade cross-file symbol navigation

## Recent Achievements (January 2025)

- ✅ **Complete LSP Symbol Finding Implementation** - Professional-grade cross-file symbol finding
- ✅ **Cross-File Symbol Finding** - References, definitions, and type navigation across modules
- ✅ **Import Resolution Integration** - Module loading, dependency tracking, and cross-module references
- ✅ **Workspace Symbol Search** - Enhanced search with module awareness and deduplication
- ✅ **Import-Aware Completion** - Code completion with symbols from imported modules
- ✅ **VS Code Extension Advanced Features** - Professional-grade development environment

## VS Code Extension

### Installation

#### From Source

1. **Build the language server**:

   ```bash
   cargo build --release -p ligature-lsp
   ```

2. **Build the extension**:

   ```bash
   cd apps/editor-plugins/vscode-ligature
   npm install
   npm run compile
   ```

3. **Install the extension**:

   ```bash
   # Package the extension
   npm install -g @vscode/vsce
   vsce package

   # Install in VS Code
   code --install-extension vscode-ligature-*.vsix
   ```

#### Development Installation

1. Open the extension folder in VS Code
2. Press `F5` to launch Extension Development Host
3. Open a `.lig` file to test the extension

### Features

#### Syntax Highlighting

- Full syntax highlighting for Ligature code
- Support for comments, strings, numbers, keywords, operators
- Type-aware highlighting for user-defined types
- Import statement highlighting

#### IntelliSense

- **Context-aware completions**: Suggestions based on current context
- **Type-aware completions**: Suggestions that match expected types
- **Fuzzy matching**: Intelligent matching without exact prefixes
- **Auto-import suggestions**: Automatic import suggestions for missing symbols
- **Snippet support**: Pre-built code snippets for common patterns
- **Cross-module completions**: Suggestions from imported modules
- **Performance-aware suggestions**: Optimized completion performance
- **Import-aware completion**: Symbols from imported modules automatically available

#### Error Diagnostics

- **Real-time error reporting**: Immediate feedback as you type
- **Enhanced error messages**: Detailed explanations and fix suggestions
- **Error categorization**: Errors organized by severity and type
- **Performance warnings**: Suggestions for optimizing code
- **Style recommendations**: Code quality improvements
- **Cross-module error detection**: Errors detected across imported modules
- **Performance analysis**: Built-in performance bottleneck detection

#### Code Navigation

- **Go to Definition**: `Ctrl+Click` on any symbol
- **Find All References**: `Shift+F12` on any symbol
- **Symbol Search**: `Ctrl+T` for workspace symbols
- **Document Symbols**: `Ctrl+Shift+O` for file symbols
- **Workspace Symbols**: Search across entire workspace
- **Cross-Module Navigation**: Navigate between symbols across different modules
- **Type Definition Navigation**: Go to type definitions
- **Implementation Finding**: Find implementations of interfaces

#### Code Actions

- **Quick Fixes**: Automatic fixes for common errors
- **Refactoring**: Extract function, inline variable, rename symbol
- **Code Generation**: Generate boilerplate code and patterns
- **Import Organization**: Automatically organize imports

## Language Server Features

### Symbol Finding

Ligature's LSP implementation provides professional-grade symbol finding capabilities:

#### Cross-File Symbol Finding

```ligature
-- In file: user.lig
type User = {
    name: String,
    age: Integer,
    email: String
};

let create_user = \name age email -> {
    name = name,
    age = age,
    email = email
};

-- In file: main.lig
import user;

let admin = user.create_user "Admin" 30 "admin@example.com";
-- ^ Go to definition works across files
-- ^ Find all references works across workspace
```

#### Import Resolution Integration

```ligature
-- Automatic module loading and symbol resolution
import std.collections.list;
import std.core.string;

let numbers = list.from_array [1, 2, 3, 4, 5];
let greeting = string.concat "Hello, " "World!";
-- ^ Symbols from imported modules are automatically available
-- ^ Go to definition navigates to the actual module files
```

#### Workspace Symbol Search

```ligature
-- Search for any symbol across the entire workspace
-- Ctrl+T: Search for "User" finds:
-- - type User in user.lig
-- - create_user function in user.lig
-- - Any other references to User
```

### Advanced LSP Capabilities

#### Enhanced References Provider

```ligature
-- Find all references to a symbol across the entire workspace
let config = { port = 8080, host = "localhost" };

-- In multiple files:
let server_config = { ...config, timeout = 30 };
let client_config = { ...config, timeout = 10 };
-- ^ Find all references to "config" shows all usages
```

#### Enhanced Definition Provider

```ligature
-- Go to definition works across module boundaries
import user;

let user = user.create_user "Alice" 25 "alice@example.com";
-- ^ Ctrl+Click on create_user navigates to user.lig
```

#### Enhanced Symbol Provider

```ligature
-- Workspace symbols include symbols from imported modules
-- Ctrl+T shows symbols from:
-- - Current file
-- - Imported modules
-- - All workspace files
```

### Module System Integration

#### Import Resolution

```ligature
-- Automatic module discovery and loading
import std.collections.list;
import std.core.string;
import my_module.types;

-- LSP automatically:
-- - Resolves import paths
-- - Loads module symbols
-- - Provides completion for imported symbols
-- - Handles cross-module navigation
```

#### Dependency Tracking

```ligature
-- LSP tracks dependencies between modules
-- When a module changes:
-- - Dependent modules are re-analyzed
-- - Symbol information is updated
-- - Error diagnostics are refreshed
```

## Configuration

### LSP Server Configuration

Configure the LSP server through `lsp-server.toml`:

```toml
[server]
name = "ligature-lsp"
version = "1.0.0"

[server.capabilities]
completion = true
definition = true
references = true
symbol_search = true
diagnostics = true
code_actions = true

[server.performance]
cache_size = 10000
cache_ttl = 300
parallel_processing = true

[server.features]
cross_module_navigation = true
import_resolution = true
symbol_finding = true
performance_monitoring = true
```

### VS Code Extension Configuration

Configure the VS Code extension through `settings.json`:

```json
{
  "ligature.enableSymbolFinding": true,
  "ligature.enableCrossModuleNavigation": true,
  "ligature.enableImportResolution": true,
  "ligature.enablePerformanceMonitoring": true,
  "ligature.cacheSize": 10000,
  "ligature.cacheTTL": 300,
  "ligature.enableParallelProcessing": true
}
```

## Performance Features

### Symbol Caching

```ligature
-- LSP caches symbol information for performance
-- Cache includes:
-- - Symbol definitions
-- - Import resolutions
-- - Cross-module references
-- - Type information

-- Cache is automatically invalidated when files change
```

### Real-time Updates

```ligature
-- Symbol information updates in real-time
-- When you modify a file:
-- - Symbol information is immediately updated
-- - Cross-module references are refreshed
-- - Error diagnostics are recalculated
-- - Completion suggestions are updated
```

## Troubleshooting

### Common Issues

#### Symbol Not Found

```ligature
-- Problem: Symbol not found in imported module
import my_module;

let result = my_module.some_function;  -- Error: symbol not found

-- Solution: Check module exports
-- Ensure my_module exports some_function
-- Check import path is correct
```

#### Import Resolution Issues

```ligature
-- Problem: Import not resolving
import std.collections.list;  -- Error: module not found

-- Solution: Check register configuration
-- Ensure std register is installed
-- Verify module path is correct
```

#### Performance Issues

```ligature
-- Problem: Slow symbol finding
-- Solution: Adjust cache settings
-- Increase cache size
-- Reduce cache TTL
-- Enable parallel processing
```

### Debug Information

Enable debug logging for troubleshooting:

```json
{
  "ligature.debug": true,
  "ligature.logLevel": "debug",
  "ligature.enablePerformanceLogging": true
}
```

## Best Practices

### Module Organization

```ligature
-- Organize modules for optimal LSP performance
-- Use clear module hierarchies
-- Export only necessary symbols
-- Use descriptive module names

-- Good:
module user.types;
module user.operations;
module user.validation;

-- Avoid:
module utils;  -- Too generic
module a;      -- Too short
```

### Import Management

```ligature
-- Use selective imports for better performance
import std.collections.{ list, map };  -- Only import needed symbols

-- Avoid wildcard imports
import std.*;  -- Imports everything, slower performance
```

### Symbol Naming

```ligature
-- Use descriptive symbol names for better search
let create_user_with_validation = \name age email -> {
  -- Implementation
};

-- Avoid generic names
let f = \x -> x;  -- Hard to find in symbol search
```

## Conclusion

Ligature's IDE integration provides:

- **Professional-grade symbol finding** with cross-file navigation
- **Complete import resolution** with dependency tracking
- **Real-time performance monitoring** and optimization
- **Advanced LSP capabilities** comparable to mature IDEs
- **Comprehensive error diagnostics** with fix suggestions
- **Cross-module navigation** and workspace symbol search

The IDE integration is designed to provide a professional development experience with all the tools needed for productive Ligature development.
