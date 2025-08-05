# Import Resolution and Module Loading

The Ligature LSP server now includes comprehensive import resolution and module loading functionality that enables cross-module symbol resolution, completion, and navigation.

## Features

### Import Resolution
- **Relative imports**: Support for `./` and `../` path resolution
- **Register-based imports**: Support for imports from Ligature registers (e.g., `std.collections.list`)
- **Workspace imports**: Automatic resolution of modules within workspace folders
- **Nested module support**: Support for nested module structures with `mod.lig` files

### Module Loading
- **Automatic module discovery**: Recursively loads all `.lig` files in workspace folders
- **Module caching**: Efficient caching of loaded modules with file modification detection
- **Dependency tracking**: Maintains a dependency graph for cross-module references
- **Import cycle detection**: Prevents infinite recursion in import chains

### LSP Integration
- **Cross-module completion**: Provides completion suggestions from imported modules
- **Go to definition**: Navigate to symbol definitions across module boundaries
- **Find references**: Find all references to symbols across the entire workspace
- **Workspace symbols**: Search for symbols across all loaded modules

## Usage

### Basic Import Syntax

```ligature
// Relative imports
import "./utils"
import "../shared/types"

// Register imports
import "std.collections.list"
import "std.string"

// Selective imports
import "std.math" { sqrt, pow, log }

// Aliased imports
import "std.collections" as collections
```

### Module Structure

A Ligature module can be either a single file or a directory with a `mod.lig` file:

```
my_module/
├── mod.lig          # Main module file
├── utils.lig        # Submodule
└── types.lig        # Submodule
```

### Export Syntax

```ligature
// Export individual items
export let my_function = \x -> x + 1
export type MyType = { name: String, value: Int }

// Export all items (default behavior)
let internal_function = \x -> x * 2  // Not exported
export let public_function = \x -> internal_function x
```

## Configuration

The import resolution service can be configured through the LSP server settings:

```json
{
  "ligature-lsp": {
    "enableCrossFileSymbols": true,
    "maxWorkspaceFiles": 1000,
    "includePatterns": ["**/*.lig"],
    "excludePatterns": ["**/target/**", "**/node_modules/**"]
  }
}
```

## Scratch Directory

Temporary Ligature files are stored in the `registers/_scratch/` directory. This directory is automatically created when needed and can be used for:

- Temporary module files during development
- Generated code
- Test files

## API Reference

### ImportResolutionService

The main service for handling import resolution and module loading.

#### Methods

- `load_module_from_uri(uri: &str) -> AstResult<Module>`: Load a module from a file URI
- `resolve_module_imports(uri: &str) -> AstResult<()>`: Resolve all imports in a module
- `get_imported_modules(uri: &str) -> Vec<String>`: Get all modules imported by a given module
- `get_importing_modules(uri: &str) -> Vec<String>`: Get all modules that import a given module
- `find_symbol_references(symbol_name: &str, source_uri: &str) -> Vec<Location>`: Find all references to a symbol
- `clear_cache()`: Clear the module cache
- `invalidate_module(uri: &str)`: Invalidate a specific module in the cache

### LSP Server Integration

The import resolution service is automatically integrated into the LSP server and provides:

- **Enhanced completion**: Includes symbols from imported modules
- **Cross-module navigation**: Go to definition and find references work across modules
- **Workspace symbol search**: Search for symbols across all loaded modules
- **Automatic module loading**: Modules are loaded when files are opened or changed

## Examples

See the `examples/` directory for working examples of import resolution:

- `import_resolution_example.lig`: Demonstrates various import patterns
- `math_utils.lig`: A utility module with exported functions and types

## Implementation Details

### Module Resolution Strategy

1. **Relative imports**: Resolved relative to the importing file's directory
2. **Register imports**: Resolved using the module resolver with register paths
3. **Workspace imports**: Searched in workspace folders and common subdirectories

### Caching Strategy

- Modules are cached by URI with file modification timestamps
- Cache invalidation occurs when files are modified or deleted
- Dependency tracking ensures dependent modules are invalidated when dependencies change

### Performance Considerations

- Module loading is asynchronous and non-blocking
- Workspace module loading occurs in the background after server initialization
- Cache size is limited by available memory
- File system operations are minimized through intelligent caching 