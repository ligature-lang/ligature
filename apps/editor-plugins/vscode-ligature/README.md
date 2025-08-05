# Ligature Language Support for VS Code

A comprehensive VS Code extension providing complete language support for the Ligature programming language, including syntax highlighting, IntelliSense, error diagnostics, and advanced IDE features.

## Features

### ✨ Core Language Support

- **Syntax Highlighting**: Full syntax highlighting for Ligature code with semantic token support
- **Language Server Integration**: Complete LSP support with enhanced features
- **Error Diagnostics**: Real-time error reporting with detailed explanations and quick fixes
- **Code Completion**: Intelligent autocomplete with context awareness and fuzzy matching
- **Hover Information**: Rich documentation and type information on hover

### 🚀 Advanced IDE Features

- **Go to Definition**: Navigate to symbol definitions with Ctrl+Click
- **Find All References**: Discover all usages of symbols across your codebase
- **Symbol Renaming**: Safely rename symbols with automatic reference updates
- **Document Formatting**: Automatic code formatting with customizable rules
- **Code Actions**: Quick fixes and refactoring suggestions
- **Inlay Hints**: Type hints and parameter names displayed inline
- **Semantic Highlighting**: Enhanced syntax highlighting with semantic token support

### 🎯 Enhanced Developer Experience

- **Advanced Snippets**: 50+ pre-built code snippets for common patterns
- **Auto-indentation**: Smart indentation based on Ligature syntax
- **Bracket Matching**: Automatic bracket and parenthesis matching
- **Comment Support**: Line and block comment support
- **Status Bar Integration**: Real-time language server status
- **Format on Save/Paste**: Automatic formatting when saving or pasting code

### 🔧 Advanced Refactoring Tools

- **Extract Function**: Extract selected code into a new function
- **Inline Variable**: Inline variable usage with automatic replacement
- **Extract Constant**: Extract repeated values into named constants
- **Generate Tests**: Automatically generate test templates for functions
- **Generate Documentation**: Create documentation comments for functions

### 🎨 Professional-Grade Features

- **Context-Aware Completions**: Intelligent suggestions based on current context
- **Type-Aware Hover**: Enhanced hover information with type details
- **Performance Optimizations**: Incremental parsing and intelligent caching
- **Workspace Symbol Search**: Find symbols across your entire workspace
- **Import Organization**: Automatic import organization and management

## Installation

### Prerequisites

1. **Build the Ligature Language Server**:

   ```bash
   # From the project root
   cargo build --release -p ligature-lsp
   ```

2. **Install Node.js and npm** (for building the extension)

### Building the Extension

1. **Navigate to the extension directory**:

   ```bash
   cd apps/editor-plugins/vscode-ligature
   ```

2. **Install dependencies**:

   ```bash
   npm install
   ```

3. **Build the extension**:

   ```bash
   npm run compile
   ```

4. **Package the extension** (optional):

   ```bash
   # Install vsce if you haven't already
   npm install -g @vscode/vsce

   # Package the extension
   vsce package
   ```

### Installing in VS Code

#### Development Installation

1. Open the extension folder in VS Code
2. Press `F5` to launch a new Extension Development Host
3. Open a `.lig` file to test the extension

#### Production Installation

1. Install the packaged `.vsix` file:
   ```bash
   code --install-extension vscode-ligature-0.1.0.vsix
   ```
2. Or install from the VS Code marketplace (when published)

## Configuration

### Language Server Settings

The extension can be configured through VS Code settings:

```json
{
  "ligature.languageServer.enabled": true,
  "ligature.languageServer.path": "ligature-lsp",
  "ligature.languageServer.args": ["--enhanced"],
  "ligature.languageServer.trace": "off"
}
```

### Enhanced Completion Settings

```json
{
  "ligature.completion.enabled": true,
  "ligature.completion.enhanced": true,
  "ligature.completion.enableSnippets": true,
  "ligature.completion.enableAutoImport": true,
  "ligature.completion.enableFuzzyMatching": true,
  "ligature.completion.enableContextAware": true
}
```

### Formatting Settings

```json
{
  "ligature.formatting.enabled": true,
  "ligature.formatting.indentSize": 2,
  "ligature.formatting.maxLineLength": 80,
  "ligature.formatting.enableOnSave": true,
  "ligature.formatting.enableOnPaste": true
}
```

### Hover and Documentation Settings

```json
{
  "ligature.hover.enabled": true,
  "ligature.hover.enableTypeInfo": true,
  "ligature.hover.enableDocumentation": true
}
```

### Code Actions Settings

```json
{
  "ligature.codeActions.enabled": true,
  "ligature.codeActions.enableQuickFixes": true,
  "ligature.codeActions.enableRefactoring": true,
  "ligature.codeActions.enableCodeGeneration": true
}
```

### Inlay Hints Settings

```json
{
  "ligature.inlayHints.enabled": true,
  "ligature.inlayHints.enableTypeHints": true,
  "ligature.inlayHints.enableParameterHints": true
}
```

### Semantic Highlighting Settings

```json
{
  "ligature.semanticHighlighting.enabled": true,
  "ligature.semanticHighlighting.enableTypeHighlighting": true,
  "ligature.semanticHighlighting.enableFunctionHighlighting": true
}
```

### Performance Settings

```json
{
  "ligature.performance.enableIncrementalParsing": true,
  "ligature.performance.enableCaching": true,
  "ligature.performance.maxCacheSize": 100
}
```

## Usage

### Basic Features

- **Syntax Highlighting**: Automatically highlights Ligature syntax
- **Error Detection**: Real-time error reporting with squiggly underlines
- **Code Completion**: Press `Ctrl+Space` for intelligent completions
- **Hover Information**: Hover over symbols for detailed information

### Advanced Features

#### Refactoring Commands

- **Extract Function** (`Ctrl+Shift+R E`): Extract selected code into a new function
- **Inline Variable** (`Ctrl+Shift+R I`): Inline variable usage
- **Extract Constant** (`Ctrl+Shift+R C`): Extract repeated values into constants
- **Generate Tests** (`Ctrl+Shift+T`): Generate test templates
- **Generate Documentation** (`Ctrl+Shift+D`): Create documentation comments

#### Navigation Commands

- **Go to Definition** (`Ctrl+Click`): Navigate to symbol definition
- **Find All References** (`Shift+F12`): Find all usages of a symbol
- **Rename Symbol** (`F2`): Rename symbols with automatic reference updates
- **Show Document Symbols** (`Ctrl+Shift+O`): Browse symbols in current file
- **Show Workspace Symbols** (`Ctrl+T`): Search symbols across workspace

#### Formatting Commands

- **Format Document** (`Shift+Alt+F`): Format entire document
- **Format Selection**: Format selected code
- **Organize Imports**: Organize and clean up imports

### Snippets

The extension includes 50+ code snippets for common Ligature patterns:

- `fun` - Function definition
- `let` - Let binding
- `if` - If expression
- `match` - Pattern matching
- `type` - Type definition
- `record` - Record type
- `import` - Import statement
- `test` - Test definition
- `doc` - Documentation comment
- And many more...

### Context-Aware Features

The extension provides intelligent, context-aware features:

- **Smart Completions**: Suggestions based on current context (function, type, import, etc.)
- **Type Inference**: Automatic type hints and suggestions
- **Import Suggestions**: Automatic import suggestions for undefined symbols
- **Error Fixes**: Quick fixes for common errors and warnings

## Troubleshooting

### Language Server Issues

If the language server fails to start:

1. Check that `ligature-lsp` is built and available in your PATH
2. Verify the path in settings: `ligature.languageServer.path`
3. Check the output panel for error messages
4. Try restarting the language server with `Ctrl+Shift+P` → "Ligature: Restart Language Server"

### Performance Issues

If you experience performance issues:

1. Disable semantic highlighting: `ligature.semanticHighlighting.enabled = false`
2. Reduce cache size: `ligature.performance.maxCacheSize = 50`
3. Disable incremental parsing: `ligature.performance.enableIncrementalParsing = false`

### Feature Not Working

If a specific feature isn't working:

1. Check that the feature is enabled in settings
2. Verify the language server is running (check status bar)
3. Try restarting VS Code
4. Check the output panel for error messages

## Contributing

Contributions are welcome! Please see the [Contributing Guide](../../CONTRIBUTING.md) for details.

### Development Setup

1. Clone the repository
2. Build the language server: `cargo build -p ligature-lsp`
3. Install extension dependencies: `npm install`
4. Build the extension: `npm run compile`
5. Press `F5` to launch the extension development host

### Testing

Run the test suite:

```bash
npm test
```

## License

This extension is licensed under the MIT License. See the [LICENSE](../../LICENSE) file for details.

## Support

- **Issues**: Report bugs and request features on [GitHub](https://github.com/ligature-lang/ligature/issues)
- **Documentation**: See the [Ligature documentation](https://github.com/ligature-lang/ligature/docs)
- **Community**: Join the discussion on [GitHub Discussions](https://github.com/ligature-lang/ligature/discussions)

## Changelog

### Version 0.1.0

- ✨ Initial release with basic language support
- 🚀 Advanced IDE features including IntelliSense and refactoring
- 🎨 Professional-grade development experience
- 🔧 Comprehensive configuration options
- 📚 Enhanced documentation and examples
