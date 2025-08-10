# Quick Start Guide - Ligature IDE Integration

Get up and running with Ligature language support in your IDE in just a few minutes!

## Prerequisites

- **Rust and Cargo** (for building the language server)
- **Node.js and npm** (for VS Code extension)
- **VS Code** (or any LSP-compatible editor)

## Quick Setup (5 minutes)

### Step 1: Build the Language Server

```bash
# From the project root
cargo build --release -p ligature-lsp
```

### Step 2: Install VS Code Extension

```bash
# Navigate to the extension directory
cd apps/editor-plugins/vscode-ligature

# Install dependencies and build
npm install
npm run compile

# Package and install the extension
npm install -g @vscode/vsce
vsce package
code --install-extension vscode-ligature-*.vsix
```

### Step 3: Test the Setup

1. **Open VS Code**
2. **Create a new file** with `.lig` extension
3. **Start typing** Ligature code:

```ocaml
// Test the extension
fun add(x: Int, y: Int) -> Int = x + y
let result = add(10, 20)
```

You should see:

- ✅ Syntax highlighting
- ✅ Error diagnostics (if any)
- ✅ Code completion suggestions
- ✅ Hover information

## Alternative: Development Installation

For development or testing:

```bash
cd apps/editor-plugins/vscode-ligature
npm install
npm run compile
```

Then in VS Code:

1. Open the extension folder
2. Press `F5` to launch Extension Development Host
3. Open a `.lig` file to test

## Basic Usage

### Opening Ligature Files

- Files with `.lig` extension automatically get Ligature language support
- Syntax highlighting is applied immediately
- Error diagnostics appear in real-time

### Code Completion

- Type `fun` and press `Tab` for function template
- Type `let` and press `Tab` for let binding
- Type `if` and press `Tab` for if-then-else expression
- Type `match` and press `Tab` for pattern matching

### Navigation

- `Ctrl+Click` on any symbol to go to definition
- `Shift+F12` to find all references
- `F2` to rename a symbol
- `Ctrl+Shift+O` to see document symbols

### Error Diagnostics

- Red squiggly lines show errors
- Yellow squiggly lines show warnings
- Hover over errors for detailed explanations
- Use `Ctrl+Shift+M` to open Problems panel

### Code Actions

- Lightbulb icon (💡) appears for quick fixes
- `Ctrl+.` to see available code actions
- Automatic suggestions for common issues

## Configuration

### Basic Settings

Add to your VS Code settings (`Ctrl+,`):

```json
{
  "ligature.languageServer.enabled": true,
  "ligature.diagnostics.enabled": true,
  "ligature.completion.enabled": true,
  "ligature.formatting.enabled": true
}
```

### Advanced Settings

```json
{
  "ligature.languageServer.path": "ligature-lsp",
  "ligature.languageServer.args": ["--enhanced"],
  "ligature.formatting.indentSize": 2,
  "ligature.formatting.maxLineLength": 80
}
```

## Troubleshooting

### Language Server Not Starting

1. **Check if the server is built**:

   ```bash
   cargo build --release -p ligature-lsp
   ```

2. **Verify the path in settings**:

   ```json
   {
     "ligature.languageServer.path": "/path/to/ligature-lsp"
   }
   ```

3. **Check Output panel** for error messages

### No Completions or Diagnostics

1. **Ensure the language server is running** (check status bar)
2. **Verify file has `.lig` extension**
3. **Check if features are enabled** in settings
4. **Restart the language server**: `Ctrl+Shift+P` → "Ligature: Restart Language Server"

### Performance Issues

1. **Reduce workspace size**:

   ```json
   {
     "ligature.workspace.maxFiles": 500
   }
   ```

2. **Disable unnecessary features**:
   ```json
   {
     "ligature.inlayHints.enabled": false,
     "ligature.workspace.enableWorkspaceSymbols": false
   }
   ```

## Other Editors

### Neovim

```lua
require'lspconfig'.ligature_lsp.setup{
  cmd = {"ligature-lsp", "--enhanced"},
  filetypes = {"ligature"}
}
```

### Emacs

```elisp
(lsp-register-client
 (make-lsp-client :new-connection (lsp-stdio-connection '("ligature-lsp" "--enhanced"))
                  :major-modes '(ligature-mode)
                  :server-id 'ligature-lsp))
```

## Next Steps

### Learn More

- **Language Reference**: See the main Ligature documentation
- **IDE Integration Guide**: Comprehensive IDE features documentation
- **Error Reporting Guide**: Understanding error messages and diagnostics
- **Configuration Guide**: Advanced settings and customization

### Examples

Try these examples to test different features:

#### Function Definition

```ocaml
fun factorial(n: Int) -> Int =
  if n <= 1 then 1
  else n * factorial(n - 1)
```

#### Pattern Matching

```ocaml
fun safeDivide(x: Int, y: Int) -> Option<Int> =
  match y with
    | 0 -> None
    | _ -> Some(x / y)
```

#### Type Definition

```ocaml
type Result<T, E> =
  | Ok of T
  | Error of E
```

#### Import and Usage

```ocaml
import "stdlib/core" as core
let result = core.add(10, 20)
```

## Getting Help

### Common Issues

- **Build errors**: Check Rust toolchain and dependencies
- **Extension not loading**: Verify VS Code version compatibility
- **No language support**: Ensure `.lig` file extension
- **Performance problems**: Check workspace size and settings

### Debugging

Enable verbose logging:

```json
{
  "ligature.languageServer.trace": "verbose"
}
```

Check Output panels:

- "Ligature Language Server" for server logs
- "Ligature Language Server Trace" for detailed communication

### Support

- **GitHub Issues**: Report bugs and feature requests
- **Documentation**: Comprehensive guides and references
- **Community**: Join discussions and get help

## Success Indicators

You know everything is working when you see:

✅ **Status bar** shows "Ligature" with a checkmark  
✅ **Syntax highlighting** colors your code  
✅ **Error diagnostics** appear in real-time  
✅ **Code completion** suggests relevant items  
✅ **Hover information** shows details on symbols  
✅ **Navigation** works (Ctrl+Click, F12, etc.)

Congratulations! You now have a fully functional Ligature development environment! 🎉
