#!/bin/bash

# Build script for VS Code Ligature Extension

set -e

echo "🚀 Building VS Code Ligature Extension..."

# Check if we're in the right directory
if [ ! -f "package.json" ]; then
    echo "❌ Error: package.json not found. Please run this script from the vscode-ligature directory."
    exit 1
fi

# Check if Node.js is installed
if ! command -v node &> /dev/null; then
    echo "❌ Error: Node.js is not installed. Please install Node.js first."
    exit 1
fi

# Check if npm is installed
if ! command -v npm &> /dev/null; then
    echo "❌ Error: npm is not installed. Please install npm first."
    exit 1
fi

echo "📦 Installing dependencies..."
npm install

echo "🔨 Compiling TypeScript..."
npm run compile

echo "🧪 Running tests..."
npm test

echo "🔍 Running linter..."
npm run lint

echo "✅ Build completed successfully!"

# Check if vsce is available for packaging
if command -v vsce &> /dev/null; then
    echo "📦 Packaging extension..."
    vsce package
    echo "✅ Extension packaged successfully!"
else
    echo "💡 Tip: Install vsce globally to package the extension:"
    echo "   npm install -g @vscode/vsce"
    echo "   Then run: vsce package"
fi

echo ""
echo "🎉 Extension is ready for development!"
echo ""
echo "To test the extension:"
echo "1. Open this folder in VS Code"
echo "2. Press F5 to launch Extension Development Host"
echo "3. Open a .lig file to test the extension"
echo ""
echo "To install the extension:"
echo "1. Build the language server: cargo build --release -p ligature-lsp"
echo "2. Package the extension: vsce package"
echo "3. Install: code --install-extension vscode-ligature-*.vsix" 