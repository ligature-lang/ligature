#!/bin/bash

# Test script for the Ligature LSP server
# This script helps debug the LSP server by sending test messages

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}Building LSP server...${NC}"
cargo build --package ligature-lsp

echo -e "${YELLOW}Testing LSP server...${NC}"

# Create a temporary test file
TEST_FILE="test_lsp.lig"
cat > "$TEST_FILE" << 'EOF'
let x = 42;
let y = "hello";
let z = { a = 1, b = 2 };
EOF

# Test the server with a simple LSP initialization message
echo -e "${GREEN}Testing LSP initialization...${NC}"

# Initialize message
INIT_MSG='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":123,"rootUri":"file:///tmp","capabilities":{"textDocument":{"completion":{"completionItem":{"snippetSupport":true}}}},"trace":"verbose"}}'

# Send the message to the LSP server
echo "$INIT_MSG" | cargo run --package ligature-lsp 2>&1 | head -20

echo -e "${GREEN}Testing file parsing...${NC}"
cargo run --bin reed -- parse --file "$TEST_FILE"

echo -e "${GREEN}Cleaning up...${NC}"
rm -f "$TEST_FILE"

echo -e "${GREEN}LSP test completed!${NC}"
echo -e "${YELLOW}To test with VS Code:${NC}"
echo "1. Open VS Code in this directory"
echo "2. Open a .lig file"
echo "3. Check the Output panel for LSP logs"
echo "4. Use the debug configurations in launch.json" 