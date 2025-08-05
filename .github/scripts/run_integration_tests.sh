#!/bin/bash

# Integration Tests Runner for Ligature
# This script runs all integration tests to verify the enhanced type inference system

set -e

echo "🧪 Running Ligature Integration Tests"
echo "======================================"

# Run the enhanced type inference tests
echo ""
echo "1. Enhanced Type Inference Tests:"
cargo run --example test_type_inference

# Run the evaluation engine tests
echo ""
echo "2. Evaluation Engine Tests:"
cargo run --example test_evaluation

# Run the parser tests
echo ""
echo "3. Parser Tests:"
cargo run --example test_parser

# Run the core type system tests
echo ""
echo "4. Core Type System Tests:"
cd crates/ligature-types && cargo test && cd ../..

# Run the evaluation engine unit tests
echo ""
echo "5. Evaluation Engine Unit Tests:"
cd crates/ligature-eval && cargo test && cd ../..

echo ""
echo "✅ All integration tests completed successfully!" 