#!/bin/bash

# Ligature Coverage Script
# This script helps run coverage locally for development

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to show usage
show_usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Run test coverage locally for the Ligature project.

OPTIONS:
    -h, --help              Show this help message
    -c, --crate <crate>     Run coverage for specific crate only
    -t, --threshold <num>   Set coverage threshold (default: 80)
    -o, --output <dir>      Output directory for reports (default: coverage)
    -f, --format <format>   Output format: html, lcov, text (default: all)
    -v, --verbose           Verbose output
    --no-clean              Don't clean previous coverage data
    --upload                Upload to Codecov (requires CODECOV_TOKEN)

EXAMPLES:
    $0                      # Run coverage for all crates
    $0 -c ligature-parser   # Run coverage for specific crate
    $0 -t 90               # Set 90% threshold
    $0 --format html       # Generate HTML report only
    $0 --upload            # Upload to Codecov

EOF
}

# Parse command line arguments
CRATE=""
THRESHOLD=80
OUTPUT_DIR="coverage"
FORMAT="all"
VERBOSE=false
CLEAN=true
UPLOAD=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_usage
            exit 0
            ;;
        -c|--crate)
            CRATE="$2"
            shift 2
            ;;
        -t|--threshold)
            THRESHOLD="$2"
            shift 2
            ;;
        -o|--output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        -f|--format)
            FORMAT="$2"
            shift 2
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        --no-clean)
            CLEAN=false
            shift
            ;;
        --upload)
            UPLOAD=true
            shift
            ;;
        -*)
            print_error "Unknown option: $1"
            show_usage
            exit 1
            ;;
        *)
            print_error "Unknown argument: $1"
            show_usage
            exit 1
            ;;
    esac
done

# Check if we're in the right directory
if [[ ! -f "Cargo.toml" ]]; then
    print_error "Cargo.toml not found. Please run this script from the project root."
    exit 1
fi

# Check if cargo-llvm-cov is installed
if ! command -v cargo-llvm-cov &> /dev/null; then
    print_warning "cargo-llvm-cov not found. Installing..."
    cargo install cargo-llvm-cov
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Clean previous coverage data if requested
if [[ "$CLEAN" == "true" ]]; then
    print_status "Cleaning previous coverage data..."
    cargo llvm-cov clean
fi

# Set environment variables for coverage
export CARGO_INCREMENTAL=0
export RUSTFLAGS="-Cinstrument-coverage"
export LLVM_PROFILE_FILE="$OUTPUT_DIR/cargo-test-%p-%m.profraw"

print_status "Running coverage with threshold: ${THRESHOLD}%"

# Run coverage
if [[ -n "$CRATE" ]]; then
    print_status "Running coverage for crate: $CRATE"
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "html" ]]; then
        cargo llvm-cov --all-features --package "$CRATE" --html --output-dir "$OUTPUT_DIR/html-$CRATE"
    fi
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "lcov" ]]; then
        cargo llvm-cov --all-features --package "$CRATE" --lcov --output-path "$OUTPUT_DIR/lcov-$CRATE.info"
    fi
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "text" ]]; then
        cargo llvm-cov --all-features --package "$CRATE" --text > "$OUTPUT_DIR/coverage-$CRATE.txt"
    fi
else
    print_status "Running coverage for all crates"
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "html" ]]; then
        cargo llvm-cov --all-features --workspace --html --output-dir "$OUTPUT_DIR/html"
    fi
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "lcov" ]]; then
        cargo llvm-cov --all-features --workspace --lcov --output-path "$OUTPUT_DIR/lcov.info"
    fi
    
    if [[ "$FORMAT" == "all" || "$FORMAT" == "text" ]]; then
        cargo llvm-cov --all-features --workspace --text > "$OUTPUT_DIR/coverage.txt"
    fi
fi

# Check coverage threshold
print_status "Checking coverage threshold..."
if [[ -n "$CRATE" ]]; then
    COVERAGE=$(cargo llvm-cov --all-features --package "$CRATE" --text | grep "Total" | awk '{print $2}' | sed 's/%//')
else
    COVERAGE=$(cargo llvm-cov --all-features --workspace --text | grep "Total" | awk '{print $2}' | sed 's/%//')
fi

print_status "Coverage: ${COVERAGE}%"

if (( $(echo "$COVERAGE >= $THRESHOLD" | bc -l) )); then
    print_success "Coverage threshold passed! (${COVERAGE}% >= ${THRESHOLD}%)"
else
    print_error "Coverage threshold failed! (${COVERAGE}% < ${THRESHOLD}%)"
    exit 1
fi

# Upload to Codecov if requested
if [[ "$UPLOAD" == "true" ]]; then
    if [[ -z "${CODECOV_TOKEN:-}" ]]; then
        print_error "CODECOV_TOKEN environment variable not set"
        exit 1
    fi
    
    print_status "Uploading to Codecov..."
    if [[ -n "$CRATE" ]]; then
        codecov -f "$OUTPUT_DIR/lcov-$CRATE.info" -t "$CODECOV_TOKEN"
    else
        codecov -f "$OUTPUT_DIR/lcov.info" -t "$CODECOV_TOKEN"
    fi
    print_success "Uploaded to Codecov"
fi

# Show summary
print_success "Coverage completed successfully!"
print_status "Reports generated in: $OUTPUT_DIR"

if [[ "$FORMAT" == "all" || "$FORMAT" == "html" ]]; then
    if [[ -n "$CRATE" ]]; then
        print_status "HTML report: $OUTPUT_DIR/html-$CRATE/index.html"
    else
        print_status "HTML report: $OUTPUT_DIR/html/index.html"
    fi
fi

if [[ "$FORMAT" == "all" || "$FORMAT" == "text" ]]; then
    if [[ -n "$CRATE" ]]; then
        print_status "Text report: $OUTPUT_DIR/coverage-$CRATE.txt"
    else
        print_status "Text report: $OUTPUT_DIR/coverage.txt"
    fi
fi 