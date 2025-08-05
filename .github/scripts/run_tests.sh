#!/bin/bash

# Ligature Language Test Runner
# This script runs all tests with proper configuration and reporting

set -e  # Exit on any error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
CARGO_FLAGS=""
TEST_FLAGS="--nocapture"
VERBOSE=false
RUN_INTEGRATION=true
RUN_PROPERTY=true
RUN_DIFFERENTIAL=true
BENCHMARK=false

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
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  -h, --help              Show this help message"
    echo "  -v, --verbose           Enable verbose output"
    echo "  -i, --integration       Run only integration tests"
    echo "  -p, --property          Run only property tests"
    echo "  -d, --differential      Run only differential tests"
    echo "  -b, --benchmark         Run benchmarks"
    echo "  --release               Run tests in release mode"
    echo "  --no-capture            Show test output (default)"
    echo "  --test-threads=N        Set number of test threads"
    echo ""
    echo "Examples:"
    echo "  $0                      # Run all tests"
    echo "  $0 -v                   # Run all tests with verbose output"
    echo "  $0 -i                   # Run only integration tests"
    echo "  $0 --release            # Run tests in release mode"
    echo "  $0 --test-threads=1     # Run tests single-threaded"
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_usage
            exit 0
            ;;
        -v|--verbose)
            VERBOSE=true
            TEST_FLAGS="$TEST_FLAGS --nocapture"
            shift
            ;;
        -i|--integration)
            RUN_INTEGRATION=true
            RUN_PROPERTY=false
            RUN_DIFFERENTIAL=false
            shift
            ;;
        -p|--property)
            RUN_INTEGRATION=false
            RUN_PROPERTY=true
            RUN_DIFFERENTIAL=false
            shift
            ;;
        -d|--differential)
            RUN_INTEGRATION=false
            RUN_PROPERTY=false
            RUN_DIFFERENTIAL=true
            shift
            ;;
        -b|--benchmark)
            BENCHMARK=true
            shift
            ;;
        --release)
            CARGO_FLAGS="$CARGO_FLAGS --release"
            shift
            ;;
        --no-capture)
            TEST_FLAGS="$TEST_FLAGS --nocapture"
            shift
            ;;
        --test-threads)
            TEST_FLAGS="$TEST_FLAGS --test-threads=$2"
            shift 2
            ;;
        *)
            print_error "Unknown option: $1"
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

# Check if cargo is available
if ! command -v cargo &> /dev/null; then
    print_error "Cargo not found. Please install Rust and Cargo."
    exit 1
fi

print_status "Starting Ligature Language Test Suite"
print_status "Configuration:"
print_status "  Cargo flags: $CARGO_FLAGS"
print_status "  Test flags: $TEST_FLAGS"
print_status "  Verbose: $VERBOSE"
print_status "  Integration tests: $RUN_INTEGRATION"
print_status "  Property tests: $RUN_PROPERTY"
print_status "  Differential tests: $RUN_DIFFERENTIAL"
print_status "  Benchmark: $BENCHMARK"

# Function to run tests with timing
run_tests() {
    local test_type=$1
    local test_args=$2
    
    print_status "Running $test_type tests..."
    local start_time=$(date +%s)
    
    if cargo test $CARGO_FLAGS $test_args $TEST_FLAGS; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        print_success "$test_type tests completed in ${duration}s"
        return 0
    else
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        print_error "$test_type tests failed after ${duration}s"
        return 1
    fi
}

# Function to run benchmarks
run_benchmarks() {
    if [[ "$BENCHMARK" == "true" ]]; then
        print_status "Running benchmarks..."
        if cargo bench $CARGO_FLAGS; then
            print_success "Benchmarks completed"
        else
            print_error "Benchmarks failed"
            return 1
        fi
    fi
}

# Main test execution
main() {
    local exit_code=0
    
    # Run unit tests first (these are fast and catch basic issues)
    print_status "Running unit tests..."
    if ! cargo test $CARGO_FLAGS --lib $TEST_FLAGS; then
        print_error "Unit tests failed"
        exit_code=1
    else
        print_success "Unit tests passed"
    fi
    
    # Run integration tests
    if [[ "$RUN_INTEGRATION" == "true" ]]; then
        if ! run_tests "integration" "integration"; then
            exit_code=1
        fi
    fi
    
    # Run property tests
    if [[ "$RUN_PROPERTY" == "true" ]]; then
        if ! run_tests "property" "property"; then
            exit_code=1
        fi
    fi
    
    # Run differential tests
    if [[ "$RUN_DIFFERENTIAL" == "true" ]]; then
        if ! run_tests "differential" "differential"; then
            exit_code=1
        fi
    fi
    
    # Run benchmarks
    run_benchmarks || exit_code=1
    
    # Final summary
    echo ""
    if [[ $exit_code -eq 0 ]]; then
        print_success "All tests completed successfully!"
    else
        print_error "Some tests failed. Please check the output above."
    fi
    
    return $exit_code
}

# Run the main function
main 