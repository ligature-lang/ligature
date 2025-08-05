#!/bin/bash

# Benchmark runner script for Ligature
# Usage: ./benches/run_benchmarks.sh [options]

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default configuration
BENCHMARK_CRATES=("ligature-parser" "ligature-eval")
OUTPUT_FORMAT="human"
MEMORY_PROFILING=true
WARMUP_ITERATIONS=1000
MEASUREMENT_ITERATIONS=10000
TIMEOUT_SECONDS=30
VERBOSE=false
CUSTOM_BENCHMARKS=false
GENERATE_REPORTS=true

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

Options:
    -c, --crates CRATES     Comma-separated list of crates to benchmark (default: ligature-parser,ligature-eval)
    -f, --format FORMAT     Output format: human, json, csv, all (default: human)
    -m, --memory           Enable memory profiling (default: true)
    -w, --warmup N         Number of warmup iterations (default: 1000)
    -i, --iterations N     Number of measurement iterations (default: 10000)
    -t, --timeout N        Timeout in seconds (default: 30)
    -v, --verbose          Enable verbose output
    --custom               Run custom benchmarks only
    --no-reports           Don't generate reports
    -h, --help             Show this help message

Examples:
    $0                                    # Run all benchmarks with default settings
    $0 -c ligature-parser                 # Benchmark only the parser
    $0 -f json -m                         # Run with JSON output and memory profiling
    $0 --custom                           # Run only custom benchmarks
    $0 -w 500 -i 5000                     # Run with custom iteration counts

EOF
}

# Function to parse command line arguments
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -c|--crates)
                BENCHMARK_CRATES=(${2//,/ })
                shift 2
                ;;
            -f|--format)
                OUTPUT_FORMAT="$2"
                shift 2
                ;;
            -m|--memory)
                MEMORY_PROFILING=true
                shift
                ;;
            -w|--warmup)
                WARMUP_ITERATIONS="$2"
                shift 2
                ;;
            -i|--iterations)
                MEASUREMENT_ITERATIONS="$2"
                shift 2
                ;;
            -t|--timeout)
                TIMEOUT_SECONDS="$2"
                shift 2
                ;;
            -v|--verbose)
                VERBOSE=true
                shift
                ;;
            --custom)
                CUSTOM_BENCHMARKS=true
                shift
                ;;
            --no-reports)
                GENERATE_REPORTS=false
                shift
                ;;
            -h|--help)
                show_usage
                exit 0
                ;;
            *)
                print_error "Unknown option: $1"
                show_usage
                exit 1
                ;;
        esac
    done
}

# Function to check prerequisites
check_prerequisites() {
    print_status "Checking prerequisites..."
    
    # Check if cargo is available
    if ! command -v cargo &> /dev/null; then
        print_error "cargo is not installed or not in PATH"
        exit 1
    fi
    
    # Check if we're in a Rust project
    if [[ ! -f "Cargo.toml" ]]; then
        print_error "Not in a Rust project directory (Cargo.toml not found)"
        exit 1
    fi
    
    # Check if criterion is available
    if ! cargo search criterion &> /dev/null; then
        print_warning "criterion crate not found in registry, but this is normal"
    fi
    
    print_success "Prerequisites check passed"
}

# Function to run cargo benchmarks
run_cargo_benchmarks() {
    local crate_name="$1"
    print_status "Running cargo benchmarks for $crate_name..."
    
    local start_time=$(date +%s)
    
    if [[ "$VERBOSE" == "true" ]]; then
        if cargo bench --package "$crate_name"; then
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_success "Cargo benchmarks completed for $crate_name in ${duration}s"
        else
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_error "Cargo benchmarks failed for $crate_name after ${duration}s"
            return 1
        fi
    else
        if cargo bench --package "$crate_name" --quiet; then
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_success "Cargo benchmarks completed for $crate_name in ${duration}s"
        else
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_error "Cargo benchmarks failed for $crate_name after ${duration}s"
            return 1
        fi
    fi
}

# Function to run custom benchmarks
run_custom_benchmarks() {
    print_status "Running custom benchmarks..."
    
    # Check if the benchmark runner exists
    if [[ ! -f "benchmark_runner.rs" ]]; then
        print_warning "Custom benchmark runner not found, skipping custom benchmarks"
        return 0
    fi
    
    local start_time=$(date +%s)
    
    # Compile and run the custom benchmark runner
    if rustc benchmark_runner.rs -o ../target/benchmark_runner --extern serde --extern sysinfo; then
        if ../target/benchmark_runner; then
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_success "Custom benchmarks completed in ${duration}s"
        else
            local end_time=$(date +%s)
            local duration=$((end_time - start_time))
            print_error "Custom benchmarks failed after ${duration}s"
            return 1
        fi
    else
        print_error "Failed to compile custom benchmark runner"
        return 1
    fi
}

# Function to generate benchmark reports
generate_reports() {
    if [[ "$GENERATE_REPORTS" != "true" ]]; then
        return 0
    fi
    
    print_status "Generating benchmark reports..."
    
    # Create reports directory
    mkdir -p reports
    
    # Generate summary report
    local report_file="reports/benchmark_summary_$(date +%Y%m%d_%H%M%S).md"
    cat > "$report_file" << EOF
# Benchmark Report

Generated on: $(date)

## Configuration
- Output Format: $OUTPUT_FORMAT
- Memory Profiling: $MEMORY_PROFILING
- Warmup Iterations: $WARMUP_ITERATIONS
- Measurement Iterations: $MEASUREMENT_ITERATIONS
- Timeout: ${TIMEOUT_SECONDS}s

## Benchmarked Crates
$(printf '%s\n' "${BENCHMARK_CRATES[@]}")

## Results
EOF
    
    # Look for criterion results
    if [[ -d "target/criterion" ]]; then
        echo "### Criterion Results" >> "$report_file"
        echo "Criterion benchmark results are available in \`target/criterion/\`" >> "$report_file"
        echo "" >> "$report_file"
    fi
    
    # Look for custom benchmark results
    if [[ -f "benchmark_results.json" ]]; then
        echo "### Custom Benchmark Results" >> "$report_file"
        echo "Custom benchmark results are available in:" >> "$report_file"
        echo "- \`benchmark_results.json\`" >> "$report_file"
        echo "- \`benchmark_results.csv\`" >> "$report_file"
        echo "" >> "$report_file"
    fi
    
    print_success "Report generated: $report_file"
}

# Function to clean up
cleanup() {
    print_status "Cleaning up..."
    
    # Remove temporary files
    rm -f ../target/benchmark_runner
    
    print_success "Cleanup completed"
}

# Function to run all benchmarks
run_all_benchmarks() {
    local exit_code=0
    
    print_status "Starting benchmark execution..."
    print_status "Configuration:"
    print_status "  Crates: ${BENCHMARK_CRATES[*]}"
    print_status "  Output Format: $OUTPUT_FORMAT"
    print_status "  Memory Profiling: $MEMORY_PROFILING"
    print_status "  Warmup Iterations: $WARMUP_ITERATIONS"
    print_status "  Measurement Iterations: $MEASUREMENT_ITERATIONS"
    print_status "  Timeout: ${TIMEOUT_SECONDS}s"
    echo ""
    
    # Run custom benchmarks if requested
    if [[ "$CUSTOM_BENCHMARKS" == "true" ]]; then
        if ! run_custom_benchmarks; then
            exit_code=1
        fi
    else
        # Run cargo benchmarks for each crate
        for crate in "${BENCHMARK_CRATES[@]}"; do
            if ! run_cargo_benchmarks "$crate"; then
                exit_code=1
            fi
        done
        
        # Run custom benchmarks as well
        if ! run_custom_benchmarks; then
            exit_code=1
        fi
    fi
    
    # Generate reports
    generate_reports
    
    # Cleanup
    cleanup
    
    # Final summary
    echo ""
    if [[ $exit_code -eq 0 ]]; then
        print_success "All benchmarks completed successfully!"
    else
        print_error "Some benchmarks failed. Please check the output above."
    fi
    
    return $exit_code
}

# Main execution
main() {
    # Parse command line arguments
    parse_args "$@"
    
    # Check prerequisites
    check_prerequisites
    
    # Run benchmarks
    run_all_benchmarks
}

# Run main function with all arguments
main "$@" 