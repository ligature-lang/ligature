#!/bin/bash

# Script to test GitHub Actions workflows locally using act
# Usage: ./scripts/test-workflows.sh [workflow_name] [job_name]

set -e

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

# Check if act is installed
if ! command -v act &> /dev/null; then
    print_error "act is not installed. Please install it first:"
    echo "  brew install act"
    exit 1
fi

# Check if Docker is running
if ! docker info &> /dev/null; then
    print_error "Docker is not running. Please start Docker first."
    exit 1
fi

# Available workflows
WORKFLOWS=(
    "ci"
    "coverage"
    "release"
    "status-badge"
    "shared-crates"
    "test-crates-config"
    "cargo-llvm-cov-setup"
)

# Function to list available workflows
list_workflows() {
    print_status "Available workflows:"
    for workflow in "${WORKFLOWS[@]}"; do
        echo "  - $workflow"
    done
    echo ""
    print_status "Usage examples:"
    echo "  ./scripts/test-workflows.sh ci"
    echo "  ./scripts/test-workflows.sh ci code-quality"
    echo "  ./scripts/test-workflows.sh coverage"
}

# Function to run a specific workflow
run_workflow() {
    local workflow=$1
    local job=$2
    
    print_status "Testing workflow: $workflow"
    
    if [[ -n "$job" ]]; then
        print_status "Running specific job: $job"
        act workflow_dispatch -W ".github/workflows/${workflow}.yml" -j "$job"
    else
        print_status "Running all jobs in workflow"
        act workflow_dispatch -W ".github/workflows/${workflow}.yml"
    fi
}

# Main script logic
if [[ $# -eq 0 ]]; then
    print_status "No workflow specified. Showing available options:"
    list_workflows
    exit 0
fi

WORKFLOW_NAME=$1
JOB_NAME=$2

# Validate workflow name
if [[ ! " ${WORKFLOWS[@]} " =~ " ${WORKFLOW_NAME} " ]]; then
    print_error "Unknown workflow: $WORKFLOW_NAME"
    list_workflows
    exit 1
fi

# Check if workflow file exists
if [[ ! -f ".github/workflows/${WORKFLOW_NAME}.yml" ]]; then
    print_error "Workflow file not found: .github/workflows/${WORKFLOW_NAME}.yml"
    exit 1
fi

print_status "Starting local workflow test..."
print_warning "Note: Some actions may not work exactly the same locally as they do on GitHub"

# Run the workflow
run_workflow "$WORKFLOW_NAME" "$JOB_NAME"

print_success "Workflow test completed!" 