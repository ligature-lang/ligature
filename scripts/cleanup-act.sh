#!/bin/bash

# Script to clean up Docker resources used by act
# Usage: ./scripts/cleanup-act.sh

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

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

# Check if Docker is running
if ! docker info &> /dev/null; then
    print_error "Docker is not running. Please start Docker first."
    exit 1
fi

print_status "Cleaning up act Docker resources..."

# Stop and remove act containers
print_status "Stopping act containers..."
docker ps -a --filter "name=act-" --format "{{.ID}}" | xargs -r docker stop 2>/dev/null || true

print_status "Removing act containers..."
docker ps -a --filter "name=act-" --format "{{.ID}}" | xargs -r docker rm 2>/dev/null || true

# Remove act volumes
print_status "Removing act volumes..."
docker volume ls --filter "name=act-" --format "{{.Name}}" | xargs -r docker volume rm 2>/dev/null || true

# Remove act images (optional - uncomment if you want to remove images too)
# print_status "Removing act images..."
# docker images --filter "reference=catthehacker/ubuntu:act-latest" --format "{{.ID}}" | xargs -r docker rmi 2>/dev/null || true

# Clean up any dangling resources
print_status "Cleaning up dangling resources..."
docker system prune -f --volumes 2>/dev/null || true

print_success "Act cleanup completed!"
print_status "You can now run act workflows with fresh containers." 