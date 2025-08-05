#!/bin/bash

# Ligature Release Preparation Script
# This script helps prepare a new release by bumping versions and creating tags

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
Usage: $0 [OPTIONS] <version>

Prepare a new release by bumping versions and creating tags.

OPTIONS:
    -h, --help              Show this help message
    -p, --patch             Bump patch version (0.1.0 -> 0.1.1)
    -m, --minor             Bump minor version (0.1.0 -> 0.2.0)
    -M, --major             Bump major version (0.1.0 -> 1.0.0)
    -d, --dry-run           Show what would be done without making changes
    -f, --force             Force version bump even if working directory is not clean
    --no-tag                Don't create a git tag (just bump version)

EXAMPLES:
    $0 --patch              # Bump patch version
    $0 --minor              # Bump minor version
    $0 --major              # Bump major version
    $0 0.2.0                # Set specific version
    $0 --dry-run --patch    # See what would happen

EOF
}

# Parse command line arguments
DRY_RUN=false
FORCE=false
CREATE_TAG=true
VERSION_TYPE=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_usage
            exit 0
            ;;
        -d|--dry-run)
            DRY_RUN=true
            shift
            ;;
        -f|--force)
            FORCE=true
            shift
            ;;
        --no-tag)
            CREATE_TAG=false
            shift
            ;;
        -p|--patch)
            VERSION_TYPE="patch"
            shift
            ;;
        -m|--minor)
            VERSION_TYPE="minor"
            shift
            ;;
        -M|--major)
            VERSION_TYPE="major"
            shift
            ;;
        -*)
            print_error "Unknown option: $1"
            show_usage
            exit 1
            ;;
        *)
            if [[ -z "$VERSION_TYPE" ]]; then
                VERSION_TYPE="specific"
                SPECIFIC_VERSION="$1"
            else
                print_error "Multiple version specifications provided"
                exit 1
            fi
            shift
            ;;
    esac
done

# Check if we're in the right directory
if [[ ! -f "Cargo.toml" ]]; then
    print_error "Cargo.toml not found. Please run this script from the project root."
    exit 1
fi

# Check if git is available
if ! command -v git &> /dev/null; then
    print_error "Git not found. Please install Git."
    exit 1
fi

# Check if working directory is clean (unless --force is used)
if [[ "$FORCE" != "true" ]]; then
    if ! git diff-index --quiet HEAD --; then
        print_error "Working directory is not clean. Commit or stash your changes first, or use --force."
        exit 1
    fi
fi

# Get current version from Cargo.toml
CURRENT_VERSION=$(grep '^version = ' Cargo.toml | cut -d'"' -f2)
print_status "Current version: $CURRENT_VERSION"

# Calculate new version
if [[ "$VERSION_TYPE" == "specific" ]]; then
    NEW_VERSION="$SPECIFIC_VERSION"
elif [[ "$VERSION_TYPE" == "patch" ]]; then
    # Bump patch version (0.1.0 -> 0.1.1)
    NEW_VERSION=$(echo "$CURRENT_VERSION" | awk -F. '{$NF = $NF + 1;} 1' | sed 's/ /./g')
elif [[ "$VERSION_TYPE" == "minor" ]]; then
    # Bump minor version (0.1.0 -> 0.2.0)
    NEW_VERSION=$(echo "$CURRENT_VERSION" | awk -F. '{$(NF-1) = $(NF-1) + 1; $NF = 0;} 1' | sed 's/ /./g')
elif [[ "$VERSION_TYPE" == "major" ]]; then
    # Bump major version (0.1.0 -> 1.0.0)
    NEW_VERSION=$(echo "$CURRENT_VERSION" | awk -F. '{$1 = $1 + 1; $(NF-1) = 0; $NF = 0;} 1' | sed 's/ /./g')
else
    print_error "No version type specified. Use --patch, --minor, --major, or provide a specific version."
    show_usage
    exit 1
fi

print_status "New version: $NEW_VERSION"

# Validate version format
if [[ ! $NEW_VERSION =~ ^[0-9]+\.[0-9]+\.[0-9]+(-[a-zA-Z0-9.-]+)?(\+[a-zA-Z0-9.-]+)?$ ]]; then
    print_error "Invalid version format: $NEW_VERSION"
    exit 1
fi

# Check if version already exists
if git tag | grep -q "v$NEW_VERSION"; then
    print_error "Version v$NEW_VERSION already exists as a tag"
    exit 1
fi

# Function to update version in Cargo.toml
update_version() {
    local version=$1
    local dry_run=$2
    
    if [[ "$dry_run" == "true" ]]; then
        print_status "Would update version in Cargo.toml to $version"
        return
    fi
    
    # Update workspace version
    sed -i.bak "s/^version = \".*\"/version = \"$version\"/" Cargo.toml
    rm Cargo.toml.bak
    
    print_success "Updated version in Cargo.toml to $version"
}

# Function to create git tag
create_tag() {
    local version=$1
    local dry_run=$2
    
    if [[ "$dry_run" == "true" ]]; then
        print_status "Would create git tag v$version"
        return
    fi
    
    git add Cargo.toml
    git commit -m "chore: bump version to $version"
    git tag "v$version"
    
    print_success "Created git tag v$version"
}

# Function to push changes
push_changes() {
    local version=$1
    local dry_run=$2
    
    if [[ "$dry_run" == "true" ]]; then
        print_status "Would push changes and tag v$version to remote"
        return
    fi
    
    git push origin main
    git push origin "v$version"
    
    print_success "Pushed changes and tag v$version to remote"
}

# Main execution
print_status "Preparing release for version $NEW_VERSION"

if [[ "$DRY_RUN" == "true" ]]; then
    print_warning "DRY RUN MODE - No changes will be made"
fi

# Update version
update_version "$NEW_VERSION" "$DRY_RUN"

# Create tag if requested
if [[ "$CREATE_TAG" == "true" ]]; then
    create_tag "$NEW_VERSION" "$DRY_RUN"
    
    # Push changes
    if [[ "$DRY_RUN" != "true" ]]; then
        read -p "Push changes and tag to remote? (y/N): " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            push_changes "$NEW_VERSION" "$DRY_RUN"
        else
            print_warning "Changes not pushed. You can push manually with:"
            echo "  git push origin main"
            echo "  git push origin v$NEW_VERSION"
        fi
    fi
fi

if [[ "$DRY_RUN" == "true" ]]; then
    print_status "Dry run completed. No changes were made."
else
    print_success "Release preparation completed!"
    print_status "Next steps:"
    echo "  1. Review the changes"
    echo "  2. Push the tag to trigger the release workflow:"
    echo "     git push origin v$NEW_VERSION"
    echo "  3. Monitor the release workflow at:"
    echo "     https://github.com/ligature-lang/ligature/actions"
fi 