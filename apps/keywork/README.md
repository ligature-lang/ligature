# Keywork - Ligature Package Manager

Keywork is a comprehensive package management system for Ligature registers. It provides tools for creating, building, publishing, installing, and managing Ligature packages with full dependency resolution and registry integration.

## Features

### Core Package Management

- **Register Creation**: Initialize new Ligature registers with proper structure
- **Building**: Compile and package registers with dependency resolution
- **Validation**: Comprehensive validation of register manifests and modules
- **Publishing**: Upload registers to remote registries
- **Installation**: Install registers locally or globally

### Dependency Management

- **Dependency Resolution**: Automatic resolution of package dependencies
- **Conflict Detection**: Detect and report version conflicts
- **Circular Dependency Detection**: Prevent circular dependency issues
- **Transitive Dependencies**: Handle dependencies of dependencies
- **Version Management**: Support for version ranges and latest versions

### Registry Operations

- **Package Search**: Search for packages in remote registries
- **Package Discovery**: Browse available packages by category
- **Version Listing**: List all available versions for a package
- **Package Statistics**: View download counts and metadata
- **Caching**: Intelligent caching of downloaded packages

### Advanced Features

- **Checksum Verification**: Verify package integrity
- **Archive Management**: Create and extract tar.gz packages
- **Build Artifacts**: Generate detailed build information
- **Module Validation**: Syntax and type checking of Ligature modules
- **Cache Management**: Clean and manage package cache

## Installation

```bash
# From the ligature workspace
cargo install --path apps/keywork
```

## Usage

### Creating a New Register

```bash
# Create a new register in the current directory
keywork init my-register

# Create in a specific directory
keywork init my-register --directory /path/to/project
```

This creates a register with the following structure:

```
my-register/
├── register.toml
├── src/
│   └── example.lig
└── tests/
    └── example_test.lig
```

### Building a Register

```bash
# Build in the current directory
keywork build

# Build with custom output directory
keywork build --output ./build
```

The build process:

1. Validates the register manifest
2. Checks module syntax and types
3. Resolves dependencies
4. Copies files to output directory
5. Generates build artifacts and checksums

### Installing Registers

```bash
# Install the latest version
keywork install stdlib

# Install a specific version
keywork install stdlib --version 1.0.0

# Install globally
keywork install stdlib --global
```

### Publishing to Registry

```bash
# Publish to default registry
keywork publish

# Publish to custom registry
keywork publish --registry https://my-registry.com
```

**Note**: Requires `KEYWORK_AUTH_TOKEN` environment variable to be set.

### Managing Dependencies

```bash
# Install dependencies for a project
keywork install-deps

# Update all dependencies
keywork update --all

# Update specific dependency
keywork update --dependency stdlib
```

### Searching and Discovery

```bash
# Search for packages
keywork search "config"

# Discover packages by category
keywork discover "web"

# List available versions
keywork versions stdlib

# Show package statistics
keywork stats stdlib
```

### Validation and Information

```bash
# Validate a register
keywork validate

# Show detailed validation
keywork validate --verbose

# Show register information
keywork info my-register

# List installed registers
keywork list --verbose
```

### Cache Management

```bash
# Clean package cache
keywork clean-cache
```

## Register Manifest Format

The `register.toml` file defines your package:

```toml
[register]
name = "my-register"
version = "1.0.0"
description = "A useful Ligature register"
authors = ["Your Name <your.email@example.com>"]
license = "Apache-2.0"
repository = "https://github.com/user/my-register"

[dependencies]
stdlib = "1.0.0"
config = "0.1.0"

[exports]
core = "src/core.lig"
utils = "src/utils.lig"

[metadata]
tags = ["web", "utilities"]
```

### Manifest Fields

- **name**: Package name (required)
- **version**: Semantic version (required)
- **description**: Package description (required)
- **authors**: List of authors (required)
- **license**: License identifier (required)
- **repository**: Source repository URL (optional)

### Dependencies

Dependencies can be specified with version constraints:

- `"1.0.0"` - Exact version
- `"latest"` - Latest available version
- `">=1.0.0"` - Version range (future enhancement)

### Exports

Exports define which modules are publicly available:

- Key: Module name for import
- Value: Path to the module file

## Registry Integration

Keywork supports multiple registry backends:

### Default Registry

- URL: `https://registry.ligature.dev`
- Public packages
- No authentication required for downloads

### Custom Registries

- Specify with `--registry` flag
- Support for private registries
- Authentication via `KEYWORK_AUTH_TOKEN`

## Dependency Resolution

The dependency resolver:

1. **Parses Dependencies**: Reads dependency specifications from manifests
2. **Resolves Versions**: Fetches available versions from registries
3. **Builds Graph**: Creates dependency graph with relationships
4. **Detects Conflicts**: Identifies version conflicts and circular dependencies
5. **Resolves Order**: Determines installation order
6. **Downloads**: Downloads and caches packages

### Conflict Resolution

When conflicts are detected:

- Reports conflicting versions
- Suggests resolution strategies
- Prevents installation until resolved

## Caching

Keywork caches downloaded packages to improve performance:

- **Location**: `~/.cache/keywork/` (configurable)
- **TTL**: 1 hour for package metadata
- **Verification**: Checksum verification for integrity
- **Cleanup**: Manual cache cleaning via `clean-cache`

## Error Handling

Comprehensive error reporting with:

- Detailed error messages
- Suggested solutions
- Context information
- Stack traces for debugging

## Examples

### Complete Workflow

```bash
# 1. Create a new register
keywork init my-web-app

# 2. Add dependencies to register.toml
# [dependencies]
# stdlib = "1.0.0"
# web = "0.2.0"

# 3. Install dependencies
keywork install-deps

# 4. Build the register
keywork build

# 5. Validate before publishing
keywork validate --verbose

# 6. Publish to registry
export KEYWORK_AUTH_TOKEN="your-token"
keywork publish
```

### Using Installed Registers

```bash
# Install a register
keywork install stdlib

# Use in your Ligature code
# import { String, List } from stdlib
```

## Configuration

### Environment Variables

- `KEYWORK_AUTH_TOKEN`: Authentication token for publishing
- `KEYWORK_REGISTRY_URL`: Default registry URL
- `KEYWORK_CACHE_DIR`: Custom cache directory

### Global vs Local Installation

- **Local**: Installs to `./registers/` (default)
- **Global**: Installs to `/usr/local/lib/ligature/registers/`

## Troubleshooting

### Common Issues

1. **Validation Errors**

   - Check manifest syntax
   - Ensure exported modules exist
   - Verify dependency specifications

2. **Dependency Conflicts**

   - Update conflicting packages
   - Use compatible versions
   - Check for circular dependencies

3. **Network Issues**

   - Check internet connection
   - Verify registry URL
   - Clear cache if needed

4. **Permission Errors**
   - Use `--global` for system-wide installation
   - Check directory permissions
   - Run with appropriate privileges

### Debug Mode

Enable verbose output for debugging:

```bash
keywork validate --verbose
keywork list --verbose
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Submit a pull request

## License

This project is licensed under the Apache License, Version 2.0 - see the [LICENSE](../../LICENSE) file for details.
