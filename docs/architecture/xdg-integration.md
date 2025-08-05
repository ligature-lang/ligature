# XDG Integration Documentation

## Overview

Ligature implements comprehensive XDG Base Directory Specification support to provide standardized, user-friendly configuration management across all components. This document provides an overview of the XDG integration and links to detailed documentation.

## What is XDG Integration?

The XDG Base Directory Specification defines standard locations for user-specific files on Linux and Unix-like systems. Ligature's XDG integration ensures:

- **Standards compliance** - Follows established Linux/Unix standards
- **User privacy** - Respects user's choice of directory locations
- **System integration** - Works seamlessly with backup tools and package managers
- **Cross-platform support** - Works on Linux, macOS, and Windows with appropriate fallbacks

## Documentation Structure

### For Users

- **[XDG Integration Guide](user-guide/xdg-integration.md)** - Complete user guide covering:
  - What XDG is and why it matters
  - Directory structure and organization
  - Configuration file formats (JSON, YAML, TOML)
  - Environment variable customization
  - Component-specific configuration details
  - Troubleshooting and best practices
  - Integration with system tools

### For Developers

- **[XDG Integration Quick Reference](user-guide/xdg-integration-quick-reference.md)** - Developer-focused guide covering:
  - How to use the `ligature-xdg` crate
  - Basic usage patterns and examples
  - Advanced configuration management
  - Testing strategies
  - Migration from legacy systems
  - Best practices for component development

### Technical Implementation

- **[XDG Implementation Phase 1](xdg-implementation-phase1.md)** - Technical details of the implementation
- **[ligature-xdg Crate README](../crates/ligature-xdg/README.md)** - API documentation for the core crate

## Key Features

### Directory Structure

Each Ligature component gets its own organized directory structure:

```
~/.config/ligature/component-name/     # Configuration files
~/.local/share/ligature/component-name/ # Data files
~/.cache/ligature/component-name/       # Cache files
~/.local/state/ligature/component-name/ # State files
```

### Supported Components

- **keywork** - Package manager configuration and cache
- **ligature-lsp** - Language server configuration and workspace cache
- **ligature-cli** - CLI preferences and compilation cache
- **krox** - Client configuration and execution cache
- **cacophony** - Project configuration and build cache

### Configuration Formats

- **JSON** - Default format, human-readable
- **YAML** - Alternative format, more readable for complex configurations
- **TOML** - Alternative format, good for hierarchical configurations

### Environment Variables

Standard XDG environment variables are supported:

- `XDG_CONFIG_HOME` - Configuration directory
- `XDG_DATA_HOME` - Data directory
- `XDG_CACHE_HOME` - Cache directory
- `XDG_STATE_HOME` - State directory

## Benefits

### For End Users

1. **Standards Compliance** - Follows established Linux/Unix standards
2. **User Privacy** - Respects user's choice of directory locations
3. **System Integration** - Works seamlessly with backup tools
4. **Cross-Platform Support** - Consistent behavior across platforms

### For System Administrators

1. **Centralized Management** - All Ligature configuration in standard locations
2. **Backup Integration** - Easy to include in backup routines
3. **Package Manager Integration** - Better integration with system package managers
4. **User Isolation** - Clear separation of user-specific and system-wide configurations

### For Developers

1. **Consistent API** - Unified configuration management across all components
2. **Error Handling** - Comprehensive error types with detailed context
3. **Async Support** - Full async/await support for file operations
4. **Testing Support** - Easy to test with temporary directories

## Quick Start

### For Users

1. Read the **[XDG Integration Guide](user-guide/xdg-integration.md)**
2. Understand the directory structure for your components
3. Customize configuration using environment variables if needed
4. Set up backup and maintenance routines

### For Developers

1. Read the **[XDG Integration Quick Reference](user-guide/xdg-integration-quick-reference.md)**
2. Add the `ligature-xdg` dependency to your component
3. Define your configuration structure with serde
4. Implement the XDG configuration manager pattern
5. Add tests for configuration persistence

## Implementation Status

### Phase 1: Core Infrastructure ✅

- [x] `ligature-xdg` crate implementation
- [x] XDG Base Directory compliance
- [x] Cross-platform support
- [x] Multiple file format support
- [x] Comprehensive error handling
- [x] Async file operations

### Phase 2: Component Integration 🔄

- [x] Keywork package manager integration
- [x] Ligature LSP integration
- [x] Ligature CLI integration
- [ ] Krox client integration
- [ ] Cacophony project integration

### Phase 3: Advanced Features 📋

- [ ] Configuration validation
- [ ] Configuration templates
- [ ] Migration tools
- [ ] GUI configuration editors
- [ ] Cloud synchronization

## Getting Help

### Documentation

- Start with the **[XDG Integration Guide](user-guide/xdg-integration.md)** for user-oriented information
- Use the **[Quick Reference](user-guide/xdg-integration-quick-reference.md)** for development tasks
- Check the **[Technical Implementation](xdg-implementation-phase1.md)** for implementation details

### Troubleshooting

- Check the troubleshooting section in the user guide
- Verify XDG directory permissions
- Test with default configurations
- Enable debug logging for detailed error information

### Reporting Issues

- File bug reports with detailed information about your environment
- Include XDG directory paths and permissions
- Provide error messages and logs
- Test with minimal configurations

## Related Documentation

- **[User Guide](../user-guide/README.md)** - Complete user documentation
- **[Architecture Documentation](../architecture/)** - Technical architecture details
- **[Contributing Guide](../../CONTRIBUTING.md)** - How to contribute to Ligature
- **[XDG Base Directory Specification](https://specifications.freedesktop.org/basedir-spec/basedir-spec-latest.html)** - Official specification

## Examples

### Basic Configuration

```json
{
  "name": "my-component",
  "version": "1.0.0",
  "settings": {
    "enabled": true,
    "timeout": 30,
    "max_retries": 3
  }
}
```

### Environment Customization

```bash
# Custom XDG directories
export XDG_CONFIG_HOME="$HOME/.my-config"
export XDG_CACHE_HOME="$HOME/.my-cache"
export XDG_DATA_HOME="$HOME/.my-data"
export XDG_STATE_HOME="$HOME/.my-state"
```

### Component Usage

```rust
use ligature_xdg::{config_for_component, XdgPaths};

let paths = XdgPaths::new("my-component")?;
let config_manager = config_for_component("my-component")?;

// Load configuration
let config = config_manager.load::<MyConfig>().await?;

// Save configuration
config_manager.save(&config).await?;
```

This XDG integration provides a solid foundation for standardized configuration management across all Ligature components, ensuring a consistent and user-friendly experience.
