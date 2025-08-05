# XDG Integration in Ligature

## Overview

Ligature implements the XDG Base Directory Specification to provide a standardized, user-friendly way to manage configuration files, data, cache, and state across all Ligature components. This ensures that Ligature follows Linux/Unix standards and respects user privacy and system integration preferences.

## What is XDG?

The XDG Base Directory Specification is a standard that defines where user-specific files should be placed on Linux and Unix-like systems. It provides a consistent way for applications to store:

- **Configuration files** (`~/.config/`)
- **Data files** (`~/.local/share/`)
- **Cache files** (`~/.cache/`)
- **State files** (`~/.local/state/`)

## Benefits for Users

### 1. **Standards Compliance**
- Follows established Linux/Unix standards
- Better integration with system package managers
- Consistent behavior across different distributions

### 2. **User Privacy and Control**
- Respects user's choice of directory locations
- Allows users to customize where Ligature stores files
- Supports environment variable overrides

### 3. **System Integration**
- Works seamlessly with backup tools
- Integrates with system-wide configuration management
- Supports user-specific and system-wide configurations

### 4. **Cross-Platform Support**
- Works on Linux, macOS, and Windows
- Provides appropriate fallbacks for non-XDG systems
- Consistent behavior across platforms

## Directory Structure

For each Ligature component, the following directory structure is created:

```
~/.config/ligature/component-name/     # Configuration files
~/.local/share/ligature/component-name/ # Data files  
~/.cache/ligature/component-name/       # Cache files
~/.local/state/ligature/component-name/ # State files
```

### Component-Specific Directories

Each Ligature component gets its own subdirectory:

- **`keywork`** - Package manager configuration and cache
- **`ligature-lsp`** - Language server configuration and workspace cache
- **`ligature-cli`** - CLI preferences and compilation cache
- **`krox`** - Client configuration and execution cache
- **`cacophony`** - Project configuration and build cache

## Configuration File Formats

Ligature supports multiple configuration file formats:

### JSON (Default)
```json
{
  "name": "example-app",
  "version": "1.0.0",
  "settings": {
    "enabled": true,
    "timeout": 30,
    "max_retries": 3
  }
}
```

### YAML
```yaml
name: example-app
version: 1.0.0
settings:
  enabled: true
  timeout: 30
  max_retries: 3
```

### TOML
```toml
name = "example-app"
version = "1.0.0"

[settings]
enabled = true
timeout = 30
max_retries = 3
```

## Environment Variables

You can customize XDG directory locations using standard environment variables:

### Linux/Unix
```bash
# Configuration directory
export XDG_CONFIG_HOME="$HOME/.my-config"

# Data directory  
export XDG_DATA_HOME="$HOME/.my-data"

# Cache directory
export XDG_CACHE_HOME="$HOME/.my-cache"

# State directory
export XDG_STATE_HOME="$HOME/.my-state"
```

### macOS
```bash
# macOS uses the same environment variables as Linux
export XDG_CONFIG_HOME="$HOME/Library/Application Support/MyApp"
```

### Windows
```bash
# Windows uses the same environment variables
set XDG_CONFIG_HOME=%APPDATA%\MyApp
```

## Component-Specific Configuration

### Keywork (Package Manager)

Keywork stores package registry configuration, authentication tokens, and cache:

```bash
# Configuration location
~/.config/ligature/keywork/config.json

# Cache location
~/.cache/ligature/keywork/packages/

# Data location
~/.local/share/ligature/keywork/installed/
```

**Example Configuration:**
```json
{
  "registry": {
    "default_url": "https://registry.ligature.dev",
    "timeout": 30,
    "max_retries": 3
  },
  "cache": {
    "enabled": true,
    "max_size": 104857600,
    "max_age": 86400
  }
}
```

### Ligature LSP (Language Server)

The LSP server stores workspace cache, symbol information, and performance settings:

```bash
# Configuration location
~/.config/ligature/ligature-lsp/config.toml

# Workspace cache
~/.cache/ligature/ligature-lsp/workspaces/

# Symbol cache
~/.cache/ligature/ligature-lsp/symbols/

# Module cache
~/.cache/ligature/ligature-lsp/modules/
```

**Example Configuration:**
```toml
enable_workspace_diagnostics = true
enable_cross_file_symbols = true
max_workspace_files = 1000

[logging]
level = "info"
log_to_file = true
log_to_console = false

[performance]
max_cached_documents = 100
cache_ttl_seconds = 3600
enable_incremental_parsing = true
```

### Ligature CLI

The CLI stores user preferences and compilation cache:

```bash
# Configuration location
~/.config/ligature/ligature-cli/config.json

# Compilation cache
~/.cache/ligature/ligature-cli/compiled/

# User preferences
~/.local/share/ligature/ligature-cli/preferences/
```

## Managing Configuration

### Viewing Current Configuration

You can view the current XDG paths for any component:

```bash
# For keywork
keywork config show

# For LSP (if available)
ligature-lsp --show-config

# For CLI
reed config show
```

### Modifying Configuration

Configuration can be modified through:

1. **Direct file editing** - Edit the JSON/YAML/TOML files directly
2. **Command-line tools** - Use component-specific commands
3. **Environment variables** - Override specific paths

### Backup and Migration

Since all configuration is stored in standard XDG directories, you can easily:

- **Backup configurations**: Copy the `~/.config/ligature/` directory
- **Migrate between systems**: Transfer the entire `~/.config/ligature/` directory
- **Version control**: Track configuration changes in git (exclude cache directories)

## Troubleshooting

### Common Issues

1. **Permission Denied**
   ```bash
   # Ensure directories have correct permissions
   chmod 755 ~/.config/ligature/
   chmod 755 ~/.cache/ligature/
   ```

2. **Configuration Not Loading**
   ```bash
   # Check if configuration file exists
   ls -la ~/.config/ligature/component-name/
   
   # Verify file permissions
   cat ~/.config/ligature/component-name/config.json
   ```

3. **Cache Issues**
   ```bash
   # Clear cache for a component
   rm -rf ~/.cache/ligature/component-name/
   
   # Recreate cache directory
   mkdir -p ~/.cache/ligature/component-name/
   ```

### Debugging

Enable debug logging to see XDG path resolution:

```bash
# Set debug environment variable
export LIGATURE_DEBUG=1

# Run component with debug output
keywork --debug
```

### Reset Configuration

To reset a component's configuration to defaults:

```bash
# Remove configuration file
rm ~/.config/ligature/component-name/config.json

# Remove cache
rm -rf ~/.cache/ligature/component-name/

# Component will recreate with defaults on next run
```

## Best Practices

### 1. **Configuration Management**
- Use version control for important configurations
- Document custom configurations
- Test configuration changes in a safe environment

### 2. **Cache Management**
- Regularly clean old cache files
- Monitor cache size usage
- Exclude cache directories from backups

### 3. **Security**
- Protect configuration files with appropriate permissions
- Don't store sensitive data in plain text
- Use environment variables for secrets

### 4. **Backup Strategy**
- Include `~/.config/ligature/` in your backup routine
- Exclude `~/.cache/ligature/` from backups
- Test backup restoration procedures

## Integration with System Tools

### Systemd User Services

You can create systemd user services that use XDG directories:

```ini
# ~/.config/systemd/user/ligature-lsp.service
[Unit]
Description=Ligature Language Server
After=network.target

[Service]
Type=simple
ExecStart=/usr/local/bin/ligature-lsp
Environment=XDG_CONFIG_HOME=%h/.config
Restart=always

[Install]
WantedBy=default.target
```

### Cron Jobs

Schedule cache cleanup with cron:

```bash
# Add to crontab
0 2 * * 0 find ~/.cache/ligature -type f -mtime +7 -delete
```

### Backup Scripts

Include Ligature configuration in backup scripts:

```bash
#!/bin/bash
# Backup Ligature configuration
rsync -av ~/.config/ligature/ /backup/ligature-config/
rsync -av ~/.local/share/ligature/ /backup/ligature-data/
```

## Future Enhancements

The XDG integration is designed to be extensible. Future enhancements may include:

- **Configuration validation** - Schema-based validation
- **Configuration templates** - Pre-built configuration templates
- **Migration tools** - Tools to migrate from old configurations
- **GUI configuration** - Graphical configuration editors
- **Cloud sync** - Synchronization with cloud storage

## Getting Help

If you encounter issues with XDG integration:

1. **Check the logs** - Look for error messages in component output
2. **Verify paths** - Ensure XDG directories exist and are writable
3. **Test with defaults** - Try resetting to default configuration
4. **Report issues** - File bug reports with detailed information

For more information about the XDG Base Directory Specification, see:
- [XDG Base Directory Specification](https://specifications.freedesktop.org/basedir-spec/basedir-spec-latest.html)
- [XDG User Directories](https://wiki.archlinux.org/title/XDG_user_directories) 