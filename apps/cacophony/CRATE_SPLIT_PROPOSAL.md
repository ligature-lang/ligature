# Cacophony Crate Split Proposal

## Overview

The current `cacophony` crate has grown to handle multiple responsibilities. This document proposes splitting it into focused, reusable crates that can be developed and maintained independently.

## Proposed Crate Structure

### 1. `cacophony-core` - Core Types and Traits

**Purpose**: Define the fundamental types, traits, and interfaces used across all cacophony crates.

**Contents**:

- `error.rs` - Error types and handling
- `types.rs` - Core data structures (Collection, Environment, etc.)
- `traits.rs` - Plugin and Operation traits
- `config.rs` - Core configuration types

**Dependencies**:

- `serde`
- `thiserror`
- `async-trait`

### 2. `cacophony-config` - Configuration Management

**Purpose**: Handle configuration loading, validation, and XDG integration.

**Contents**:

- `manager.rs` - ConfigManager implementation
- `xdg.rs` - XDG base directory support
- `validation.rs` - Configuration validation logic
- `loader.rs` - Configuration file loading (TOML, JSON, YAML)

**Dependencies**:

- `cacophony-core`
- `serde`
- `serde_json`
- `serde_yaml`
- `toml`
- `ligature-xdg`

### 3. `cacophony-collections` - Collection Management

**Purpose**: Handle collection loading, validation, and management.

**Contents**:

- `collection.rs` - Collection implementation
- `manager.rs` - CollectionManager
- `loader.rs` - Ligature program loading
- `validation.rs` - Collection validation

**Dependencies**:

- `cacophony-core`
- `cacophony-config`
- `ligature-parser`
- `ligature-eval`

### 4. `cacophony-operations` - Operation System

**Purpose**: Define and manage operations that can be executed on collections.

**Contents**:

- `operation.rs` - Operation trait and base implementations
- `manager.rs` - OperationManager
- `builtin.rs` - Built-in operations (Deploy, Validate, Diff)
- `custom.rs` - Custom operation support

**Dependencies**:

- `cacophony-core`
- `cacophony-collections`

### 5. `cacophony-plugins` - Plugin System

**Purpose**: Plugin management and built-in plugin implementations.

**Contents**:

- `plugin.rs` - Plugin trait and PluginManager
- `terraform.rs` - Terraform plugin implementation
- `registry.rs` - Plugin registry and discovery
- `loader.rs` - Dynamic plugin loading

**Dependencies**:

- `cacophony-core`
- `cacophony-operations`
- `reqwest`
- `tokio-util`

### 6. `cacophony-cli` - Command Line Interface

**Purpose**: CLI argument parsing and command execution.

**Contents**:

- `main.rs` - Entry point
- `cli.rs` - Command definitions and execution
- `commands/` - Individual command implementations
  - `init.rs`
  - `deploy.rs`
  - `validate.rs`
  - `diff.rs`
  - `list.rs`
  - `run.rs`
  - `status.rs`

**Dependencies**:

- `cacophony-core`
- `cacophony-config`
- `cacophony-collections`
- `cacophony-operations`
- `cacophony-plugins`
- `clap`
- `tracing`

### 7. `cacophony-plugin-terraform` - Terraform Plugin (Optional)

**Purpose**: Separate crate for the Terraform plugin implementation.

**Contents**:

- `plugin.rs` - TerraformPlugin implementation
- `operations.rs` - Terraform-specific operations
- `config.rs` - Terraform configuration

**Dependencies**:

- `cacophony-plugins`
- `reqwest`
- `tokio-util`

## Benefits of This Split

### 1. **Modularity**

- Each crate has a single, well-defined responsibility
- Easier to understand and maintain
- Better separation of concerns

### 2. **Reusability**

- Other tools can use `cacophony-core` without CLI dependencies
- Plugin system can be used independently
- Configuration management can be reused

### 3. **Development Velocity**

- Teams can work on different crates in parallel
- Smaller, focused codebases are easier to navigate
- Faster compilation times for individual crates

### 4. **Testing**

- Each crate can have focused, unit-level tests
- Integration tests can test specific components
- Better test isolation

### 5. **Dependency Management**

- More granular control over dependencies
- Smaller dependency trees for each crate
- Easier to manage version compatibility

## Migration Strategy

### Phase 1: Extract Core Types

1. Create `cacophony-core` with fundamental types and traits
2. Update existing `cacophony` to use `cacophony-core`
3. Ensure all tests pass

### Phase 2: Extract Configuration

1. Create `cacophony-config` with configuration management
2. Move configuration-related code from main crate
3. Update dependencies

### Phase 3: Extract Collections

1. Create `cacophony-collections` with collection management
2. Move collection-related code
3. Update dependencies

### Phase 4: Extract Operations

1. Create `cacophony-operations` with operation system
2. Move operation-related code
3. Update dependencies

### Phase 5: Extract Plugins

1. Create `cacophony-plugins` with plugin system
2. Move plugin-related code
3. Update dependencies

### Phase 6: Refactor CLI

1. Create `cacophony-cli` with CLI interface
2. Move CLI-related code
3. Update main binary to use new crates

### Phase 7: Optional Terraform Plugin

1. Create `cacophony-plugin-terraform` as separate crate
2. Move Terraform-specific code
3. Update plugin registry

## Directory Structure After Split

```
apps/
├── cacophony-core/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── error.rs
│       ├── types.rs
│       └── traits.rs
├── cacophony-config/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── manager.rs
│       ├── xdg.rs
│       └── validation.rs
├── cacophony-collections/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── collection.rs
│       ├── manager.rs
│       └── loader.rs
├── cacophony-operations/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── operation.rs
│       ├── manager.rs
│       └── builtin.rs
├── cacophony-plugins/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── plugin.rs
│       ├── registry.rs
│       └── loader.rs
├── cacophony-cli/
│   ├── Cargo.toml
│   └── src/
│       ├── main.rs
│       ├── cli.rs
│       └── commands/
│           ├── mod.rs
│           ├── init.rs
│           ├── deploy.rs
│           └── ...
└── cacophony-plugin-terraform/ (optional)
    ├── Cargo.toml
    └── src/
        ├── lib.rs
        ├── plugin.rs
        └── operations.rs
```

## Considerations

### 1. **Breaking Changes**

- This split will introduce breaking changes
- Need to coordinate with users of the library
- Consider maintaining compatibility layer

### 2. **Version Management**

- Each crate will have its own version
- Need to coordinate releases
- Consider workspace-level versioning

### 3. **Documentation**

- Each crate needs its own documentation
- Update README files for each crate
- Consider unified documentation site

### 4. **CI/CD**

- Update CI/CD pipelines for multiple crates
- Ensure all crates are tested together
- Coordinate releases

## Next Steps

1. **Review and Approve**: Get feedback on this proposal
2. **Create Implementation Plan**: Detailed migration steps
3. **Set Up Workspace**: Create new crate structure
4. **Begin Migration**: Start with Phase 1 (Core Types)
5. **Update Documentation**: Update all documentation
6. **Coordinate Release**: Plan breaking change release
