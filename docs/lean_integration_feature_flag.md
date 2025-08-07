# Lean Integration Feature Flag

## Overview

The Lean integration has been moved behind a Cargo feature flag (`lean-integration`) to provide better build performance and dependency management. This allows users to choose whether they want to include the Lean integration dependencies and functionality.

## Feature Flag Benefits

### 1. **Faster Builds**

- Users who don't need Lean integration can build faster
- Reduced dependency tree when Lean integration is not required
- Faster CI/CD pipelines for basic testing

### 2. **Optional Dependencies**

- The `baton-*` crates are only included when the feature is enabled
- Reduces the overall dependency footprint
- Allows for more flexible deployment scenarios

### 3. **Better Development Experience**

- Developers can work on core functionality without Lean setup
- Clear separation between core language features and formal verification
- Easier onboarding for new contributors

## Usage

### Enabling the Feature

```bash
# Build with Lean integration
cargo build --features lean-integration

# Run tests with Lean integration
cargo test --features lean-integration

# Run examples with Lean integration
cargo run --example working_lean_test --features lean-integration
```

### Disabling the Feature (Default)

```bash
# Build without Lean integration (default)
cargo build

# Run tests without Lean integration (default)
cargo test

# Run examples without Lean integration
cargo run --example working_lean_test
# This will show a message that the feature is not enabled
```

## Implementation Details

### Workspace Configuration

The feature is defined in the workspace `Cargo.toml`:

```toml
[workspace.features]
default = []
lean-integration = [
  "baton-client",
  "baton-protocol",
  "baton-verification",
  "baton-specification",
  "baton-core",
  "baton-error"
]
```

### Conditional Compilation

The differential testing framework uses conditional compilation:

```rust
#[cfg(feature = "lean-integration")]
use baton_verification::prelude::*;

#[cfg(feature = "lean-integration")]
pub async fn run_lean_test_case(source: &str) -> Result<String, String> {
    // Real implementation
}

#[cfg(not(feature = "lean-integration"))]
pub async fn run_lean_test_case(source: &str) -> Result<String, String> {
    Err("Lean integration is not enabled. Enable the 'lean-integration' feature to use this functionality.".to_string())
}
```

### Examples

All Lean integration examples are conditional:

```rust
#[cfg(feature = "lean-integration")]
use baton_client::LeanClient;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    #[cfg(not(feature = "lean-integration"))]
    {
        println!("=== Lean Integration Not Enabled ===");
        println!("This example requires the 'lean-integration' feature to be enabled.");
        println!("Run with: cargo run --example working_lean_test --features lean-integration");
        return Ok(());
    }

    #[cfg(feature = "lean-integration")]
    {
        // Real implementation
    }
}
```

## Affected Components

### 1. **Differential Testing Framework**

- `tests/differential/mod.rs` - Conditional imports and functions
- All Lean-related functions are feature-gated
- Stub implementations when feature is disabled

### 2. **Examples**

- `examples/working_lean_test.rs` - Conditional compilation
- `examples/debug_lean_communication.rs` - Conditional compilation
- `examples/simple_lean_test.rs` - Conditional compilation
- `examples/lean_integration_example.rs` - Conditional compilation

### 3. **Dependencies**

- `examples/Cargo.toml` - Optional baton dependencies
- All `baton-*` crates are optional when feature is disabled

## Migration Guide

### For Users

**No changes required** - the default behavior remains the same (no Lean integration).

### For Developers

1. **To use Lean integration:**

   ```bash
   cargo test --features lean-integration
   ```

2. **To run Lean examples:**

   ```bash
   cargo run --example working_lean_test --features lean-integration
   ```

3. **To build with Lean integration:**
   ```bash
   cargo build --features lean-integration
   ```

### For CI/CD

Update your CI configuration to include the feature when needed:

```yaml
# Example GitHub Actions
- name: Run tests without Lean integration
  run: cargo test

- name: Run tests with Lean integration
  run: cargo test --features lean-integration
```

## Future Enhancements

### 1. **Additional Features**

- `lean-integration-full` - Include all Lean dependencies and tools
- `lean-integration-minimal` - Only core verification functionality

### 2. **Configuration Options**

- Environment variable to enable/disable features
- Configuration file support for feature selection

### 3. **Documentation**

- Auto-generated feature documentation
- Feature compatibility matrix

## Troubleshooting

### Common Issues

1. **"Lean integration is not enabled" error:**

   - Solution: Add `--features lean-integration` to your cargo command

2. **Missing baton dependencies:**

   - Solution: Ensure the `lean-integration` feature is enabled

3. **Build errors with Lean integration:**
   - Check that Lean is properly installed
   - Verify the Lean specification files are present

### Debugging

```bash
# Check available features
cargo check --features lean-integration

# Build with verbose output
cargo build --features lean-integration -v

# Run specific example with debugging
RUST_LOG=debug cargo run --example working_lean_test --features lean-integration
```

## Conclusion

The feature flag system provides a clean separation between core language functionality and formal verification capabilities. This improves build performance, reduces dependencies, and provides a better development experience while maintaining full functionality when needed.
