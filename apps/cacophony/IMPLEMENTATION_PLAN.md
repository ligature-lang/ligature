# Cacophony Crate Split Implementation Plan

## Phase 1: Extract Core Types (`cacophony-core`)

### Step 1: Create the Core Crate Structure

```bash
# Create new crate directory
mkdir -p apps/cacophony-core/src

# Create Cargo.toml for cacophony-core
```

### Step 2: Define Core Crate Dependencies

**`apps/cacophony-core/Cargo.toml`**:

```toml
[package]
name = "cacophony-core"
version = "0.1.0"
edition = "2021"
authors = ["Ligature Team"]
description = "Core types and traits for the Cacophony orchestration system"
license = "Apache-2.0"
repository = "https://github.com/fugue-ai/ligature"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
thiserror = "1.0"
async-trait = "0.1"
serde_json = "1.0"
```

### Step 3: Extract Core Types

**`apps/cacophony-core/src/lib.rs`**:

```rust
pub mod error;
pub mod types;
pub mod traits;
pub mod config;

pub use error::{CacophonyError, Result};
pub use types::{Collection, Environment, LigatureProgram};
pub use traits::{Plugin, Operation};
pub use config::{CacophonyConfig, ProjectConfig, EnvironmentConfig, CollectionConfig};
```

**`apps/cacophony-core/src/error.rs`**:

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CacophonyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("TOML error: {0}")]
    Toml(#[from] toml::de::Error),

    #[error("Not found: {0}")]
    NotFound(String),

    #[error("Validation error: {0}")]
    Validation(String),

    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Plugin error: {0}")]
    Plugin(String),

    #[error("Operation error: {0}")]
    Operation(String),
}

pub type Result<T> = std::result::Result<T, CacophonyError>;
```

**`apps/cacophony-core/src/types.rs`**:

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LigatureProgram {
    pub name: String,
    pub content: String,
    pub path: PathBuf,
}

impl LigatureProgram {
    pub fn new(name: String, content: String, path: PathBuf) -> Self {
        Self { name, content, path }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Collection {
    pub name: String,
    pub config: CollectionConfig,
    pub programs: Vec<LigatureProgram>,
    pub dependencies: Vec<String>,
    pub variables: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Environment {
    pub name: String,
    pub description: Option<String>,
    pub variables: HashMap<String, String>,
    pub plugins: Vec<String>,
    pub overrides: Option<HashMap<String, serde_json::Value>>,
}

impl Environment {
    pub fn get_variable(&self, key: &str) -> Option<&String> {
        self.variables.get(key)
    }
}
```

**`apps/cacophony-core/src/traits.rs`**:

```rust
use async_trait::async_trait;
use serde_json::Value;
use crate::types::{Collection, Environment};
use crate::error::Result;

#[async_trait]
pub trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn description(&self) -> &str;
    fn operations(&self) -> Vec<Box<dyn Operation>>;
    fn configure(&mut self, config: &Value) -> Result<()>;
}

#[async_trait]
pub trait Operation: Send + Sync {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    async fn execute(&self, collection: &Collection, environment: &Environment) -> Result<OperationResult>;
    fn validate(&self, collection: &Collection, environment: &Environment) -> Result<ValidationResult>;
}

#[derive(Debug)]
pub struct OperationResult {
    pub success: bool,
    pub message: String,
    pub details: HashMap<String, Value>,
    pub duration: std::time::Duration,
}

#[derive(Debug)]
pub struct ValidationResult {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}
```

**`apps/cacophony-core/src/config.rs`**:

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacophonyConfig {
    pub project: ProjectConfig,
    pub environments: HashMap<String, EnvironmentConfig>,
    pub collections: HashMap<String, CollectionConfig>,
    pub plugins: Vec<PluginConfig>,
    pub operations: HashMap<String, OperationConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectConfig {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub authors: Vec<String>,
    pub repository: Option<String>,
    pub license: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentConfig {
    pub name: String,
    pub description: Option<String>,
    pub variables: HashMap<String, String>,
    pub plugins: Vec<String>,
    pub overrides: Option<HashMap<String, serde_json::Value>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectionConfig {
    pub name: String,
    pub description: Option<String>,
    pub dependencies: Vec<String>,
    pub operations: Vec<String>,
    pub environments: Vec<String>,
    pub config: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginConfig {
    pub name: String,
    pub version: Option<String>,
    pub config: Option<serde_json::Value>,
    pub enabled: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OperationConfig {
    pub name: String,
    pub description: Option<String>,
    pub script: Option<String>,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
    pub timeout: Option<u64>,
    pub retries: Option<u32>,
}
```

### Step 4: Update Main Cacophony Crate

**Update `apps/cacophony/Cargo.toml`**:

```toml
[dependencies]
# ... existing dependencies ...
cacophony-core = { path = "../cacophony-core" }
```

**Update `apps/cacophony/src/main.rs`**:

```rust
use clap::Parser;
use tracing::{error, info, Level};
use tracing_subscriber::FmtSubscriber;

mod cli;
mod collection;
mod config;
mod environment;
mod ligature_loader;
mod operation;
mod plugin;
mod xdg_config;

use cli::Commands;
use cacophony_core::error::{CacophonyError, Result};

// ... rest of the file remains the same ...
```

**Update `apps/cacophony/src/error.rs`**:

```rust
pub use cacophony_core::error::{CacophonyError, Result};
```

### Step 5: Update All Import Statements

Throughout the existing `cacophony` crate, replace:

- `use crate::error::{CacophonyError, Result};` with `use cacophony_core::error::{CacophonyError, Result};`
- `use crate::collection::Collection;` with `use cacophony_core::types::Collection;`
- `use crate::environment::Environment;` with `use cacophony_core::types::Environment;`
- etc.

### Step 6: Create Tests for Core Crate

**`apps/cacophony-core/src/lib.rs`** (add to existing):

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ligature_program_creation() {
        let program = LigatureProgram::new(
            "test".to_string(),
            "content".to_string(),
            std::path::PathBuf::from("test.lig"),
        );
        assert_eq!(program.name, "test");
        assert_eq!(program.content, "content");
    }

    #[test]
    fn test_environment_variable_access() {
        let mut env = Environment {
            name: "test".to_string(),
            description: None,
            variables: HashMap::new(),
            plugins: Vec::new(),
            overrides: None,
        };
        env.variables.insert("TEST_VAR".to_string(), "test_value".to_string());

        assert_eq!(env.get_variable("TEST_VAR"), Some(&"test_value".to_string()));
        assert_eq!(env.get_variable("NONEXISTENT"), None);
    }
}
```

### Step 7: Update Workspace Configuration

**Update root `Cargo.toml`** (if it exists):

```toml
[workspace]
members = [
    "crates/*",
    "apps/cacophony",
    "apps/cacophony-core",
]
```

### Step 8: Verify Build and Tests

```bash
# Test the core crate
cd apps/cacophony-core
cargo test

# Test the main crate still works
cd ../cacophony
cargo test

# Test the workspace
cd ../..
cargo test --workspace
```

## Success Criteria for Phase 1

1. ✅ `cacophony-core` crate compiles successfully
2. ✅ All tests pass in `cacophony-core`
3. ✅ Main `cacophony` crate compiles with `cacophony-core` dependency
4. ✅ All existing tests in `cacophony` still pass
5. ✅ No functionality is lost during the extraction
6. ✅ Clean separation of concerns between core types and implementation

## Next Steps After Phase 1

Once Phase 1 is complete and verified:

1. **Phase 2**: Extract `cacophony-config` for configuration management
2. **Phase 3**: Extract `cacophony-collections` for collection management
3. **Phase 4**: Extract `cacophony-operations` for operation system
4. **Phase 5**: Extract `cacophony-plugins` for plugin system
5. **Phase 6**: Refactor `cacophony-cli` for CLI interface

## Rollback Plan

If issues arise during Phase 1:

1. Keep the original `cacophony` crate unchanged
2. Revert `cacophony-core` changes
3. Update `cacophony/Cargo.toml` to remove `cacophony-core` dependency
4. Restore original import statements in `cacophony` source files
5. Verify all tests pass with original structure

This approach ensures we can safely experiment with the crate split while maintaining a working system.
