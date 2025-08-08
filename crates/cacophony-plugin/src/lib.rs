//! Cacophony Plugins
//!
//! This crate provides the plugin system for the Cacophony CLI tool.
//! It includes the plugin trait, plugin manager, and built-in plugins.

pub mod manager;
pub mod terraform;

// Re-export core types for convenience
pub use cacophony_core::{
    CacophonyError, Operation, OperationResult, Plugin, Result, ValidationResult,
};
pub use manager::PluginManager;
pub use terraform::TerraformPlugin;
