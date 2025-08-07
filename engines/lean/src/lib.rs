//! Lean verification engine plugin for Baton.
//!
//! This crate provides a Lean theorem prover plugin that implements
//! the Baton verification engine interface.

pub mod engine;
pub mod plugin;

pub use engine::LeanEngine;
pub use plugin::LeanEnginePlugin;

/// Re-export commonly used types
pub mod prelude {
    pub use super::{LeanEngine, LeanEnginePlugin};
    pub use baton_engine_plugin::prelude::*;
}
