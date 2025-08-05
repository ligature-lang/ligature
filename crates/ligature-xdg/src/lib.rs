//! XDG base directory support for Ligature components.
//!
//! This crate provides a unified interface for accessing XDG base directories
//! across all Ligature components, with fallback support for non-XDG systems.

pub mod config;
pub mod error;
pub mod paths;
pub mod validation;
pub mod hot_reload;

pub use config::*;
pub use error::*;
pub use paths::*;
pub use validation::*;
pub use hot_reload::*;
