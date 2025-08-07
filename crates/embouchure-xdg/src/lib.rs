//! XDG base directory support for Embouchure ecosystem components.
//!
//! This crate provides a unified interface for accessing XDG base directories
//! across all Embouchure ecosystem components, with fallback support for non-XDG systems.

pub mod config;
pub mod error;
pub mod hot_reload;
pub mod paths;
pub mod validation;

pub use config::*;
pub use error::*;
pub use hot_reload::*;
pub use paths::*;
pub use validation::*;
