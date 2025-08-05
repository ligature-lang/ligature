//! Package management library for Ligature registers.

pub mod commands;
pub mod dependency;
pub mod register;
pub mod registry;
pub mod xdg_config;

pub use dependency::{Dependency, DependencyGraph, DependencyNode, ResolutionResult};
pub use register::Register;
pub use xdg_config::{KeyworkConfig, KeyworkXdgConfig};
