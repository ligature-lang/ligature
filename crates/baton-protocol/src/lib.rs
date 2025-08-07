//! Protocol definitions for Baton formal verification.
//!
//! This crate provides the request/response protocol for communication
//! with the Lean theorem prover.

pub mod types;
pub mod impls;

pub use types::*;

/// Re-export commonly used types
pub mod prelude {
    pub use super::*;
} 