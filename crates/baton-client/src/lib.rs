//! Generic client for Baton formal verification.
//!
//! This crate provides the client for communicating with verification engines.

pub mod client;
pub mod config;
pub mod connection;
pub mod stats;
pub mod utils;

pub use baton_error::{BatonError, BatonResult};
pub use client::EngineClient;
// Legacy type aliases for backward compatibility
pub use client::LeanClient;
pub use config::{EngineClientConfig, LeanClientConfig};
pub use connection::EngineConnection;
pub use stats::ClientStats;

/// Re-export commonly used types
pub mod prelude {
    pub use baton_engine_plugin::prelude::*;
    pub use baton_error::{BatonError, BatonResult};

    pub use super::{
        ClientStats,
        EngineClient,
        EngineClientConfig,
        EngineConnection,
        // Legacy exports
        LeanClient,
        LeanClientConfig,
    };
}
