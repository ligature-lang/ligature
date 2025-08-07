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
pub use config::EngineClientConfig;
pub use connection::EngineConnection;
pub use stats::ClientStats;

// Legacy type aliases for backward compatibility
pub use client::LeanClient;
pub use config::LeanClientConfig;

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        ClientStats,
        EngineClient,
        EngineClientConfig,
        EngineConnection,
        // Legacy exports
        LeanClient,
        LeanClientConfig,
    };
    pub use baton_engine_plugin::prelude::*;
    pub use baton_error::{BatonError, BatonResult};
}
