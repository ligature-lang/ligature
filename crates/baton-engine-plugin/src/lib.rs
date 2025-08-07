//! Plugin interface for Baton verification engines.
//!
//! This crate provides a plugin system for different verification engines
//! that can be used with the Baton formal verification system.

pub mod engine;
pub mod generic;
pub mod manager;
pub mod specification;
pub mod traits;

pub use engine::{EngineCapabilities, EngineInfo, EngineStatus};
pub use generic::{
    BuildConfig, ClientStats, ComparisonType, ConsistencyCheckType, CoverageInfo,
    DetailedComparison, Difference, DifferenceSeverity, DifferentialTestType, EngineClient,
    EngineClientFactory, EngineConfig, EngineRequest, EngineRequestType, EngineResponse,
    EngineResponseType, ErrorType, MemoryUsage, PerformanceComparison, RequestPriority,
    RetryConfig, SpecificationCheckType, TestType, TheoremInfo, VerificationContext,
};
pub use manager::EnginePluginManager;
pub use specification::prelude::*;
pub use traits::{EnginePlugin, VerificationEngine};

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        BuildConfig, ClientStats, ComparisonType, ConsistencyCheckType, CoverageInfo,
        DetailedComparison, Difference, DifferenceSeverity, DifferentialTestType,
        EngineCapabilities, EngineClient, EngineClientFactory, EngineConfig, EngineInfo,
        EnginePlugin, EnginePluginManager, EngineRequest, EngineRequestType, EngineResponse,
        EngineResponseType, EngineStatus, ErrorType, MemoryUsage, PerformanceComparison,
        RequestPriority, RetryConfig, SpecificationCheckType, TestType, TheoremInfo,
        VerificationContext, VerificationEngine,
    };
    pub use baton_error::prelude::*;
    pub use baton_protocol::prelude::*;
}
