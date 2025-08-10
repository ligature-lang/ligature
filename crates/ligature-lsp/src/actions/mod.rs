//! Enhanced code actions provider for the Ligature LSP server.

pub mod code_generation;
pub mod config;
pub mod core;
pub mod evaluation;
pub mod performance_style;
pub mod quick_fixes;
pub mod refactoring;
pub mod source_actions;
pub mod type_aware;

// Re-exports for the actions module

pub use core::CodeActionsProvider;

// Re-export commonly used types
pub use code_generation::*;
pub use config::CodeActionsConfig;
pub use evaluation::*;
pub use performance_style::*;
pub use quick_fixes::*;
pub use refactoring::*;
pub use source_actions::*;
pub use type_aware::*;
