//! Configuration for code actions.

/// Configuration for code actions.
#[derive(Debug, Clone)]
pub struct CodeActionsConfig {
    /// Whether to enable advanced refactoring actions.
    pub enable_advanced_refactoring: bool,
    /// Whether to enable code generation actions.
    pub enable_code_generation: bool,
    /// Whether to enable type-aware fixes.
    pub enable_type_aware_fixes: bool,
    /// Whether to enable performance suggestions.
    pub enable_performance_suggestions: bool,
    /// Whether to enable style suggestions.
    pub enable_style_suggestions: bool,
}

impl Default for CodeActionsConfig {
    fn default() -> Self {
        Self {
            enable_advanced_refactoring: true,
            enable_code_generation: true,
            enable_type_aware_fixes: true,
            enable_performance_suggestions: true,
            enable_style_suggestions: true,
        }
    }
}
