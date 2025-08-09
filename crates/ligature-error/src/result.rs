//! Standardized result types for Ligature crates.

use anyhow::Result as AnyhowResult;
use ligature_ast::LigatureResult;

/// Standard result type for Ligature crates.
pub type StandardResult<T> = Result<T, crate::StandardError>;

/// Result type that can handle both Ligature errors and standard errors.
pub type UnifiedResult<T> = Result<T, crate::StandardError>;

/// Extension trait for adding context to results.
pub trait ResultExt<T, E> {
    /// Add context to an error result.
    fn with_context<C>(self, context: C) -> Result<T, crate::StandardError>
    where
        C: Into<String>;

    /// Add context to an error result using a closure.
    fn with_context_fn<C, F>(self, context_fn: F) -> Result<T, crate::StandardError>
    where
        C: Into<String>,
        F: FnOnce() -> C;
}

impl<T, E> ResultExt<T, E> for Result<T, E>
where
    E: Into<crate::StandardError>,
{
    fn with_context<C>(self, context: C) -> Result<T, crate::StandardError>
    where
        C: Into<String>,
    {
        self.map_err(|e| e.into().with_context(context))
    }

    fn with_context_fn<C, F>(self, context_fn: F) -> Result<T, crate::StandardError>
    where
        C: Into<String>,
        F: FnOnce() -> C,
    {
        self.map_err(|e| e.into().with_context(context_fn()))
    }
}

/// Extension trait for LigatureResult.
pub trait LigatureResultExt<T> {
    /// Convert to a standard result.
    fn into_standard(self) -> StandardResult<T>;

    /// Add context to a Ligature error.
    fn with_context<C>(self, context: C) -> StandardResult<T>
    where
        C: Into<String>;
}

impl<T> LigatureResultExt<T> for LigatureResult<T> {
    fn into_standard(self) -> StandardResult<T> {
        self.map_err(|e| crate::StandardError::Internal(e.to_string()))
    }

    fn with_context<C>(self, context: C) -> StandardResult<T>
    where
        C: Into<String>,
    {
        self.map_err(|e| crate::StandardError::Internal(format!("{}: {}", context.into(), e)))
    }
}

/// Extension trait for AnyhowResult.
pub trait AnyhowResultExt<T> {
    /// Convert to a standard result.
    fn into_standard(self) -> StandardResult<T>;

    /// Add context to an anyhow error.
    fn with_context<C>(self, context: C) -> StandardResult<T>
    where
        C: Into<String>;
}

impl<T> AnyhowResultExt<T> for AnyhowResult<T> {
    fn into_standard(self) -> StandardResult<T> {
        self.map_err(|e| crate::StandardError::Internal(e.to_string()))
    }

    fn with_context<C>(self, context: C) -> StandardResult<T>
    where
        C: Into<String>,
    {
        self.map_err(|e| crate::StandardError::Internal(format!("{}: {}", context.into(), e)))
    }
}

/// Utility functions for working with results.
pub mod utils {
    use super::*;

    /// Combine multiple results, returning the first error or all values.
    pub fn combine_results<T>(results: Vec<StandardResult<T>>) -> StandardResult<Vec<T>> {
        let mut values = Vec::new();
        let mut errors = Vec::new();

        for result in results {
            match result {
                Ok(value) => values.push(value),
                Err(error) => errors.push(error),
            }
        }

        if errors.is_empty() {
            Ok(values)
        } else {
            Err(crate::StandardError::internal_error(format!(
                "Multiple errors occurred: {}",
                errors
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )))
        }
    }

    /// Try multiple operations and return the first successful result.
    pub fn try_operations<T, F>(operations: Vec<F>) -> StandardResult<T>
    where
        F: FnOnce() -> StandardResult<T>,
    {
        let mut last_error = None;

        for operation in operations {
            match operation() {
                Ok(value) => return Ok(value),
                Err(error) => last_error = Some(error),
            }
        }

        Err(last_error
            .unwrap_or_else(|| crate::StandardError::internal_error("No operations provided")))
    }

    /// Retry an operation with exponential backoff.
    pub async fn retry_with_backoff<T, F, Fut>(
        mut operation: F,
        max_retries: usize,
        initial_delay: std::time::Duration,
    ) -> StandardResult<T>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = StandardResult<T>>,
    {
        let mut delay = initial_delay;
        let mut last_error = None;

        for attempt in 0..=max_retries {
            match operation().await {
                Ok(value) => return Ok(value),
                Err(error) => {
                    last_error = Some(error);
                    if attempt < max_retries {
                        tokio::time::sleep(delay).await;
                        delay *= 2;
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| {
            crate::StandardError::internal_error("Operation failed after all retries")
        }))
    }
}
