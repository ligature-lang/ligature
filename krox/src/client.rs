//! Main client for executing Ligature programs.

use crate::{
    ClientConfig, ExecutionMode, ExecutionResult,
    cache::Cache,
    error::{Error, Result},
    executor::{Executor, HttpExecutor, NativeExecutor},
};
use ligature_ast::Program;
use std::path::Path;
use tracing::{debug, info, warn};

/// The main Krox client for executing Ligature programs.
pub struct Client {
    config: ClientConfig,
    executor: Box<dyn Executor>,
    cache: Option<Cache>,
}

impl Client {
    /// Create a new client with the specified execution mode.
    pub async fn new(mode: ExecutionMode) -> Result<Self> {
        let config = ClientConfig {
            execution_mode: mode,
            ..Default::default()
        };
        Self::with_config(config).await
    }

    /// Create a new client with custom configuration.
    pub async fn with_config(config: ClientConfig) -> Result<Self> {
        let executor: Box<dyn Executor> = match config.execution_mode {
            ExecutionMode::Native => {
                let native_executor = NativeExecutor::new(&config)?;
                Box::new(native_executor)
            }
            ExecutionMode::Http => {
                let http_endpoint = config.http_endpoint.as_ref().ok_or_else(|| {
                    Error::configuration(
                        "HTTP endpoint is required for HTTP execution mode".to_string(),
                        Some("http_endpoint".to_string()),
                    )
                })?;
                let http_executor = HttpExecutor::new(http_endpoint, &config)?;
                Box::new(http_executor)
            }
            ExecutionMode::InProcess => {
                return Err(Error::unsupported(
                    "In-process execution is not yet implemented".to_string(),
                    "InProcess".to_string(),
                ));
            }
        };

        let cache = if config.enable_cache {
            let cache_dir = config.cache_dir.clone().unwrap_or_else(|| {
                let mut dir = std::env::temp_dir();
                dir.push("krox-cache");
                dir.to_string_lossy().to_string()
            });
            Some(Cache::new(&cache_dir).await?)
        } else {
            None
        };

        Ok(Self {
            config,
            executor,
            cache,
        })
    }

    /// Execute a Ligature program from a file.
    pub async fn execute_file<P: AsRef<Path>>(&mut self, path: P) -> Result<ExecutionResult> {
        let path = path.as_ref();
        let start_time = std::time::Instant::now();

        info!("Executing Ligature file: {:?}", path);

        // Check cache first
        if let Some(ref mut cache) = self.cache {
            if let Some(cached_result) = cache.get(path).await? {
                debug!("Returning cached result for {:?}", path);
                return Ok(ExecutionResult {
                    value: cached_result,
                    metadata: crate::ExecutionMetadata {
                        duration: start_time.elapsed(),
                        cached: true,
                        mode: self.config.execution_mode,
                        warnings: vec![],
                    },
                });
            }
        }

        // Execute the program
        let value = self.executor.execute_file(path.as_ref()).await?;

        // Cache the result
        if let Some(ref mut cache) = self.cache {
            if let Err(e) = cache.set(path, &value).await {
                warn!("Failed to cache result: {}", e);
            }
        }

        let duration = start_time.elapsed();
        info!("Execution completed in {:?}", duration);

        Ok(ExecutionResult {
            value,
            metadata: crate::ExecutionMetadata {
                duration,
                cached: false,
                mode: self.config.execution_mode,
                warnings: vec![],
            },
        })
    }

    /// Execute a Ligature program from source code.
    pub async fn execute_source(&mut self, source: &str) -> Result<ExecutionResult> {
        let start_time = std::time::Instant::now();

        info!("Executing Ligature source code ({} bytes)", source.len());

        // Check cache first
        if let Some(ref mut cache) = self.cache {
            if let Some(cached_result) = cache.get_by_content(source).await? {
                debug!("Returning cached result for source content");
                return Ok(ExecutionResult {
                    value: cached_result,
                    metadata: crate::ExecutionMetadata {
                        duration: start_time.elapsed(),
                        cached: true,
                        mode: self.config.execution_mode,
                        warnings: vec![],
                    },
                });
            }
        }

        // Execute the program
        let value = self.executor.execute_source(source).await?;

        // Cache the result
        if let Some(ref mut cache) = self.cache {
            if let Err(e) = cache.set_by_content(source, &value).await {
                warn!("Failed to cache result: {}", e);
            }
        }

        let duration = start_time.elapsed();
        info!("Execution completed in {:?}", duration);

        Ok(ExecutionResult {
            value,
            metadata: crate::ExecutionMetadata {
                duration,
                cached: false,
                mode: self.config.execution_mode,
                warnings: vec![],
            },
        })
    }

    /// Execute a Ligature program from a parsed AST.
    pub async fn execute_program(&mut self, program: &Program) -> Result<ExecutionResult> {
        let start_time = std::time::Instant::now();

        info!("Executing Ligature program AST");

        // Execute the program
        let value = self.executor.execute_program(program).await?;

        let duration = start_time.elapsed();
        info!("Execution completed in {:?}", duration);

        Ok(ExecutionResult {
            value,
            metadata: crate::ExecutionMetadata {
                duration,
                cached: false,
                mode: self.config.execution_mode,
                warnings: vec![],
            },
        })
    }

    /// Get the current configuration.
    pub fn config(&self) -> &ClientConfig {
        &self.config
    }

    /// Clear the cache.
    pub async fn clear_cache(&mut self) -> Result<()> {
        if let Some(ref mut cache) = self.cache {
            cache.clear().await?;
        }
        Ok(())
    }

    /// Get cache statistics.
    pub async fn cache_stats(&mut self) -> Result<Option<crate::cache::CacheStats>> {
        if let Some(ref mut cache) = self.cache {
            Ok(Some(cache.stats().await?))
        } else {
            Ok(None)
        }
    }

    /// Get the cache instance.
    pub fn cache(&self) -> Option<&Cache> {
        self.cache.as_ref()
    }

    /// Get a mutable reference to the cache instance.
    pub fn cache_mut(&mut self) -> Option<&mut Cache> {
        self.cache.as_mut()
    }
}

// Remove the From trait implementation since it's not compatible with async

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ClientBuilder;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_client_creation() {
        let client = Client::new(ExecutionMode::Native).await;
        // This might fail if ligature-cli is not in PATH, which is expected in test environments
        if client.is_err() {
            println!("Note: ligature-cli not found in PATH, test skipped");
        }
    }

    #[tokio::test]
    async fn test_client_builder() {
        let client = ClientBuilder::new()
            .execution_mode(ExecutionMode::Native)
            .enable_cache(true)
            .verbose(true)
            .build()
            .await;
        // This might fail if ligature-cli is not in PATH, which is expected in test environments
        if client.is_err() {
            println!("Note: ligature-cli not found in PATH, test skipped");
        }
    }

    #[tokio::test]
    async fn test_cache_configuration() {
        let temp_dir = tempdir().unwrap();
        let client = ClientBuilder::new()
            .cache_dir(temp_dir.path().to_string_lossy().to_string())
            .enable_cache(true)
            .build()
            .await;

        if let Ok(client) = client {
            assert!(client.cache().is_some());
        } else {
            println!("Note: ligature-cli not found in PATH, test skipped");
        }
    }
}
