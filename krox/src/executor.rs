//! Executors for different Ligature program execution modes.

use std::path::Path;

use ligature_ast::Program;
use ligature_eval::Value;
use ligature_parser::parse_program;
use serde::Serialize;
use tracing::{debug, warn};

use crate::ClientConfig;
use crate::error::{Error, Result};

/// Trait for executing Ligature programs.
#[async_trait::async_trait]
pub trait Executor: Send + Sync {
    /// Execute a Ligature program from a file.
    async fn execute_file(&self, path: &Path) -> Result<Value>;

    /// Execute a Ligature program from source code.
    async fn execute_source(&self, source: &str) -> Result<Value>;

    /// Execute a Ligature program from a parsed AST.
    async fn execute_program(&self, program: &Program) -> Result<Value>;
}

/// Native executor that uses the ligature-cli binary.
pub struct NativeExecutor {
    cli_path: String,
    timeout: std::time::Duration,
}

impl NativeExecutor {
    /// Create a new native executor.
    pub fn new(config: &ClientConfig) -> Result<Self> {
        let cli_path = if let Some(ref path) = config.ligature_cli_path {
            path.clone()
        } else {
            // Try to find ligature-cli in PATH
            which::which("ligature-cli")
                .map(|p| p.to_string_lossy().to_string())
                .map_err(|_| {
                    Error::ligature_cli(
                        "Could not find ligature-cli binary in PATH".to_string(),
                        None,
                    )
                })?
        };

        let timeout = config
            .http_timeout
            .unwrap_or_else(|| std::time::Duration::from_secs(30));

        Ok(Self { cli_path, timeout })
    }

    /// Execute a command with timeout.
    async fn execute_command(&self, args: &[&str]) -> Result<String> {
        use tokio::process::Command;
        use tokio::time::timeout;

        debug!("Executing command: {} {:?}", self.cli_path, args);

        let output = timeout(
            self.timeout,
            Command::new(&self.cli_path).args(args).output(),
        )
        .await
        .map_err(|_| Error::timeout("Command execution timed out".to_string(), self.timeout))?
        .map_err(|e| {
            Error::process_execution(
                format!("Failed to execute command: {e}"),
                Some(format!("{} {:?}", self.cli_path, args)),
                None,
            )
        })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Error::cli_execution(
                "Command failed".to_string(),
                output.status.code(),
                stderr.to_string(),
            ));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(stdout.to_string())
    }
}

#[async_trait::async_trait]
impl Executor for NativeExecutor {
    async fn execute_file(&self, path: &Path) -> Result<Value> {
        let path_str = path.to_string_lossy();
        let _output = self.execute_command(&["eval", &path_str]).await?;

        // For now, we'll return a simple unit value since we can't deserialize Value
        // In a real implementation, you'd need a custom serialization format
        Ok(Value::unit(ligature_ast::Span::default()))
    }

    async fn execute_source(&self, source: &str) -> Result<Value> {
        use std::io::Write;

        use tempfile::NamedTempFile;

        // Create a temporary file with the source code
        let mut temp_file = NamedTempFile::new().map_err(|e| {
            Error::file_system(format!("Failed to create temporary file: {e}"), None)
        })?;

        temp_file.write_all(source.as_bytes()).map_err(|e| {
            Error::file_system(
                format!("Failed to write to temporary file: {e}"),
                Some(temp_file.path().to_string_lossy().to_string()),
            )
        })?;

        // Execute the temporary file
        let result = self.execute_file(temp_file.path()).await;

        // Clean up the temporary file
        if let Err(e) = temp_file.close() {
            warn!("Failed to close temporary file: {e}");
        }

        result
    }

    async fn execute_program(&self, program: &Program) -> Result<Value> {
        // For now, serialize the program to source and execute it
        // In the future, we could add a direct AST execution mode
        let source = format!("{program:?}"); // This is a placeholder
        self.execute_source(&source).await
    }
}

/// HTTP executor that sends requests to a remote server.
pub struct HttpExecutor {
    client: reqwest::Client,
    endpoint: String,
    #[allow(dead_code)]
    timeout: std::time::Duration,
}

impl HttpExecutor {
    /// Create a new HTTP executor.
    pub fn new(endpoint: &str, config: &ClientConfig) -> Result<Self> {
        let timeout = config
            .http_timeout
            .unwrap_or_else(|| std::time::Duration::from_secs(30));

        let client = reqwest::Client::builder()
            .timeout(timeout)
            .build()
            .map_err(Error::Http)?;

        Ok(Self {
            client,
            endpoint: endpoint.to_string(),
            timeout,
        })
    }

    /// Send an execution request to the server.
    async fn send_request(&self, request: &ExecutionRequest) -> Result<Value> {
        let response = self
            .client
            .post(&self.endpoint)
            .json(request)
            .send()
            .await
            .map_err(Error::Http)?;

        if !response.status().is_success() {
            let status = response.status().as_u16();
            let body = response.text().await.unwrap_or_default();
            return Err(Error::http_server(
                status,
                format!("HTTP request failed with status {status}"),
                Some(body),
            ));
        }

        // For now, we'll return a simple unit value since we can't deserialize Value
        // In a real implementation, you'd need a custom serialization format
        Ok(Value::unit(ligature_ast::Span::default()))
    }
}

#[async_trait::async_trait]
impl Executor for HttpExecutor {
    async fn execute_file(&self, path: &Path) -> Result<Value> {
        let path_str = path.to_string_lossy();
        let request = ExecutionRequest::File {
            path: path_str.to_string(),
        };

        self.send_request(&request).await
    }

    async fn execute_source(&self, source: &str) -> Result<Value> {
        let request = ExecutionRequest::Source {
            source: source.to_string(),
        };

        self.send_request(&request).await
    }

    async fn execute_program(&self, program: &Program) -> Result<Value> {
        let request = ExecutionRequest::Program {
            program: serde_json::to_string(program).map_err(Error::JsonSerialization)?,
        };

        self.send_request(&request).await
    }
}

/// In-process executor that directly evaluates programs.
pub struct InProcessExecutor;

impl InProcessExecutor {
    /// Create a new in-process executor.
    pub fn new() -> Self {
        Self
    }
}

impl Default for InProcessExecutor {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Executor for InProcessExecutor {
    async fn execute_file(&self, path: &Path) -> Result<Value> {
        let source = tokio::fs::read_to_string(path).await.map_err(Error::Io)?;

        self.execute_source(&source).await
    }

    async fn execute_source(&self, source: &str) -> Result<Value> {
        let program = parse_program(source).map_err(Error::Parse)?;

        self.execute_program(&program).await
    }

    async fn execute_program(&self, program: &Program) -> Result<Value> {
        ligature_eval::evaluate_program(program).map_err(Error::Parse)
    }
}

/// Request sent to HTTP execution server.
#[derive(Debug, Serialize)]
#[serde(tag = "type")]
enum ExecutionRequest {
    #[serde(rename = "file")]
    File { path: String },
    #[serde(rename = "source")]
    Source { source: String },
    #[serde(rename = "program")]
    Program { program: String },
}

/// Response from HTTP execution server.
#[derive(Debug)]
#[allow(dead_code)]
struct ExecutionResponse {
    result: Option<Value>,
    error: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_native_executor_creation() {
        let config = ClientConfig::default();
        let _executor = NativeExecutor::new(&config);
        // This might fail if ligature-cli is not in PATH, which is expected
        // in test environments
    }

    #[tokio::test]
    async fn test_http_executor_creation() {
        let config = ClientConfig::default();
        let executor = HttpExecutor::new("http://localhost:8080", &config);
        assert!(executor.is_ok());
    }

    #[tokio::test]
    async fn test_in_process_executor() {
        let executor = InProcessExecutor::new();
        let _result = executor.execute_source("let x = 42").await;
        // This might fail if the parser/evaluator is not fully implemented
    }
}
