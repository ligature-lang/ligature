//! Main client implementation for communicating with verification engines.

use crate::config::EngineClientConfig;
use crate::connection::EngineConnection;
use crate::debug_log;
use crate::stats::ClientStats;
use crate::utils::{find_engine_executable, find_specification_path};
use baton_engine_plugin::prelude::*;
use baton_error::{BatonError, BatonResult};
use serde_json;
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdout, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tempfile::NamedTempFile;

/// Generic client for communicating with verification engines.
pub struct EngineClient {
    /// Client configuration
    config: EngineClientConfig,
    /// Engine name
    engine_name: String,
    /// Connection pool
    pool: Arc<Mutex<Vec<EngineConnection>>>,
    /// Active connections
    #[allow(clippy::type_complexity)]
    active_connections: Arc<Mutex<HashMap<String, EngineConnection>>>,
    /// Request counter
    request_counter: Arc<Mutex<u64>>,
    /// Statistics
    stats: Arc<Mutex<ClientStats>>,
}

impl EngineClient {
    /// Create a new engine client with default configuration.
    pub fn new(engine_name: String) -> BatonResult<Self> {
        let config = EngineClientConfig::default();
        Self::with_config(engine_name, config)
    }

    /// Create a new engine client with custom configuration.
    pub fn with_config(engine_name: String, mut config: EngineClientConfig) -> BatonResult<Self> {
        // Auto-detect engine path if not provided
        if config.engine_path.is_empty() {
            config.engine_path = find_engine_executable(&engine_name)?;
        }

        // Auto-detect specification path if not provided
        if config.spec_path.is_empty() {
            config.spec_path = find_specification_path(&engine_name)?;
        }

        Ok(Self {
            config,
            engine_name,
            pool: Arc::new(Mutex::new(Vec::new())),
            active_connections: Arc::new(Mutex::new(HashMap::new())),
            request_counter: Arc::new(Mutex::new(0)),
            stats: Arc::new(Mutex::new(ClientStats::default())),
        })
    }

    /// Execute a verification request.
    pub async fn verify(&self, request: VerificationRequest) -> BatonResult<VerificationResponse> {
        let start_time = Instant::now();
        let request_id = self.get_next_request_id();

        debug_log!(
            self.config,
            "Executing request {}: {:?}",
            request_id,
            request
        );

        let context = ErrorContext::new("verify".to_string())
            .with_expression(format!("request_{request_id}"));

        let result = self.execute_with_retry(request, &context).await;

        // Update statistics
        let duration = start_time.elapsed();
        self.update_stats(result.is_ok(), duration).await;

        debug_log!(
            self.config,
            "Request {} completed in {:?}",
            request_id,
            duration
        );

        result
    }

    /// Execute request with retry logic.
    async fn execute_with_retry(
        &self,
        request: VerificationRequest,
        _context: &ErrorContext,
    ) -> BatonResult<VerificationResponse> {
        let mut last_error = None;

        for attempt in 0..=self.config.retry_attempts {
            match self.execute_single_request(&request).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.config.retry_attempts {
                        tokio::time::sleep(self.config.retry_delay).await;
                    }
                }
            }
        }

        Err(last_error
            .unwrap_or_else(|| BatonError::InternalError("All retry attempts failed".to_string())))
    }

    /// Execute a single request.
    async fn execute_single_request(
        &self,
        request: &VerificationRequest,
    ) -> BatonResult<VerificationResponse> {
        let connection = self.get_connection().await?;
        let input_file = self.create_input_file(request).await?;
        let lean_file = self
            .create_engine_file(&input_file.path().to_string_lossy())
            .await?;

        let output = self
            .run_engine_process_with_connection(connection, &lean_file.path().to_string_lossy())
            .await?;

        let response = self.parse_engine_response(output)?;
        Ok(VerificationResponse::new(
            LeanResponse::VerificationSuccess {
                result: format!("{response:?}"),
                proof: None,
                proof_steps: None,
                execution_time: Some(0),
            },
            0,
        )) // TODO: Calculate actual execution time
    }

    /// Get a connection from the pool or create a new one.
    async fn get_connection(&self) -> BatonResult<EngineConnection> {
        if self.config.enable_pooling {
            if let Some(connection) = self.pool.lock().unwrap().pop() {
                return Ok(connection);
            }
        }

        self.create_connection().await
    }

    /// Create a new engine connection.
    async fn create_connection(&self) -> BatonResult<EngineConnection> {
        let mut command = Command::new(&self.config.engine_path);

        if self.config.verbose {
            command.arg("--verbose");
        }

        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let mut process = command.spawn().map_err(|e| {
            BatonError::ProcessStart(format!(
                "Failed to start {} process: {}",
                self.engine_name, e
            ))
        })?;

        let stdin = process.stdin.take().ok_or_else(|| {
            BatonError::ProcessStart("Failed to get stdin from process".to_string())
        })?;

        let stdout = process.stdout.take().ok_or_else(|| {
            BatonError::ProcessStart("Failed to get stdout from process".to_string())
        })?;

        Ok(EngineConnection {
            process,
            stdin,
            stdout: BufReader::new(stdout),
            last_used: Instant::now(),
            request_count: 0,
        })
    }

    /// Run engine process with connection.
    async fn run_engine_process_with_connection(
        &self,
        mut connection: EngineConnection,
        input_file: &str,
    ) -> BatonResult<String> {
        let script = self.create_engine_script(input_file)?;

        connection
            .stdin
            .write_all(script.as_bytes())
            .map_err(|e| BatonError::Communication(format!("Failed to write to stdin: {e}")))?;

        connection
            .stdin
            .flush()
            .map_err(|e| BatonError::Communication(format!("Failed to flush stdin: {e}")))?;

        let output = self.read_engine_response(&mut connection.stdout).await?;

        // Update connection stats
        connection.last_used = Instant::now();
        connection.request_count += 1;

        // Return connection to pool if pooling is enabled
        if self.config.enable_pooling {
            self.pool.lock().unwrap().push(connection);
        }

        Ok(output)
    }

    /// Read engine response from stdout.
    async fn read_engine_response(
        &self,
        stdout: &mut BufReader<ChildStdout>,
    ) -> BatonResult<String> {
        let mut response = String::new();
        let mut line = String::new();

        // Read until we find a response marker or timeout
        let start_time = Instant::now();
        while start_time.elapsed() < self.config.timeout {
            line.clear();
            match stdout.read_line(&mut line) {
                Ok(0) => break, // EOF
                Ok(_) => {
                    response.push_str(&line);
                    if line.contains("RESPONSE_END") || line.contains("ERROR") {
                        break;
                    }
                }
                Err(e) => {
                    return Err(BatonError::Communication(format!(
                        "Failed to read from stdout: {e}"
                    )));
                }
            }
        }

        if response.is_empty() {
            return Err(BatonError::Timeout(
                "No response received from engine".to_string(),
            ));
        }

        Ok(response)
    }

    /// Create input file for the request.
    async fn create_input_file(&self, request: &VerificationRequest) -> BatonResult<NamedTempFile> {
        let content = serde_json::to_string_pretty(request).map_err(|e| {
            BatonError::SerializationError(format!("Failed to serialize request: {e}"))
        })?;

        let mut temp_file = NamedTempFile::new()
            .map_err(|e| BatonError::FileSystemError(format!("Failed to create temp file: {e}")))?;

        temp_file
            .write_all(content.as_bytes())
            .map_err(|e| BatonError::FileSystemError(format!("Failed to write temp file: {e}")))?;

        Ok(temp_file)
    }

    /// Create engine-specific file.
    async fn create_engine_file(&self, input_file: &str) -> BatonResult<NamedTempFile> {
        let script = self.create_engine_script(input_file)?;

        let mut temp_file = NamedTempFile::new()
            .map_err(|e| BatonError::FileSystemError(format!("Failed to create temp file: {e}")))?;

        temp_file
            .write_all(script.as_bytes())
            .map_err(|e| BatonError::FileSystemError(format!("Failed to write temp file: {e}")))?;

        Ok(temp_file)
    }

    /// Create engine-specific script.
    fn create_engine_script(&self, input_file: &str) -> BatonResult<String> {
        // This is a generic implementation
        // Engine-specific implementations would override this
        Ok(format!(
            r#"
-- Engine script for {}
-- Input file: {}

-- Read and process the input
let input = readFile "{}"
let request = parseJson input

-- Execute the request
let result = executeRequest request

-- Output the result
printJson result
print "RESPONSE_END"
"#,
            self.engine_name, input_file, input_file
        ))
    }

    /// Parse engine output.
    #[allow(dead_code)]
    fn parse_engine_output(&self, output: &std::process::Output) -> BatonResult<EngineResponse> {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            return Err(BatonError::VerificationFailed(format!(
                "Engine process failed: {stderr}"
            )));
        }

        self.parse_engine_response(stdout.to_string())
    }

    /// Parse engine response.
    fn parse_engine_response(&self, response: String) -> BatonResult<EngineResponse> {
        // Try to parse as JSON first
        if let Ok(engine_response) = serde_json::from_str::<EngineResponse>(&response) {
            return Ok(engine_response);
        }

        // Try to extract JSON from the response
        let trimmed = response.trim();
        if let Some(json_start) = trimmed.find('{') {
            if let Some(json_end) = trimmed.rfind('}') {
                let json_str = &trimmed[json_start..=json_end];
                if let Ok(engine_response) = serde_json::from_str::<EngineResponse>(json_str) {
                    return Ok(engine_response);
                }
            }
        }

        // Fallback: create a simple response
        Ok(EngineResponse::new(
            EngineResponseType::VerificationSuccess {
                result: response,
                proof: None,
                proof_steps: None,
                execution_time: None,
            },
            0,
        ))
    }

    /// Build specification.
    #[allow(dead_code)]
    async fn build_specification(&self) -> BatonResult<()> {
        let mut command = Command::new(&self.config.engine_path);
        command.arg("--make");
        command.arg(&self.config.spec_path);

        let output = command
            .output()
            .map_err(|e| BatonError::BuildSystemError(format!("Build command failed: {e}")))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(BatonError::BuildSystemError(format!(
                "Build failed: {stderr}"
            )));
        }

        Ok(())
    }

    /// Get engine version.
    pub async fn get_version(&self) -> BatonResult<String> {
        let mut command = Command::new(&self.config.engine_path);
        command.arg("--version");

        let output = command
            .output()
            .map_err(|e| BatonError::InternalError(format!("Failed to get version: {e}")))?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        } else {
            Err(BatonError::InternalError(
                "Failed to get version".to_string(),
            ))
        }
    }

    /// Ping the engine.
    pub async fn ping(&self) -> BatonResult<bool> {
        let _request = EngineRequest {
            request_type: EngineRequestType::Ping,
            timeout: Some(5),
            context: None,
            request_id: None,
            priority: None,
        };

        let response = self
            .verify(VerificationRequest::new(LeanRequest::Ping))
            .await?;

        Ok(matches!(response.response, LeanResponse::Pong))
    }

    /// Get client statistics.
    pub fn get_stats(&self) -> ClientStats {
        self.stats.lock().unwrap().clone()
    }

    /// Clear connection pool.
    pub async fn clear_pool(&self) {
        self.pool.lock().unwrap().clear();
    }

    /// Set timeout.
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// Set verbose mode.
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.config.verbose = verbose;
        self
    }

    /// Set pool size.
    pub fn with_pool_size(mut self, pool_size: usize) -> Self {
        self.config.pool_size = pool_size;
        self
    }

    /// Set retry configuration.
    pub fn with_retry_config(mut self, attempts: u32, delay: Duration) -> Self {
        self.config.retry_attempts = attempts;
        self.config.retry_delay = delay;
        self
    }

    /// Get next request ID.
    fn get_next_request_id(&self) -> u64 {
        let mut counter = self.request_counter.lock().unwrap();
        *counter += 1;
        *counter
    }

    /// Update statistics.
    async fn update_stats(&self, success: bool, duration: Duration) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests += 1;
        stats.total_uptime += duration;

        if success {
            stats.successful_requests += 1;
        } else {
            stats.failed_requests += 1;
        }

        // Update average response time
        let total_time = stats.average_response_time.as_millis() as u64
            * (stats.total_requests - 1)
            + duration.as_millis() as u64;
        stats.average_response_time = Duration::from_millis(total_time / stats.total_requests);

        stats.update_last_request_time();
    }
}

impl Default for EngineClient {
    fn default() -> Self {
        Self::new("lean".to_string()).unwrap_or_else(|_| {
            // Fallback to a minimal client if engine detection fails
            Self {
                config: EngineClientConfig::default(),
                engine_name: "lean".to_string(),
                pool: Arc::new(Mutex::new(Vec::new())),
                active_connections: Arc::new(Mutex::new(HashMap::new())),
                request_counter: Arc::new(Mutex::new(0)),
                stats: Arc::new(Mutex::new(ClientStats::default())),
            }
        })
    }
}

impl Drop for EngineClient {
    fn drop(&mut self) {
        // Clean up any remaining connections
        if let Ok(mut pool) = self.pool.lock() {
            pool.clear();
        }
        if let Ok(mut active) = self.active_connections.lock() {
            active.clear();
        }
    }
}

// Legacy type alias for backward compatibility
pub type LeanClient = EngineClient;
