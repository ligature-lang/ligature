//! Lean client for Baton formal verification.
//!
//! This crate provides the client for communicating with the Lean theorem prover.

use baton_core::prelude::*;
use baton_error::prelude::*;
use baton_protocol::prelude::*;
use serde_json;
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write, Read};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tempfile::NamedTempFile;
use uuid::Uuid;

/// Configuration for Lean client.
#[derive(Debug, Clone)]
pub struct LeanClientConfig {
    /// Path to Lean executable
    pub lean_path: String,
    /// Path to specification directory
    pub spec_path: String,
    /// Process timeout
    pub timeout: Duration,
    /// Whether to use verbose output
    pub verbose: bool,
    /// Maximum number of concurrent processes
    pub max_processes: usize,
    /// Connection pool size
    pub pool_size: usize,
    /// Retry attempts for failed operations
    pub retry_attempts: u32,
    /// Retry delay between attempts
    pub retry_delay: Duration,
    /// Whether to enable connection pooling
    pub enable_pooling: bool,
    /// Whether to enable debug logging
    pub debug_logging: bool,
}

impl Default for LeanClientConfig {
    fn default() -> Self {
        Self {
            lean_path: String::new(),
            spec_path: String::new(),
            timeout: Duration::from_secs(30),
            verbose: false,
            max_processes: 4,
            pool_size: 2,
            retry_attempts: 3,
            retry_delay: Duration::from_millis(100),
            enable_pooling: true,
            debug_logging: false,
        }
    }
}

/// Debug logging macro
macro_rules! debug_log {
    ($config:expr, $($arg:tt)*) => {
        if $config.debug_logging {
            eprintln!("[LEAN DEBUG] {}", format!($($arg)*));
        }
    };
}

/// Lean process connection.
struct LeanConnection {
    process: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    last_used: Instant,
    request_count: u64,
}

/// Client for communicating with Lean process.
pub struct LeanClient {
    /// Client configuration
    config: LeanClientConfig,
    /// Connection pool
    pool: Arc<Mutex<Vec<LeanConnection>>>,
    /// Active connections
    active_connections: Arc<Mutex<HashMap<String, LeanConnection>>>,
    /// Request counter
    request_counter: Arc<Mutex<u64>>,
    /// Statistics
    stats: Arc<Mutex<ClientStats>>,
}

/// Client statistics.
#[derive(Debug, Clone)]
pub struct ClientStats {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: Duration,
    pub total_uptime: Duration,
    pub last_request_time: Option<Instant>,
}

impl Default for ClientStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            average_response_time: Duration::ZERO,
            total_uptime: Duration::ZERO,
            last_request_time: None,
        }
    }
}

impl LeanClient {
    /// Create a new Lean client with default configuration.
    pub fn new() -> BatonResult<Self> {
        let config = LeanClientConfig::default();
        Self::with_config(config)
    }

    /// Create a new Lean client with custom configuration.
    pub fn with_config(mut config: LeanClientConfig) -> BatonResult<Self> {
        // Find Lean executable if not provided
        if config.lean_path.is_empty() {
            config.lean_path = Self::find_lean_executable()?;
        }

        // Find specification path if not provided
        if config.spec_path.is_empty() {
            config.spec_path = Self::find_specification_path()?;
        }

        Ok(Self {
            config,
            pool: Arc::new(Mutex::new(Vec::new())),
            active_connections: Arc::new(Mutex::new(HashMap::new())),
            request_counter: Arc::new(Mutex::new(0)),
            stats: Arc::new(Mutex::new(ClientStats::default())),
        })
    }

    /// Find Lean executable in system PATH.
    fn find_lean_executable() -> BatonResult<String> {
        // Try common Lean executable names
        let lean_names = ["lean", "lean4", "lean.exe"];
        
        for name in lean_names {
            if let Ok(output) = std::process::Command::new("which")
                .arg(name)
                .output()
            {
                if output.status.success() {
                    let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
                    if !path.is_empty() {
                        return Ok(path);
                    }
                }
            }
        }

        Err(BatonError::ConfigurationError(
            "Lean executable not found in PATH".to_string(),
        ))
    }

    /// Find specification directory.
    fn find_specification_path() -> BatonResult<String> {
        // Try to find specification in common locations
        let spec_paths = [
            "./spec",
            "./specifications",
            "./lean-spec",
            "../spec",
            "../specifications",
        ];

        for path in spec_paths {
            if std::path::Path::new(path).exists() {
                return Ok(path.to_string());
            }
        }

        // Create default specification directory
        let default_path = "./spec";
        std::fs::create_dir_all(default_path).map_err(|e| {
            BatonError::FileSystemError(format!("Failed to create spec directory: {}", e))
        })?;

        Ok(default_path.to_string())
    }

    /// Execute a verification request.
    pub async fn verify(&self, request: VerificationRequest) -> BatonResult<VerificationResponse> {
        let start_time = Instant::now();
        let context = ErrorContext::new("verify".to_string());

        // Update statistics
        {
            let mut stats = self.stats.lock().unwrap();
            stats.total_requests += 1;
            stats.last_request_time = Some(Instant::now());
        }

        let result = self.execute_with_retry(request, &context).await;

        // Update statistics
        {
            let mut stats = self.stats.lock().unwrap();
            let response_time = start_time.elapsed();
            stats.total_uptime += response_time;

            match &result {
                Ok(_) => stats.successful_requests += 1,
                Err(_) => stats.failed_requests += 1,
            }

            // Update average response time
            if stats.total_requests > 0 {
                let total_time = stats.average_response_time.as_millis() as u64 * (stats.total_requests - 1) + response_time.as_millis() as u64;
                stats.average_response_time = Duration::from_millis(total_time / stats.total_requests);
            }
        }

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
                        debug_log!(self.config, "Retry attempt {} for request", attempt + 1);
                        tokio::time::sleep(self.config.retry_delay).await;
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| {
            BatonError::InternalError("Unknown error during retry".to_string())
        }))
    }

    /// Execute a single request.
    async fn execute_single_request(
        &self,
        request: &VerificationRequest,
    ) -> BatonResult<VerificationResponse> {
        let start_time = Instant::now();

        // Get connection from pool or create new one
        let connection = if self.config.enable_pooling {
            self.get_connection().await?
        } else {
            self.create_connection().await?
        };

        // Create input file for Lean
        let input_file = self.create_input_file(&request.request).await?;
        let input_path = input_file.path().to_string_lossy().to_string();

        // Execute Lean process
        let output = self
            .run_lean_process_with_connection(connection, &input_path)
            .await?;

        // Parse response
        let lean_response = self.parse_lean_response(output)?;

        let execution_time = start_time.elapsed().as_millis() as u64;
        let response = VerificationResponse::new(lean_response, execution_time);

        Ok(response)
    }

    /// Get connection from pool or create new one.
    async fn get_connection(&self) -> BatonResult<LeanConnection> {
        // Try to get connection from pool
        {
            let mut pool = self.pool.lock().unwrap();
            if let Some(connection) = pool.pop() {
                return Ok(connection);
            }
        }

        // Create new connection if pool is empty
        self.create_connection().await
    }

    /// Create a new Lean connection.
    async fn create_connection(&self) -> BatonResult<LeanConnection> {
        debug_log!(self.config, "Creating new Lean connection");

        let mut command = Command::new(&self.config.lean_path);
        command
            .arg("--json")
            .arg("--server")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        if self.config.verbose {
            command.arg("--verbose");
        }

        let mut child = command.spawn().map_err(|e| {
            BatonError::ProcessStart(format!("Failed to start Lean process: {}", e))
        })?;

        let stdin = child.stdin.take().ok_or_else(|| {
            BatonError::ProcessStart("Failed to get stdin from Lean process".to_string())
        })?;

        let stdout = child.stdout.take().ok_or_else(|| {
            BatonError::ProcessStart("Failed to get stdout from Lean process".to_string())
        })?;

        let connection = LeanConnection {
            process: child,
            stdin,
            stdout: BufReader::new(stdout),
            last_used: Instant::now(),
            request_count: 0,
        };

        Ok(connection)
    }

    /// Run Lean process with connection.
    async fn run_lean_process_with_connection(
        &self,
        mut connection: LeanConnection,
        input_file: &str,
    ) -> BatonResult<String> {
        // Create Lean script
        let script = self.create_lean_script(input_file)?;

        // Write script to stdin
        connection
            .stdin
            .write_all(script.as_bytes())
            .map_err(|e| BatonError::Communication(format!("Failed to write to stdin: {}", e)))?;

        connection
            .stdin
            .flush()
            .map_err(|e| BatonError::Communication(format!("Failed to flush stdin: {}", e)))?;

        // Read response
        let response = self.read_lean_response(&mut connection.stdout).await?;

        // Update connection stats
        connection.last_used = Instant::now();
        connection.request_count += 1;

        // Return connection to pool if enabled
        if self.config.enable_pooling {
            let mut pool = self.pool.lock().unwrap();
            if pool.len() < self.config.pool_size {
                pool.push(connection);
            }
        }

        Ok(response)
    }

    /// Read response from Lean process.
    async fn read_lean_response(&self, stdout: &mut BufReader<ChildStdout>) -> BatonResult<String> {
        let mut response = String::new();
        let mut buffer = [0; 1024];
        let timeout = self.config.timeout;
        let start_time = Instant::now();

        loop {
            if start_time.elapsed() > timeout {
                return Err(BatonError::Timeout(format!(
                    "Timeout reading response after {:?}",
                    timeout
                )));
            }

            // Try to read from stdout
            match stdout.read(&mut buffer) {
                Ok(0) => break, // EOF
                Ok(n) => {
                    response.push_str(&String::from_utf8_lossy(&buffer[..n]));
                    
                    // Check if we have a complete JSON response
                    if response.trim().ends_with('}') || response.trim().ends_with(']') {
                        break;
                    }
                }
                Err(e) => {
                    if e.kind() == std::io::ErrorKind::WouldBlock {
                        // Non-blocking read, wait a bit
                        tokio::time::sleep(Duration::from_millis(10)).await;
                        continue;
                    } else {
                        return Err(BatonError::Communication(format!(
                            "Error reading from stdout: {}",
                            e
                        )));
                    }
                }
            }
        }

        Ok(response)
    }

    /// Create input file for Lean request.
    async fn create_input_file(&self, request: &LeanRequest) -> BatonResult<NamedTempFile> {
        let json = serde_json::to_string(request).map_err(|e| {
            BatonError::SerializationError(format!("Failed to serialize request: {}", e))
        })?;

        let mut temp_file = NamedTempFile::new().map_err(|e| {
            BatonError::FileSystemError(format!("Failed to create temp file: {}", e))
        })?;

        temp_file
            .write_all(json.as_bytes())
            .map_err(|e| BatonError::FileSystemError(format!("Failed to write to temp file: {}", e)))?;

        Ok(temp_file)
    }

    /// Create Lean script file.
    async fn create_lean_file(&self, input_file: &str) -> BatonResult<NamedTempFile> {
        let script = self.create_lean_script(input_file)?;

        let mut temp_file = NamedTempFile::new().map_err(|e| {
            BatonError::FileSystemError(format!("Failed to create temp file: {}", e))
        })?;

        temp_file
            .write_all(script.as_bytes())
            .map_err(|e| BatonError::FileSystemError(format!("Failed to write to temp file: {}", e)))?;

        Ok(temp_file)
    }

    /// Create Lean script content.
    fn create_lean_script(&self, input_file: &str) -> BatonResult<String> {
        let script = format!(
            r#"
import Lean.Data.Json
import Lean.Data.Json.FromToJson

-- Load input file
def input := IO.FS.readFile "{}"

-- Process the input and return result
def main : IO Unit := do
  let input ← input
  let json := Json.parse input
  match json with
  | Except.ok json => 
    IO.println (Json.pretty json)
  | Except.error err => 
    IO.eprintln s!"Error parsing JSON: {{err}}"
"#,
            input_file
        );

        Ok(script)
    }

    /// Parse Lean output.
    fn parse_lean_output(&self, output: &std::process::Output) -> BatonResult<LeanResponse> {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            return Err(BatonError::VerificationFailed(format!(
                "Lean process failed: {}",
                stderr
            )));
        }

        self.parse_lean_response(stdout.to_string())
    }

    /// Parse Lean response string.
    fn parse_lean_response(&self, response: String) -> BatonResult<LeanResponse> {
        let trimmed = response.trim();
        
        if trimmed.is_empty() {
            return Err(BatonError::Communication("Empty response from Lean".to_string()));
        }

        // Try to parse as JSON
        match serde_json::from_str::<LeanResponse>(trimmed) {
            Ok(response) => Ok(response),
            Err(e) => {
                // If JSON parsing fails, try to extract error information
                if trimmed.contains("error") || trimmed.contains("Error") {
                    return Err(BatonError::VerificationFailed(format!(
                        "Lean verification failed: {}",
                        trimmed
                    )));
                }

                Err(BatonError::DeserializationError(format!(
                    "Failed to parse Lean response: {}",
                    e
                )))
            }
        }
    }

    /// Build specification.
    async fn build_specification(&self) -> BatonResult<()> {
        debug_log!(self.config, "Building specification at {}", self.config.spec_path);

        let output = Command::new(&self.config.lean_path)
            .arg("--make")
            .arg(&self.config.spec_path)
            .output()
            .map_err(|e| BatonError::BuildSystemError(format!("Failed to build spec: {}", e)))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(BatonError::CompilationError(format!(
                "Specification build failed: {}",
                stderr
            )));
        }

        Ok(())
    }

    /// Get Lean version.
    pub async fn get_version(&self) -> BatonResult<String> {
        let request = VerificationRequest::new(LeanRequest::GetVersion);
        let response = self.verify(request).await?;

        match response.response {
            LeanResponse::Version { version, .. } => Ok(version),
            _ => Err(BatonError::VerificationFailed(
                "Unexpected response type for version request".to_string(),
            )),
        }
    }

    /// Ping Lean process.
    pub async fn ping(&self) -> BatonResult<bool> {
        let request = VerificationRequest::new(LeanRequest::Ping);
        let response = self.verify(request).await?;

        match response.response {
            LeanResponse::Pong => Ok(true),
            _ => Ok(false),
        }
    }

    /// Get client statistics.
    pub fn get_stats(&self) -> ClientStats {
        self.stats.lock().unwrap().clone()
    }

    /// Clear connection pool.
    pub async fn clear_pool(&self) {
        let mut pool = self.pool.lock().unwrap();
        pool.clear();
    }

    /// Set timeout for the client.
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// Set verbose mode for the client.
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.config.verbose = verbose;
        self
    }

    /// Set pool size for the client.
    pub fn with_pool_size(mut self, pool_size: usize) -> Self {
        self.config.pool_size = pool_size;
        self
    }

    /// Set retry configuration for the client.
    pub fn with_retry_config(mut self, attempts: u32, delay: Duration) -> Self {
        self.config.retry_attempts = attempts;
        self.config.retry_delay = delay;
        self
    }
}

impl Default for LeanClient {
    fn default() -> Self {
        Self::new().unwrap_or_else(|_| {
            // Fallback to basic configuration if Lean is not available
            let mut config = LeanClientConfig::default();
            config.lean_path = "lean".to_string();
            config.spec_path = "./spec".to_string();
            Self {
                config,
                pool: Arc::new(Mutex::new(Vec::new())),
                active_connections: Arc::new(Mutex::new(HashMap::new())),
                request_counter: Arc::new(Mutex::new(0)),
                stats: Arc::new(Mutex::new(ClientStats::default())),
            }
        })
    }
}

impl Drop for LeanClient {
    fn drop(&mut self) {
        // Clean up any remaining connections
        let mut pool = self.pool.lock().unwrap();
        pool.clear();
    }
}

/// Re-export commonly used types
pub mod prelude {
    pub use super::{
        LeanClient, LeanClientConfig, ClientStats,
    };
} 