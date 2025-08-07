//! Engine connection management.

use std::io::BufReader;
use std::process::{Child, ChildStdin, ChildStdout};
use std::time::Instant;

/// Engine process connection.
pub struct EngineConnection {
    pub process: Child,
    pub stdin: ChildStdin,
    pub stdout: BufReader<ChildStdout>,
    pub last_used: Instant,
    pub request_count: u64,
}
