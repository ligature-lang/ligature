//! Client statistics and metrics.

use std::time::{Duration, Instant};

/// Client statistics.
#[derive(Debug, Clone)]
pub struct ClientStats {
    /// Total number of requests
    pub total_requests: u64,
    /// Number of successful requests
    pub successful_requests: u64,
    /// Number of failed requests
    pub failed_requests: u64,
    /// Total uptime
    pub total_uptime: Duration,
    /// Average response time
    pub average_response_time: Duration,
    /// Last request time
    pub last_request_time: Option<Instant>,
}

impl Default for ClientStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            total_uptime: Duration::ZERO,
            average_response_time: Duration::ZERO,
            last_request_time: None,
        }
    }
}

impl ClientStats {
    /// Update the last request time.
    pub fn update_last_request_time(&mut self) {
        self.last_request_time = Some(Instant::now());
    }
}
