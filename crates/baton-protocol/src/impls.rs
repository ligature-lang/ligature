//! Implementations for protocol types.

use baton_core::RequestPriority;

use crate::types::*;

impl std::fmt::Display for LeanRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeanRequest::VerifyEvaluation {
                expression,
                expected_value,
                ..
            } => {
                write!(f, "VerifyEvaluation({expression} = {expected_value})")
            }
            LeanRequest::VerifyTypeCheck {
                expression,
                expected_type,
                ..
            } => {
                write!(f, "VerifyTypeCheck({expression}: {expected_type})")
            }
            LeanRequest::VerifyOperationalSemantics {
                expression,
                expected_steps,
                ..
            } => {
                write!(
                    f,
                    "VerifyOperationalSemantics({expression} -> {expected_steps:?})"
                )
            }
            LeanRequest::VerifyTypeSafety { expression, .. } => {
                write!(f, "VerifyTypeSafety({expression})")
            }
            LeanRequest::VerifyTermination { expression, .. } => {
                write!(f, "VerifyTermination({expression})")
            }
            LeanRequest::VerifyDeterminism { expression, .. } => {
                write!(f, "VerifyDeterminism({expression})")
            }
            LeanRequest::VerifyConfigurationValidation {
                configuration,
                schema,
                ..
            } => {
                write!(
                    f,
                    "VerifyConfigurationValidation({configuration} against {schema})"
                )
            }
            LeanRequest::ExtractTestCases {
                specification_file,
                test_type,
            } => {
                write!(f, "ExtractTestCases({specification_file}, {test_type:?})")
            }
            LeanRequest::CompareResults {
                rust_result,
                lean_result,
                comparison_type,
            } => {
                write!(
                    f,
                    "CompareResults({rust_result} vs {lean_result}, {comparison_type:?})"
                )
            }
            LeanRequest::RunDifferentialTest {
                test_case,
                test_type,
                ..
            } => {
                write!(f, "RunDifferentialTest({test_case}, {test_type:?})")
            }
            LeanRequest::CheckSpecification {
                specification_file,
                check_type,
            } => {
                write!(
                    f,
                    "CheckSpecification({specification_file}, {check_type:?})"
                )
            }
            LeanRequest::GetVersion => write!(f, "GetVersion"),
            LeanRequest::Ping => write!(f, "Ping"),
            LeanRequest::VerifyTheorem {
                theorem,
                proof,
                timeout,
                ..
            } => {
                write!(
                    f,
                    "VerifyTheorem({}, proof: {}, timeout: {:?})",
                    theorem,
                    proof.is_some(),
                    timeout
                )
            }
            LeanRequest::VerifyLemma {
                lemma,
                proof,
                dependencies,
                ..
            } => {
                write!(
                    f,
                    "VerifyLemma({}, proof: {}, deps: {:?})",
                    lemma,
                    proof.is_some(),
                    dependencies
                )
            }
            LeanRequest::CheckConsistency {
                specification_files,
                check_type,
            } => {
                write!(
                    f,
                    "CheckConsistency({specification_files:?}, {check_type:?})"
                )
            }
            LeanRequest::GenerateCounterexample { property, .. } => {
                write!(f, "GenerateCounterexample({property})")
            }
            LeanRequest::VerifyInvariant {
                invariant,
                expression,
                ..
            } => {
                write!(f, "VerifyInvariant({invariant} for {expression})")
            }
            LeanRequest::VerifyRefinement {
                abstract_spec,
                concrete_spec,
                refinement_relation,
                ..
            } => {
                write!(
                    f,
                    "VerifyRefinement({abstract_spec} -> {concrete_spec} via \
                     {refinement_relation})"
                )
            }
        }
    }
}

impl VerificationRequest {
    /// Create a new verification request.
    pub fn new(request: LeanRequest) -> Self {
        Self {
            request,
            timeout: None,
            context: None,
            request_id: None,
            priority: None,
        }
    }

    /// Set timeout for the request.
    pub fn with_timeout(mut self, timeout: u64) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set context for the request.
    pub fn with_context(mut self, context: serde_json::Value) -> Self {
        self.context = Some(context);
        self
    }

    /// Set request ID for tracking.
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }

    /// Set priority level.
    pub fn with_priority(mut self, priority: RequestPriority) -> Self {
        self.priority = Some(priority);
        self
    }
}

impl VerificationResponse {
    /// Create a new verification response.
    pub fn new(response: LeanResponse, execution_time: u64) -> Self {
        Self {
            response,
            execution_time,
            metadata: None,
            request_id: None,
            timestamp: Some(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs(),
            ),
        }
    }

    /// Add metadata to the response.
    pub fn with_metadata(mut self, metadata: serde_json::Value) -> Self {
        self.metadata = Some(metadata);
        self
    }

    /// Set request ID for tracking.
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }

    /// Check if the response indicates success.
    pub fn is_success(&self) -> bool {
        matches!(
            self.response,
            LeanResponse::VerificationSuccess { .. }
                | LeanResponse::TestCasesExtracted { .. }
                | LeanResponse::ResultsComparison {
                    match_result: true,
                    ..
                }
                | LeanResponse::DifferentialTestResult { success: true, .. }
                | LeanResponse::SpecificationCheckResult { success: true, .. }
                | LeanResponse::Version { .. }
                | LeanResponse::Pong
                | LeanResponse::TheoremVerificationResult { success: true, .. }
                | LeanResponse::ConsistencyCheckResult {
                    consistent: true,
                    ..
                }
                | LeanResponse::CounterexampleResult { found: true, .. }
                | LeanResponse::InvariantVerificationResult { holds: true, .. }
                | LeanResponse::RefinementVerificationResult { valid: true, .. }
        )
    }

    /// Get error message if the response indicates failure.
    pub fn error_message(&self) -> Option<&str> {
        match &self.response {
            LeanResponse::VerificationFailure { error, .. } => Some(error),
            LeanResponse::Error { error, .. } => Some(error),
            _ => None,
        }
    }

    /// Get execution time in milliseconds.
    pub fn execution_time_ms(&self) -> u64 {
        self.execution_time
    }

    /// Get execution time in seconds.
    pub fn execution_time_s(&self) -> f64 {
        self.execution_time as f64 / 1000.0
    }
}
