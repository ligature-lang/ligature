//! Type definitions for the Baton protocol.

use baton_core::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Request sent to Lean for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LeanRequest {
    /// Verify expression evaluation
    VerifyEvaluation {
        expression: String,
        expected_value: String,
        context: Option<VerificationContext>,
    },

    /// Verify type checking
    VerifyTypeCheck {
        expression: String,
        expected_type: String,
        context: Option<VerificationContext>,
    },

    /// Verify operational semantics
    VerifyOperationalSemantics {
        expression: String,
        expected_steps: Vec<String>,
        context: Option<VerificationContext>,
    },

    /// Verify type safety
    VerifyTypeSafety {
        expression: String,
        context: Option<VerificationContext>,
    },

    /// Verify termination
    VerifyTermination {
        expression: String,
        context: Option<VerificationContext>,
    },

    /// Verify determinism
    VerifyDeterminism {
        expression: String,
        context: Option<VerificationContext>,
    },

    /// Verify configuration validation
    VerifyConfigurationValidation {
        configuration: String,
        schema: String,
        context: Option<VerificationContext>,
    },

    /// Extract test cases from specification
    ExtractTestCases {
        specification_file: String,
        test_type: Option<TestType>,
    },

    /// Compare Rust and Lean results
    CompareResults {
        rust_result: String,
        lean_result: String,
        comparison_type: ComparisonType,
    },

    /// Run differential test
    RunDifferentialTest {
        test_case: String,
        test_type: DifferentialTestType,
        context: Option<VerificationContext>,
    },

    /// Check Lean specification compilation
    CheckSpecification {
        specification_file: String,
        check_type: SpecificationCheckType,
    },

    /// Get Lean version
    GetVersion,

    /// Ping Lean process
    Ping,

    /// Verify theorem
    VerifyTheorem {
        theorem: String,
        proof: Option<String>,
        timeout: Option<u64>,
        context: Option<VerificationContext>,
    },

    /// Verify lemma
    VerifyLemma {
        lemma: String,
        proof: Option<String>,
        dependencies: Vec<String>,
        context: Option<VerificationContext>,
    },

    /// Check specification consistency
    CheckConsistency {
        specification_files: Vec<String>,
        check_type: ConsistencyCheckType,
    },

    /// Generate counterexample
    GenerateCounterexample {
        property: String,
        context: Option<VerificationContext>,
    },

    /// Verify invariant
    VerifyInvariant {
        invariant: String,
        expression: String,
        context: Option<VerificationContext>,
    },

    /// Verify refinement
    VerifyRefinement {
        abstract_spec: String,
        concrete_spec: String,
        refinement_relation: String,
        context: Option<VerificationContext>,
    },
}

/// Response from Lean verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LeanResponse {
    /// Verification successful
    VerificationSuccess {
        result: String,
        proof: Option<String>,
        proof_steps: Option<Vec<String>>,
        execution_time: Option<u64>,
    },

    /// Verification failed
    VerificationFailure {
        error: String,
        details: Option<String>,
        error_type: Option<ErrorType>,
        suggestions: Option<Vec<String>>,
    },

    /// Test cases extracted
    TestCasesExtracted {
        test_cases: Vec<String>,
        test_count: usize,
        coverage_info: Option<CoverageInfo>,
    },

    /// Results comparison
    ResultsComparison {
        match_result: bool,
        differences: Vec<String>,
        similarity_score: Option<f64>,
        detailed_comparison: Option<DetailedComparison>,
    },

    /// Differential test result
    DifferentialTestResult {
        success: bool,
        rust_result: String,
        lean_result: String,
        match_result: bool,
        performance_comparison: Option<PerformanceComparison>,
    },

    /// Specification check result
    SpecificationCheckResult {
        success: bool,
        errors: Vec<String>,
        warnings: Vec<String>,
        info: Vec<String>,
        build_time: Option<u64>,
        dependency_info: Option<DependencyInfo>,
    },

    /// Version information
    Version {
        version: String,
        commit: String,
        build_date: Option<String>,
        features: Option<Vec<String>>,
    },

    /// Pong response
    Pong,

    /// Error response
    Error {
        error: String,
        details: Option<String>,
        error_type: Option<ErrorType>,
        recovery_suggestions: Option<Vec<String>>,
    },

    /// Theorem verification result
    TheoremVerificationResult {
        success: bool,
        proof: Option<String>,
        proof_steps: Option<Vec<String>>,
        execution_time: u64,
        theorem_info: Option<TheoremInfo>,
    },

    /// Consistency check result
    ConsistencyCheckResult {
        consistent: bool,
        inconsistencies: Vec<String>,
        suggestions: Vec<String>,
        check_time: u64,
    },

    /// Counterexample result
    CounterexampleResult {
        found: bool,
        counterexample: Option<String>,
        explanation: Option<String>,
        generation_time: u64,
    },

    /// Invariant verification result
    InvariantVerificationResult {
        holds: bool,
        violation_point: Option<String>,
        proof: Option<String>,
        verification_time: u64,
    },

    /// Refinement verification result
    RefinementVerificationResult {
        valid: bool,
        refinement_proof: Option<String>,
        abstraction_mapping: Option<String>,
        verification_time: u64,
    },
}

/// Verification context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationContext {
    pub environment: Option<HashMap<String, String>>,
    pub assumptions: Vec<String>,
    pub constraints: Vec<String>,
    pub metadata: Option<HashMap<String, serde_json::Value>>,
    pub timeout: Option<u64>,
    pub verbose: Option<bool>,
}

/// Test types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TestType {
    Unit,
    Integration,
    Property,
    Regression,
    Performance,
    All,
}

/// Comparison types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComparisonType {
    Exact,
    Structural,
    Semantic,
    Performance,
    All,
}

/// Differential test types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DifferentialTestType {
    /// Expression evaluation test
    Evaluation,
    /// Type checking test
    TypeCheck,
    /// Operational semantics test
    OperationalSemantics,
    /// Configuration validation test
    ConfigurationValidation,
    /// Performance test
    Performance,
    /// Memory usage test
    MemoryUsage,
    /// All tests
    All,
}

/// Specification check types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpecificationCheckType {
    Syntax,
    Type,
    Semantics,
    Consistency,
    Completeness,
    All,
}

/// Consistency check types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConsistencyCheckType {
    Type,
    Semantics,
    Axioms,
    Theorems,
    All,
}

/// Error types.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorType {
    Syntax,
    Type,
    Semantics,
    Logic,
    Timeout,
    Resource,
    System,
    Unknown,
}

/// Coverage information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageInfo {
    pub line_coverage: f64,
    pub branch_coverage: f64,
    pub function_coverage: f64,
    pub uncovered_lines: Vec<u32>,
    pub uncovered_branches: Vec<String>,
}

/// Detailed comparison information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetailedComparison {
    pub structural_match: bool,
    pub semantic_match: bool,
    pub performance_match: bool,
    pub differences: Vec<Difference>,
}

/// Difference information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Difference {
    pub field: String,
    pub expected: String,
    pub actual: String,
    pub severity: DifferenceSeverity,
}

/// Difference severity levels.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DifferenceSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// Performance comparison information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceComparison {
    pub rust_time: u64,
    pub lean_time: u64,
    pub speedup: f64,
    pub memory_usage: Option<MemoryUsage>,
}

/// Memory usage information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryUsage {
    pub rust_memory: u64,
    pub lean_memory: u64,
    pub memory_ratio: f64,
}

/// Dependency information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyInfo {
    pub direct_dependencies: Vec<String>,
    pub transitive_dependencies: Vec<String>,
    #[allow(clippy::type_complexity)]
    pub dependency_tree: Option<HashMap<String, Vec<String>>>,
}

/// Theorem information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremInfo {
    pub name: String,
    pub statement: String,
    pub proof_length: Option<usize>,
    pub complexity: Option<String>,
    pub dependencies: Vec<String>,
}

/// Verification request.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationRequest {
    /// The request type
    pub request: LeanRequest,
    /// Timeout in seconds
    pub timeout: Option<u64>,
    /// Additional context
    pub context: Option<serde_json::Value>,
    /// Request ID for tracking
    pub request_id: Option<String>,
    /// Priority level
    pub priority: Option<RequestPriority>,
}

/// Verification response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResponse {
    /// The response from Lean
    pub response: LeanResponse,
    /// Execution time in milliseconds
    pub execution_time: u64,
    /// Additional metadata
    pub metadata: Option<serde_json::Value>,
    /// Request ID for tracking
    pub request_id: Option<String>,
    /// Response timestamp
    pub timestamp: Option<u64>,
} 