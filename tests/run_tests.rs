//! Test runner for the Ligature language.
//! 
//! This module provides utilities for running all tests and generating reports.

use std::time::Instant;
use std::collections::HashMap;

/// Test result information
#[derive(Debug)]
pub struct TestResult {
    pub name: String,
    pub passed: bool,
    pub duration: std::time::Duration,
    pub error_message: Option<String>,
}

/// Test suite information
#[derive(Debug)]
pub struct TestSuite {
    pub name: String,
    pub results: Vec<TestResult>,
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub duration: std::time::Duration,
}

impl TestSuite {
    pub fn new(name: String) -> Self {
        Self {
            name,
            results: Vec::new(),
            total_tests: 0,
            passed_tests: 0,
            failed_tests: 0,
            duration: std::time::Duration::ZERO,
        }
    }
    
    pub fn add_result(&mut self, result: TestResult) {
        self.total_tests += 1;
        if result.passed {
            self.passed_tests += 1;
        } else {
            self.failed_tests += 1;
        }
        self.results.push(result);
    }
    
    pub fn set_duration(&mut self, duration: std::time::Duration) {
        self.duration = duration;
    }
    
    pub fn success_rate(&self) -> f64 {
        if self.total_tests == 0 {
            0.0
        } else {
            self.passed_tests as f64 / self.total_tests as f64
        }
    }
}

/// Test runner that can execute all test suites
pub struct TestRunner {
    suites: HashMap<String, TestSuite>,
}

impl TestRunner {
    pub fn new() -> Self {
        Self {
            suites: HashMap::new(),
        }
    }
    
    /// Run all integration tests
    pub fn run_integration_tests(&mut self) {
        let start = Instant::now();
        let mut suite = TestSuite::new("Integration Tests".to_string());
        
        // Run parser tests
        self.run_test_group(&mut suite, "Parser", || {
            crate::integration::parser_tests::test_parse_literals();
            crate::integration::parser_tests::test_parse_variable_bindings();
            crate::integration::parser_tests::test_parse_record_construction();
            crate::integration::parser_tests::test_parse_function_definitions();
            crate::integration::parser_tests::test_parse_let_expressions();
            crate::integration::parser_tests::test_parse_if_expressions();
            crate::integration::parser_tests::test_parse_binary_operations();
            crate::integration::parser_tests::test_parse_unary_operations();
            crate::integration::parser_tests::test_parse_lists();
            crate::integration::parser_tests::test_parse_pattern_matching();
            crate::integration::parser_tests::test_parse_types();
            crate::integration::parser_tests::test_parse_comments();
            crate::integration::parser_tests::test_parse_complex_expressions();
            crate::integration::parser_tests::test_parse_error_handling();
            crate::integration::parser_tests::test_parse_whitespace_handling();
        });
        
        // Run evaluation tests
        self.run_test_group(&mut suite, "Evaluation", || {
            crate::integration::eval_tests::test_evaluate_literals();
            crate::integration::eval_tests::test_evaluate_arithmetic_operations();
            crate::integration::eval_tests::test_evaluate_comparison_operations();
            crate::integration::eval_tests::test_evaluate_logical_operations();
            crate::integration::eval_tests::test_evaluate_variable_bindings();
            crate::integration::eval_tests::test_evaluate_let_expressions();
            crate::integration::eval_tests::test_evaluate_if_expressions();
            crate::integration::eval_tests::test_evaluate_record_construction();
            crate::integration::eval_tests::test_evaluate_list_construction();
            crate::integration::eval_tests::test_evaluate_function_application();
            crate::integration::eval_tests::test_evaluate_lambda_expressions();
            crate::integration::eval_tests::test_evaluate_pattern_matching();
            crate::integration::eval_tests::test_evaluate_complex_expressions();
            crate::integration::eval_tests::test_evaluate_error_handling();
            crate::integration::eval_tests::test_evaluate_termination();
        });
        
        // Run function call architecture tests
        self.run_test_group(&mut suite, "Function Call Architecture", || {
            crate::integration::function_call_architecture_tests::test_environment_pooling();
            crate::integration::function_call_architecture_tests::test_stack_based_evaluation();
            crate::integration::function_call_architecture_tests::test_tail_call_optimization();
            crate::integration::function_call_architecture_tests::test_complex_function_application();
            crate::integration::function_call_architecture_tests::test_closure_capturing();
            crate::integration::function_call_architecture_tests::test_recursive_functions();
            crate::integration::function_call_architecture_tests::test_optimization_statistics();
            crate::integration::function_call_architecture_tests::test_memory_efficiency();
            crate::integration::function_call_architecture_tests::test_stack_depth_limiting();
            crate::integration::function_call_architecture_tests::test_optimization_disabling();
            crate::integration::function_call_architecture_tests::test_mixed_optimizations();
            crate::integration::function_call_architecture_tests::test_cache_performance();
        });
        
        // Run type system tests
        self.run_test_group(&mut suite, "Type System", || {
            crate::integration::type_tests::test_type_check_literals();
            crate::integration::type_tests::test_type_check_arithmetic_operations();
            crate::integration::type_tests::test_type_check_comparison_operations();
            crate::integration::type_tests::test_type_check_logical_operations();
            crate::integration::type_tests::test_type_check_function_definitions();
            crate::integration::type_tests::test_type_check_function_application();
            crate::integration::type_tests::test_type_check_let_expressions();
            crate::integration::type_tests::test_type_check_if_expressions();
            crate::integration::type_tests::test_type_check_record_construction();
            crate::integration::type_tests::test_type_check_list_construction();
            crate::integration::type_tests::test_type_check_pattern_matching();
            crate::integration::type_tests::test_type_inference();
            crate::integration::type_tests::test_type_check_error_handling();
            crate::integration::type_tests::test_type_check_complex_programs();
            crate::integration::type_tests::test_type_check_generic_functions();
            crate::integration::type_tests::test_type_check_recursive_functions();
        });
        
        // Run end-to-end tests
        self.run_test_group(&mut suite, "End-to-End", || {
            crate::integration::end_to_end_tests::test_basic_arithmetic_pipeline();
            crate::integration::end_to_end_tests::test_function_definition_and_application();
            crate::integration::end_to_end_tests::test_conditional_logic();
            crate::integration::end_to_end_tests::test_record_construction_and_access();
            crate::integration::end_to_end_tests::test_list_operations();
            crate::integration::end_to_end_tests::test_nested_function_calls();
            crate::integration::end_to_end_tests::test_let_expressions();
            crate::integration::end_to_end_tests::test_pattern_matching();
            crate::integration::end_to_end_tests::test_complex_configuration_example();
            crate::integration::end_to_end_tests::test_recursive_function();
            crate::integration::end_to_end_tests::test_multiple_bindings();
            crate::integration::end_to_end_tests::test_string_concatenation();
            crate::integration::end_to_end_tests::test_boolean_logic();
            crate::integration::end_to_end_tests::test_comparison_operations();
            crate::integration::end_to_end_tests::test_error_propagation();
            crate::integration::end_to_end_tests::test_whitespace_and_comments();
            crate::integration::end_to_end_tests::test_type_annotations();
            crate::integration::end_to_end_tests::test_complex_nested_expressions();
        });
        
        // Run error handling tests
        self.run_test_group(&mut suite, "Error Handling", || {
            crate::integration::error_handling_tests::test_parser_error_handling();
            crate::integration::error_handling_tests::test_type_checker_error_handling();
            crate::integration::error_handling_tests::test_evaluator_error_handling();
            crate::integration::error_handling_tests::test_error_message_quality();
            crate::integration::error_handling_tests::test_error_recovery();
            crate::integration::error_handling_tests::test_nested_error_handling();
            crate::integration::error_handling_tests::test_type_inference_errors();
            crate::integration::error_handling_tests::test_complex_error_scenarios();
            crate::integration::error_handling_tests::test_error_context_preservation();
        });
        
        suite.set_duration(start.elapsed());
        self.suites.insert(suite.name.clone(), suite);
    }
    
    /// Run all property-based tests
    pub fn run_property_tests(&mut self) {
        let start = Instant::now();
        let mut suite = TestSuite::new("Property Tests".to_string());
        
        // Note: Property tests are typically run with proptest! macro
        // This is a placeholder for when we implement property test execution
        
        suite.set_duration(start.elapsed());
        self.suites.insert(suite.name.clone(), suite);
    }
    
    /// Run all differential tests
    pub fn run_differential_tests(&mut self) {
        let start = Instant::now();
        let mut suite = TestSuite::new("Differential Tests".to_string());
        
        // Run specification compliance tests
        self.run_test_group(&mut suite, "Specification Compliance", || {
            crate::differential::spec_compliance_tests::test_literal_compliance();
            crate::differential::spec_compliance_tests::test_arithmetic_compliance();
            crate::differential::spec_compliance_tests::test_comparison_compliance();
            crate::differential::spec_compliance_tests::test_logical_compliance();
            crate::differential::spec_compliance_tests::test_conditional_compliance();
            crate::differential::spec_compliance_tests::test_let_expression_compliance();
            crate::differential::spec_compliance_tests::test_function_compliance();
            crate::differential::spec_compliance_tests::test_record_compliance();
            crate::differential::spec_compliance_tests::test_list_compliance();
            crate::differential::spec_compliance_tests::test_pattern_matching_compliance();
            crate::differential::spec_compliance_tests::test_type_annotation_compliance();
            crate::differential::spec_compliance_tests::test_error_handling_compliance();
            crate::differential::spec_compliance_tests::test_termination_compliance();
            crate::differential::spec_compliance_tests::test_complex_expression_compliance();
            crate::differential::spec_compliance_tests::test_specification_extraction();
        });
        
        suite.set_duration(start.elapsed());
        self.suites.insert(suite.name.clone(), suite);
    }
    
    /// Run all tests
    pub fn run_all_tests(&mut self) {
        println!("Running all tests...");
        
        self.run_integration_tests();
        self.run_property_tests();
        self.run_differential_tests();
        
        self.print_summary();
    }
    
    /// Run a test group and record results
    fn run_test_group(&mut self, suite: &mut TestSuite, group_name: &str, test_fn: impl FnOnce()) {
        let start = Instant::now();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(test_fn));
        let duration = start.elapsed();
        
        let test_result = TestResult {
            name: group_name.to_string(),
            passed: result.is_ok(),
            duration,
            error_message: result.err().map(|e| format!("{:?}", e)),
        };
        
        suite.add_result(test_result);
    }
    
    /// Print a summary of all test results
    pub fn print_summary(&self) {
        println!("\n=== Test Summary ===");
        
        let mut total_tests = 0;
        let mut total_passed = 0;
        let mut total_failed = 0;
        let mut total_duration = std::time::Duration::ZERO;
        
        for (name, suite) in &self.suites {
            println!("\n{}:", name);
            println!("  Total tests: {}", suite.total_tests);
            println!("  Passed: {}", suite.passed_tests);
            println!("  Failed: {}", suite.failed_tests);
            println!("  Success rate: {:.1}%", suite.success_rate() * 100.0);
            println!("  Duration: {:?}", suite.duration);
            
            total_tests += suite.total_tests;
            total_passed += suite.passed_tests;
            total_failed += suite.failed_tests;
            total_duration += suite.duration;
            
            // Print failed tests
            if suite.failed_tests > 0 {
                println!("  Failed tests:");
                for result in &suite.results {
                    if !result.passed {
                        println!("    - {}: {:?}", result.name, result.error_message);
                    }
                }
            }
        }
        
        println!("\n=== Overall Summary ===");
        println!("Total tests: {}", total_tests);
        println!("Passed: {}", total_passed);
        println!("Failed: {}", total_failed);
        println!("Success rate: {:.1}%", if total_tests > 0 { total_passed as f64 / total_tests as f64 * 100.0 } else { 0.0 });
        println!("Total duration: {:?}", total_duration);
        
        if total_failed > 0 {
            std::process::exit(1);
        }
    }
}

/// Run all tests and generate a report
pub fn run_tests() {
    let mut runner = TestRunner::new();
    runner.run_all_tests();
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_test_runner_creation() {
        let runner = TestRunner::new();
        assert_eq!(runner.suites.len(), 0);
    }
    
    #[test]
    fn test_test_suite_creation() {
        let mut suite = TestSuite::new("Test Suite".to_string());
        assert_eq!(suite.name, "Test Suite");
        assert_eq!(suite.total_tests, 0);
        assert_eq!(suite.passed_tests, 0);
        assert_eq!(suite.failed_tests, 0);
        assert_eq!(suite.success_rate(), 0.0);
    }
    
    #[test]
    fn test_test_suite_add_result() {
        let mut suite = TestSuite::new("Test Suite".to_string());
        
        let result = TestResult {
            name: "Test 1".to_string(),
            passed: true,
            duration: std::time::Duration::from_millis(100),
            error_message: None,
        };
        
        suite.add_result(result);
        assert_eq!(suite.total_tests, 1);
        assert_eq!(suite.passed_tests, 1);
        assert_eq!(suite.failed_tests, 0);
        assert_eq!(suite.success_rate(), 1.0);
    }
} 