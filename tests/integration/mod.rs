//! Integration tests for the Ligature language.
//!
//! These tests verify that all components work together correctly.

pub mod binding_conflicts_tests;
pub mod comprehensive_tests;
pub mod end_to_end_tests;
pub mod enhanced_error_reporting_tests;
pub mod error_handling_tests;
pub mod eval_tests;
pub mod function_call_architecture_tests;
pub mod parser_tests;
pub mod pattern_guards_tests;
pub mod precedence_comprehensive_test;
pub mod real_world_examples;
pub mod subtyping_demo;
pub mod subtyping_tests;
pub mod test_evaluation;
pub mod test_parse;
pub mod test_parser;
pub mod test_simple;
pub mod test_type_inference;
pub mod type_class_tests;
pub mod type_tests;
pub mod union_type_inference_tests;
pub mod value_optimization_tests;

use ligature_ast::AstResult;
use ligature_eval::evaluate_program;
use ligature_parser::parse_program;
use ligature_types::type_check_program;

/// Helper function to parse, type check, and evaluate a program
pub fn parse_type_check_and_evaluate(source: &str) -> AstResult<ligature_eval::Value> {
    let program = parse_program(source)?;
    type_check_program(&program)?;
    evaluate_program(&program)
}

/// Helper function to create a test environment
pub fn create_test_environment() -> ligature_eval::Environment {
    let mut env = ligature_eval::Environment::new();

    // Add standard library functions
    env.bind(
        "add",
        ligature_eval::Value::Function(Box::new(|args| {
            if args.len() != 2 {
                return Err(ligature_ast::AstError::new("add expects 2 arguments"));
            }
            match (&args[0], &args[1]) {
                (ligature_eval::Value::Integer(a), ligature_eval::Value::Integer(b)) => {
                    Ok(ligature_eval::Value::Integer(a + b))
                }
                _ => Err(ligature_ast::AstError::new("add expects integer arguments")),
            }
        })),
    );

    env.bind(
        "multiply",
        ligature_eval::Value::Function(Box::new(|args| {
            if args.len() != 2 {
                return Err(ligature_ast::AstError::new("multiply expects 2 arguments"));
            }
            match (&args[0], &args[1]) {
                (ligature_eval::Value::Integer(a), ligature_eval::Value::Integer(b)) => {
                    Ok(ligature_eval::Value::Integer(a * b))
                }
                _ => Err(ligature_ast::AstError::new(
                    "multiply expects integer arguments",
                )),
            }
        })),
    );

    env
}
