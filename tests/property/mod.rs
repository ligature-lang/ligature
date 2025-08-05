//! Property-based tests for the Ligature language.
//! 
//! These tests use property-based testing to verify that the language
//! satisfies various properties and invariants.

pub mod parser_properties;
pub mod eval_properties;
pub mod type_properties;
pub mod roundtrip_properties;

use proptest::prelude::*;
use ligature_parser::{parse_program, parse_expression};
use ligature_eval::{evaluate_program, evaluate_expression};
use ligature_types::{type_check_program, infer_expression};
use ligature_ast::{Expr, Value, Type, AstResult};

/// Helper function to generate random integer expressions
pub fn integer_expr_strategy() -> impl Strategy<Value = String> {
    any::<i64>().prop_map(|n| n.to_string())
}

/// Helper function to generate random string expressions
pub fn string_expr_strategy() -> impl Strategy<Value = String> {
    any::<String>().prop_map(|s| format!("\"{}\"", s.replace("\"", "\\\"")))
}

/// Helper function to generate random boolean expressions
pub fn boolean_expr_strategy() -> impl Strategy<Value = String> {
    prop_oneof![Just("true".to_string()), Just("false".to_string())]
}

/// Helper function to generate random arithmetic expressions
pub fn arithmetic_expr_strategy() -> impl Strategy<Value = String> {
    let integer = integer_expr_strategy();
    let op = prop_oneof![
        Just("+".to_string()),
        Just("-".to_string()),
        Just("*".to_string()),
        Just("/".to_string())
    ];
    
    (integer.clone(), op, integer).prop_map(|(a, op, b)| {
        format!("{} {} {}", a, op, b)
    })
}

/// Helper function to generate random comparison expressions
pub fn comparison_expr_strategy() -> impl Strategy<Value = String> {
    let integer = integer_expr_strategy();
    let op = prop_oneof![
        Just(">".to_string()),
        Just("<".to_string()),
        Just("==".to_string()),
        Just("!=".to_string())
    ];
    
    (integer.clone(), op, integer).prop_map(|(a, op, b)| {
        format!("{} {} {}", a, op, b)
    })
}

/// Helper function to generate random logical expressions
pub fn logical_expr_strategy() -> impl Strategy<Value = String> {
    let boolean = boolean_expr_strategy();
    let op = prop_oneof![
        Just("&&".to_string()),
        Just("||".to_string())
    ];
    
    (boolean.clone(), op, boolean).prop_map(|(a, op, b)| {
        format!("{} {} {}", a, op, b)
    })
}

/// Helper function to generate random variable binding expressions
pub fn binding_expr_strategy() -> impl Strategy<Value = String> {
    let var_name = "[a-z][a-z0-9_]*".prop_map(|s: String| s);
    let value = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy()
    ];
    
    (var_name, value).prop_map(|(name, val)| {
        format!("let {} = {};", name, val)
    })
}

/// Helper function to generate random if expressions
pub fn if_expr_strategy() -> impl Strategy<Value = String> {
    let condition = boolean_expr_strategy();
    let then_branch = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy()
    ];
    let else_branch = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy()
    ];
    
    (condition, then_branch, else_branch).prop_map(|(cond, then_val, else_val)| {
        format!("if {} then {} else {}", cond, then_val, else_val)
    })
}

/// Helper function to generate random record expressions
pub fn record_expr_strategy() -> impl Strategy<Value = String> {
    let field_name = "[a-z][a-z0-9_]*".prop_map(|s: String| s);
    let field_value = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy()
    ];
    
    prop::collection::vec((field_name, field_value), 1..4).prop_map(|fields| {
        let field_strs: Vec<String> = fields.into_iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect();
        format!("{{ {} }}", field_strs.join(", "))
    })
}

/// Helper function to generate random list expressions
pub fn list_expr_strategy() -> impl Strategy<Value = String> {
    let element = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy()
    ];
    
    prop::collection::vec(element, 0..5).prop_map(|elements| {
        format!("[{}]", elements.join(", "))
    })
}

/// Helper function to generate random function expressions
pub fn function_expr_strategy() -> impl Strategy<Value = String> {
    let param_name = "[a-z][a-z0-9_]*".prop_map(|s: String| s);
    let body = prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy(),
        arithmetic_expr_strategy()
    ];
    
    (param_name, body).prop_map(|(param, body)| {
        format!("\\{} -> {}", param, body)
    })
}

/// Helper function to generate random expressions
pub fn expr_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        integer_expr_strategy(),
        string_expr_strategy(),
        boolean_expr_strategy(),
        arithmetic_expr_strategy(),
        comparison_expr_strategy(),
        logical_expr_strategy(),
        if_expr_strategy(),
        record_expr_strategy(),
        list_expr_strategy(),
        function_expr_strategy()
    ]
}

/// Helper function to generate random programs
pub fn program_strategy() -> impl Strategy<Value = String> {
    prop::collection::vec(binding_expr_strategy(), 1..5).prop_map(|bindings| {
        bindings.join("\n")
    })
}

/// Helper function to check if an expression is well-formed
pub fn is_well_formed(expr: &str) -> bool {
    parse_expression(expr).is_ok()
}

/// Helper function to check if a program is well-formed
pub fn is_program_well_formed(program: &str) -> bool {
    parse_program(program).is_ok()
}

/// Helper function to check if an expression type checks
pub fn type_checks(expr: &str) -> bool {
    parse_expression(expr)
        .and_then(|expr| type_check_program(&parse_program(&format!("let x = {};", expr))?))
        .is_ok()
}

/// Helper function to check if an expression evaluates successfully
pub fn evaluates_successfully(expr: &str) -> bool {
    parse_expression(expr)
        .and_then(|expr| evaluate_expression(&expr))
        .is_ok()
} 