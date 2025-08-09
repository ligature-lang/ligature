//! Type checker for the Ligature language.
//!
//! This crate provides type checking, type inference, and type system
//! functionality for the Ligature language.

pub mod checker;
pub mod constraints;
pub mod environment;
pub mod error;
pub mod resolver;

use std::path::PathBuf;

use ligature_ast::Program;
use ligature_error::StandardResult;

/// Type check a complete program.
pub fn type_check_program(program: &Program) -> StandardResult<()> {
    let mut checker = checker::TypeChecker::new();
    checker.check_program(program)
}

/// Type check a program with custom search and register paths.
pub fn type_check_program_with_paths(
    program: &Program,
    search_paths: &[PathBuf],
    register_paths: &[PathBuf],
) -> StandardResult<()> {
    let mut checker =
        checker::TypeChecker::with_paths(search_paths.to_vec(), register_paths.to_vec());
    checker.check_program(program)
}

/// Type check a complete module.
pub fn type_check_module(module: &crate::resolver::Module) -> StandardResult<()> {
    let mut checker = checker::TypeChecker::new();
    checker.check_module(module)
}

/// Infer the type of an expression.
pub fn infer_expression(expr: &ligature_ast::Expr) -> StandardResult<ligature_ast::Type> {
    let mut checker = checker::TypeChecker::new();
    checker.infer_expression(expr)
}

// Re-export the main TypeChecker for convenience
pub use checker::TypeChecker;

#[cfg(test)]
mod tests {
    use ligature_ast::{Expr, ExprKind, Literal, Program, Span, Type, TypeKind};
    use ligature_parser::parse_program;

    use super::*;

    #[test]
    fn test_basic_type_checking() {
        // Test that the embouchure-checker crate can type check a simple program
        let source = "let x = 42;";
        let program = parse_program(source).unwrap();

        let result = type_check_program(&program);
        assert!(result.is_ok(), "Type checking failed: {result:?}");
    }

    #[test]
    fn test_type_inference() {
        // Test that type inference works
        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };

        let result = infer_expression(&expr);
        assert!(result.is_ok(), "Type inference failed: {result:?}");

        let inferred_type = result.unwrap();
        assert!(matches!(inferred_type.kind, TypeKind::Integer));
    }

    #[test]
    fn test_type_checker_creation() {
        // Test that TypeChecker can be created
        let checker = TypeChecker::new();
        assert!(checker.register_paths().is_empty());
    }
}
