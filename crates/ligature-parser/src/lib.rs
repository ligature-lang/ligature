//! Parser for the Ligature language.
//!
//! This crate provides parsing functionality for Ligature source code,
//! converting text into an Abstract Syntax Tree (AST).

pub mod error;
pub mod grammar;
pub mod parser;

#[cfg(feature = "fuzzing")]
pub mod fuzzing;

pub use error::ParserError;
// Re-export commonly used types from ligature-ast
pub use ligature_ast::{
    AstError, AstResult, Declaration, ExportDeclaration, ExportItem, Expr, ExprKind, Import,
    InstanceDeclaration, Literal, MatchCase, Pattern, RecordField, RecordPatternField, Span, Type,
    TypeAlias, TypeClassDeclaration, TypeConstructor, TypeField, TypeKind, TypeVariant,
    ValueDeclaration,
};
pub use parser::Parser;

/// Parse a complete program from source text.
pub fn parse_program(source: &str) -> AstResult<ligature_ast::Program> {
    let mut parser = Parser::new();
    parser.parse_program(source)
}

/// Parse a complete module from source text.
pub fn parse_module(source: &str) -> AstResult<ligature_ast::Module> {
    let mut parser = Parser::new();
    parser.parse_module(source)
}

/// Parse a single expression from source text.
pub fn parse_expression(source: &str) -> AstResult<ligature_ast::Expr> {
    let mut parser = Parser::new();
    parser.parse_expression(source)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test basic literal parsing
    #[test]
    fn test_literal_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test integer literals
        let program = parser.parse_program("let x = 42;")?;
        assert_eq!(program.declarations.len(), 1);

        // Test float literals
        let program = parser.parse_program("let x = 3.14;")?;
        assert_eq!(program.declarations.len(), 1);

        // Test boolean literals
        let program = parser.parse_program("let x = true;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = false;")?;
        assert_eq!(program.declarations.len(), 1);

        // Test string literals
        let program = parser.parse_program("let x = \"hello\";")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test variable binding parsing
    #[test]
    fn test_variable_binding() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = 42;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let my_variable = 123;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 1; let y = 2;")?;
        assert_eq!(program.declarations.len(), 2);

        Ok(())
    }

    /// Test arithmetic expression parsing
    #[test]
    fn test_arithmetic_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test basic arithmetic
        let program = parser.parse_program("let x = 5 + 3;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 10 - 4;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 6 * 7;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 20 / 4;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 17 % 5;")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test comparison expression parsing
    #[test]
    fn test_comparison_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = 5 > 3;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 7 == 7;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 4 != 5;")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test logical expression parsing
    #[test]
    fn test_logical_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = true && false;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = true || false;")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test unary expression parsing
    #[test]
    fn test_unary_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        // ✅ FIXED: Unary operator parsing precedence issue resolved
        // The grammar is producing unary_operator instead of unary at the expression level
        // This needs to be fixed in the grammar or parser precedence handling

        // ✅ FIXED: Unary operator parsing now works correctly
        let result = parser.parse_expression("!true");
        assert!(
            result.is_ok(),
            "Unary operator parsing should now work correctly"
        );

        let result = parser.parse_expression("-5");
        assert!(
            result.is_ok(),
            "Unary operator parsing should now work correctly"
        );

        // Test more complex unary expressions
        let result = parser.parse_expression("--5");
        assert!(
            result.is_ok(),
            "Multiple unary operators should work correctly"
        );

        let result = parser.parse_expression("-5 + 3");
        assert!(
            result.is_ok(),
            "Unary operators with binary operators should work correctly"
        );

        Ok(())
    }

    /// Test function definition parsing
    #[test]
    fn test_function_definitions() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let add = \\x -> x + 1;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let double = \\x -> x * 2;")?;
        assert_eq!(program.declarations.len(), 1);

        let program =
            parser.parse_program("let add_one = \\x -> x + 1; let result = add_one(5);")?;
        assert_eq!(program.declarations.len(), 2);

        Ok(())
    }

    /// Test function application parsing
    #[test]
    fn test_function_application() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = f(5);")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = f(g(5));")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test pattern matching parsing
    #[test]
    fn test_pattern_matching() -> AstResult<()> {
        let mut parser = Parser::new();

        let program =
            parser.parse_program("let x = 5; let result = match x { _ => \"default\" };")?;
        assert_eq!(program.declarations.len(), 2);

        let program = parser.parse_program(
            "let x = 10; let result = match x { n when n > 0 => \"positive\", _ => \"zero\" };",
        )?;
        assert_eq!(program.declarations.len(), 2);

        Ok(())
    }

    /// Test complex expression parsing
    #[test]
    fn test_complex_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = (5 + 3) * 2;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = true && (false || true);")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test module parsing
    #[test]
    fn test_module_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        let module = parser.parse_module("let x = 42;")?;
        assert_eq!(module.name, "main");
        assert_eq!(module.declarations.len(), 1);

        let module = parser.parse_module("let x = 1; let y = 2;")?;
        assert_eq!(module.name, "main");
        assert_eq!(module.declarations.len(), 2);

        Ok(())
    }

    /// Test error handling
    #[test]
    fn test_error_handling() {
        let mut parser = Parser::new();

        // Test invalid syntax
        assert!(parser.parse_program("let x = ;").is_err());
        assert!(parser.parse_program("let = 5;").is_err());
        assert!(parser.parse_program("x +").is_err());
        assert!(parser.parse_program("let x = 5").is_err()); // Missing semicolon
    }

    /// Test whitespace handling
    #[test]
    fn test_whitespace_handling() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test with various whitespace patterns
        let program = parser.parse_program("let x = 42;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("  let  x  =  42  ;  ")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("\nlet\nx\n=\n42\n;")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test comment handling
    #[test]
    fn test_comment_handling() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("// This is a comment\nlet x = 42;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = 42; // End of line comment")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test nested expression parsing
    #[test]
    fn test_nested_expressions() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let x = ((((5 + 3) * 2) - 1) / 3);")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = f(g(h(5)));")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test string literal parsing
    #[test]
    fn test_string_literals() -> AstResult<()> {
        let mut parser = Parser::new();

        let program = parser.parse_program("let greeting = \"Hello, World!\";")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let empty = \"\";")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = \"Hello\" == \"Hello\";")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test precedence parsing
    #[test]
    fn test_precedence() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test operator precedence
        let program = parser.parse_program("let x = 2 + 3 * 4;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = (2 + 3) * 4;")?;
        assert_eq!(program.declarations.len(), 1);

        let program = parser.parse_program("let x = true && false || true;")?;
        assert_eq!(program.declarations.len(), 1);

        Ok(())
    }

    /// Test large program parsing
    #[test]
    fn test_large_program() -> AstResult<()> {
        let mut parser = Parser::new();

        // Create a larger program
        let mut source = String::new();
        for i in 0..1000 {
            source.push_str(&format!("let x{i} = {i};\n"));
        }

        let program = parser.parse_program(&source)?;
        assert_eq!(program.declarations.len(), 1000);

        Ok(())
    }

    /// Test performance
    #[test]
    fn test_performance() -> AstResult<()> {
        let mut parser = Parser::new();

        // Create a large program
        let mut source = String::new();
        for i in 0..100 {
            source.push_str(&format!("let x{} = {} + {} * {};\n", i, i, i + 1, i + 2));
        }

        let start = std::time::Instant::now();
        let program = parser.parse_program(&source)?;
        let duration = start.elapsed();

        assert_eq!(program.declarations.len(), 100);
        assert!(
            duration.as_millis() < 100,
            "Parsing took too long: {duration:?}",
        );

        Ok(())
    }

    /// Test refinement type parsing
    #[test]
    fn test_refinement_type_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test basic refinement type: Int where x > 0
        let source = "type PositiveInt = Int where x > 0;";
        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "PositiveInt");
            assert!(alias.type_.is_refinement());

            if let Some((base_type, predicate, _)) = alias.type_.as_refinement() {
                assert!(matches!(base_type.kind, TypeKind::Integer));
                // The predicate should be a binary operation x > 0
                assert!(matches!(predicate.kind, ExprKind::BinaryOp { .. }));
            } else {
                panic!("Expected refinement type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }

    /// Test constraint type parsing
    #[test]
    fn test_constraint_type_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test constraint type: String with regexp("^[^@]+@[^@]+\\.[^@]+$")
        let source = "type ValidEmail = String with regexp(\"^[^@]+@[^@]+\\.[^@]+$\");";

        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "ValidEmail");
            assert!(alias.type_.is_constraint_type());

            if let Some((base_type, constraints)) = alias.type_.as_constraint_type() {
                assert!(matches!(base_type.kind, TypeKind::String));
                assert_eq!(constraints.len(), 1);

                println!("Debug: Constraint type: {:?}", constraints[0]);

                if let ligature_ast::ty::Constraint::PatternConstraint { pattern, regex } =
                    &constraints[0]
                {
                    println!("Debug: Pattern: {pattern}, Regex: {regex}");
                    assert_eq!(pattern, "^[^@]+@[^@]+\\.[^@]+$");
                    assert!(regex);
                } else {
                    panic!("Expected pattern constraint, got: {:?}", constraints[0]);
                }
            } else {
                panic!("Expected constraint type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }

    /// Test range constraint parsing
    #[test]
    fn test_range_constraint_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test range constraint: Int with >= 0
        let source = "type ValidAge = Int with >= 0;";
        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "ValidAge");
            assert!(alias.type_.is_constraint_type());

            if let Some((base_type, constraints)) = alias.type_.as_constraint_type() {
                assert!(matches!(base_type.kind, TypeKind::Integer));
                assert_eq!(constraints.len(), 1);

                // Check constraint (>= 0)
                if let ligature_ast::ty::Constraint::RangeConstraint { min, max, .. } =
                    &constraints[0]
                {
                    assert!(min.is_some()); // >= 0 means min = 0
                    assert!(max.is_none());
                } else {
                    panic!("Expected range constraint");
                }
            } else {
                panic!("Expected constraint type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }

    /// Test custom constraint parsing
    #[test]
    fn test_custom_constraint_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test custom constraint: String with isValidEmail(x)
        let source = "type ValidEmail = String with isValidEmail(x);";
        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "ValidEmail");
            assert!(alias.type_.is_constraint_type());

            if let Some((base_type, constraints)) = alias.type_.as_constraint_type() {
                assert!(matches!(base_type.kind, TypeKind::String));
                assert_eq!(constraints.len(), 1);

                if let ligature_ast::ty::Constraint::CustomConstraint {
                    function,
                    arguments,
                } = &constraints[0]
                {
                    assert_eq!(function, "isValidEmail");
                    assert_eq!(arguments.len(), 1);
                } else {
                    panic!("Expected custom constraint");
                }
            } else {
                panic!("Expected constraint type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }

    /// Test complex refinement type parsing
    #[test]
    fn test_complex_refinement_type_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test complex refinement type with record: { name: String, age: Int } where isValidUser x
        let source = "type ValidUser = { name: String, age: Int } where isValidUser x;";
        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "ValidUser");
            assert!(alias.type_.is_refinement());

            if let Some((base_type, predicate, _)) = alias.type_.as_refinement() {
                assert!(matches!(base_type.kind, TypeKind::Record { .. }));
                // The predicate should be a function application isValidUser x
                assert!(matches!(predicate.kind, ExprKind::Application { .. }));
            } else {
                panic!("Expected refinement type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }

    /// Test multiple constraints parsing
    #[test]
    fn test_multiple_constraints_parsing() -> AstResult<()> {
        let mut parser = Parser::new();

        // Test multiple constraints: String with regexp("^[A-Za-z]+$") with isValidEmail(x)
        let source =
            "type NonEmptyAlpha = String with regexp(\"^[A-Za-z]+$\") with isValidEmail(x);";
        let program = parser.parse_program(source)?;
        assert_eq!(program.declarations.len(), 1);

        if let Some(alias) = program.declarations[0].as_type_alias() {
            assert_eq!(alias.name, "NonEmptyAlpha");
            assert!(alias.type_.is_constraint_type());

            if let Some((base_type, constraints)) = alias.type_.as_constraint_type() {
                assert!(matches!(base_type.kind, TypeKind::String));
                assert_eq!(constraints.len(), 2);

                // First constraint should be pattern constraint
                assert!(matches!(
                    constraints[0],
                    ligature_ast::ty::Constraint::PatternConstraint { .. }
                ));

                // Second constraint should be custom constraint
                assert!(matches!(
                    constraints[1],
                    ligature_ast::ty::Constraint::CustomConstraint { .. }
                ));
            } else {
                panic!("Expected constraint type");
            }
        } else {
            panic!("Expected type alias declaration");
        }

        Ok(())
    }
}
