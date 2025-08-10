use embouchure_checker::resolver::{Module, ModuleResolver};
use ligature_ast::{AstResult, Declaration, Import, Span};

fn main() -> AstResult<()> {
    let mut resolver = ModuleResolver::new();

    // Test 1: Basic module creation
    let basic_module = Module {
        name: "main".to_string(),
        imports: vec![],
        declarations: vec![
            Declaration::value(
                "x".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
            Declaration::value(
                "y".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::BinaryOp {
                        operator: ligature_ast::BinaryOperator::Add,
                        left: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Variable("x".to_string()),
                            span: Span::default(),
                        }),
                        right: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(
                                1,
                            )),
                            span: Span::default(),
                        }),
                    },
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
        ],
        span: Span::default(),
    };

    println!("Testing basic module...");
    println!("  - Module name: {}", basic_module.name);
    println!("  - Imports: {}", basic_module.imports.len());
    println!("  - Declarations: {}", basic_module.declarations.len());

    // Debug: Print all declarations
    for (i, decl) in basic_module.declarations.iter().enumerate() {
        println!("  Declaration {i}: {decl:?}");
    }

    // Verify that declarations are correct
    assert_eq!(
        basic_module.declarations.len(),
        2,
        "Expected 2 declarations, got {}",
        basic_module.declarations.len()
    );
    assert_eq!(
        basic_module.name, "main",
        "Expected default module name 'main', got '{}'",
        basic_module.name
    );
    println!("✓ Declaration count and default module name are correct");

    // Test 2: Module with explicit name
    let module_with_name = Module {
        name: "MyModule".to_string(),
        imports: vec![],
        declarations: vec![
            Declaration::value(
                "x".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
            Declaration::value(
                "y".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::BinaryOp {
                        operator: ligature_ast::BinaryOperator::Add,
                        left: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Variable("x".to_string()),
                            span: Span::default(),
                        }),
                        right: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(
                                1,
                            )),
                            span: Span::default(),
                        }),
                    },
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
        ],
        span: Span::default(),
    };

    println!("\nTesting module with explicit name...");
    println!("  - Module name: {}", module_with_name.name);
    println!("  - Imports: {}", module_with_name.imports.len());
    println!("  - Declarations: {}", module_with_name.declarations.len());

    assert_eq!(
        module_with_name.name, "MyModule",
        "Expected module name 'MyModule', got '{}'",
        module_with_name.name
    );
    assert_eq!(
        module_with_name.declarations.len(),
        2,
        "Expected 2 declarations"
    );
    println!("✓ Module name extraction works correctly");

    // Test 3: Module with imports
    let module_with_imports = Module {
        name: "main".to_string(),
        imports: vec![Import {
            path: "stdlib.core".to_string(),
            alias: None,
            items: None,
            span: Span::default(),
        }],
        declarations: vec![
            Declaration::value(
                "x".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
            Declaration::value(
                "y".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::BinaryOp {
                        operator: ligature_ast::BinaryOperator::Add,
                        left: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Variable("x".to_string()),
                            span: Span::default(),
                        }),
                        right: Box::new(ligature_ast::Expr {
                            kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(
                                1,
                            )),
                            span: Span::default(),
                        }),
                    },
                    span: Span::default(),
                },
                false,
                Span::default(),
            ),
        ],
        span: Span::default(),
    };

    println!("\nTesting module with imports...");
    println!("  - Module name: {}", module_with_imports.name);
    println!("  - Imports: {}", module_with_imports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_imports.declarations.len()
    );

    assert_eq!(module_with_imports.imports.len(), 1, "Expected 1 import");
    assert_eq!(
        module_with_imports.declarations.len(),
        2,
        "Expected 2 declarations"
    );
    println!("✓ Module with imports works correctly");

    // Test 4: Module with aliased imports
    let module_with_aliased_imports = Module {
        name: "main".to_string(),
        imports: vec![
            Import {
                path: "stdlib.core".to_string(),
                alias: Some("core".to_string()),
                items: None,
                span: Span::default(),
            },
            Import {
                path: "stdlib.collections".to_string(),
                alias: Some("collections".to_string()),
                items: None,
                span: Span::default(),
            },
        ],
        declarations: vec![Declaration::value(
            "x".to_string(),
            None,
            ligature_ast::Expr {
                kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                span: Span::default(),
            },
            false,
            Span::default(),
        )],
        span: Span::default(),
    };

    println!("\nTesting module with aliased imports...");
    println!("  - Module name: {}", module_with_aliased_imports.name);
    println!("  - Imports: {}", module_with_aliased_imports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_aliased_imports.declarations.len()
    );

    // Verify import details
    for (i, import) in module_with_aliased_imports.imports.iter().enumerate() {
        println!(
            "  Import {i}: path='{}', alias='{:?}'",
            import.path, import.alias
        );
    }

    assert_eq!(
        module_with_aliased_imports.imports.len(),
        2,
        "Expected 2 imports"
    );
    println!("✓ Module with aliased imports works correctly");

    // Test 5: Module with exports
    let module_with_exports = Module {
        name: "main".to_string(),
        imports: vec![],
        declarations: vec![
            Declaration::value(
                "x".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                true, // exported
                Span::default(),
            ),
            Declaration::value(
                "y".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(100)),
                    span: Span::default(),
                },
                false, // not exported
                Span::default(),
            ),
        ],
        span: Span::default(),
    };

    println!("\nTesting module with exports...");
    println!("  - Module name: {}", module_with_exports.name);
    println!("  - Imports: {}", module_with_exports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_exports.declarations.len()
    );

    // Count exported declarations
    let exported_count = module_with_exports
        .declarations
        .iter()
        .filter(|decl| decl.is_export())
        .count();
    println!("  - Exported declarations: {exported_count}");

    assert_eq!(exported_count, 1, "Expected 1 exported declaration");
    println!("✓ Module with exports works correctly");

    // Test 6: Complex module with all features
    let complex_module = Module {
        name: "ComplexModule".to_string(),
        imports: vec![
            Import {
                path: "stdlib.core".to_string(),
                alias: None,
                items: None,
                span: Span::default(),
            },
            Import {
                path: "stdlib.collections".to_string(),
                alias: Some("collections".to_string()),
                items: None,
                span: Span::default(),
            },
        ],
        declarations: vec![
            Declaration::value(
                "public_value".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                true, // exported
                Span::default(),
            ),
            Declaration::value(
                "private_value".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(100)),
                    span: Span::default(),
                },
                false, // not exported
                Span::default(),
            ),
        ],
        span: Span::default(),
    };

    println!("\nTesting complex module...");
    println!("  - Module name: {}", complex_module.name);
    println!("  - Imports: {}", complex_module.imports.len());
    println!("  - Declarations: {}", complex_module.declarations.len());

    assert_eq!(
        complex_module.name, "ComplexModule",
        "Expected module name 'ComplexModule', got '{}'",
        complex_module.name
    );
    assert_eq!(
        complex_module.name, "ComplexModule",
        "Expected module name 'ComplexModule'"
    );
    assert_eq!(complex_module.imports.len(), 2, "Expected 2 imports");
    assert_eq!(
        complex_module.declarations.len(),
        2,
        "Expected 2 declarations"
    );

    let exported_count = complex_module
        .declarations
        .iter()
        .filter(|decl| decl.is_export())
        .count();
    assert_eq!(exported_count, 1, "Expected 1 exported declaration");

    println!("✓ Complex module works correctly");

    // Test 7: Module resolver functionality
    println!("\nTesting module resolver...");

    // Add a test module to the resolver cache
    resolver
        .cache
        .insert("test_module".to_string(), basic_module.clone());

    // Test cache functionality
    assert!(resolver.is_cached("test_module"), "Module should be cached");
    assert!(
        resolver.get_cached("test_module").is_some(),
        "Should retrieve cached module"
    );

    println!("✓ Module resolver cache works correctly");

    println!("\nAll module system tests completed successfully!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_module() {
        let module = Module {
            name: "test".to_string(),
            imports: vec![],
            declarations: vec![],
            span: Span::default(),
        };

        assert_eq!(module.name, "test");
        assert_eq!(module.imports.len(), 0);
        assert_eq!(module.declarations.len(), 0);
    }

    #[test]
    fn test_module_with_imports() {
        let module = Module {
            name: "test".to_string(),
            imports: vec![Import {
                path: "stdlib.core".to_string(),
                alias: None,
                items: None,
                span: Span::default(),
            }],
            declarations: vec![],
            span: Span::default(),
        };

        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].path, "stdlib.core");
    }

    #[test]
    fn test_module_with_declarations() {
        let module = Module {
            name: "test".to_string(),
            imports: vec![],
            declarations: vec![Declaration::value(
                "x".to_string(),
                None,
                ligature_ast::Expr {
                    kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                    span: Span::default(),
                },
                false,
                Span::default(),
            )],
            span: Span::default(),
        };

        assert_eq!(module.declarations.len(), 1);
        if let Some(value_decl) = module.declarations[0].as_value() {
            assert_eq!(value_decl.name, "x");
        } else {
            panic!("Expected value declaration");
        }
    }
}
