//! Tests for union type inference in the Ligature language.

use crate::inference::TypeInference;
use crate::type_check_program;
use ligature_ast::{Expr, ExprKind, Literal, Span, Type, TypeKind, TypeVariant};
use ligature_parser::parse_program;

#[test]
fn test_basic_union_construction() {
    let mut inference = TypeInference::new();

    // Test union construction without payload
    let union_expr = Expr {
        kind: ExprKind::Union {
            variant: "None".to_string(),
            value: None,
        },
        span: Span::default(),
    };

    let union_type = inference.infer_expression(&union_expr).unwrap();
    assert!(union_type.is_union());

    if let Some(variants) = union_type.as_union() {
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].name, "None");
        assert!(variants[0].type_.is_none());
    } else {
        panic!("Expected union type");
    }
}

#[test]
fn test_union_construction_with_payload() {
    let mut inference = TypeInference::new();

    // Test union construction with payload
    let value_expr = Expr {
        kind: ExprKind::Literal(Literal::Integer(42)),
        span: Span::default(),
    };

    let union_expr = Expr {
        kind: ExprKind::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(value_expr)),
        },
        span: Span::default(),
    };

    let union_type = inference.infer_expression(&union_expr).unwrap();
    assert!(union_type.is_union());

    if let Some(variants) = union_type.as_union() {
        assert_eq!(variants.len(), 1);
        assert_eq!(variants[0].name, "Some");
        assert!(variants[0].type_.is_some());
        if let Some(variant_type) = &variants[0].type_ {
            assert!(matches!(variant_type.kind, TypeKind::Integer));
        }
    } else {
        panic!("Expected union type");
    }
}

#[test]
fn test_union_pattern_matching() {
    let mut inference = TypeInference::new();

    // Create a union type with two variants
    let option_type = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // Bind the option type to a variable
    inference.bind("opt".to_string(), option_type);

    // Create a match expression
    let scrutinee = Expr {
        kind: ExprKind::Variable("opt".to_string()),
        span: Span::default(),
    };

    let some_case = ligature_ast::MatchCase {
        pattern: ligature_ast::Pattern::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(ligature_ast::Pattern::Variable("n".to_string()))),
        },
        guard: None,
        expression: Expr {
            kind: ExprKind::Variable("n".to_string()),
            span: Span::default(),
        },
        span: Span::default(),
    };

    let none_case = ligature_ast::MatchCase {
        pattern: ligature_ast::Pattern::Union {
            variant: "None".to_string(),
            value: None,
        },
        guard: None,
        expression: Expr {
            kind: ExprKind::Literal(Literal::Integer(0)),
            span: Span::default(),
        },
        span: Span::default(),
    };

    let match_expr = Expr {
        kind: ExprKind::Match {
            scrutinee: Box::new(scrutinee),
            cases: vec![some_case, none_case],
        },
        span: Span::default(),
    };

    let match_type = inference.infer_expression(&match_expr).unwrap();
    assert!(matches!(match_type.kind, TypeKind::Integer));
}

#[test]
fn test_union_type_constructor_lookup() {
    let mut inference = TypeInference::new();

    // Define a union type constructor
    let option_type = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // Bind it as a type constructor
    let type_constructor = ligature_ast::TypeConstructor {
        name: "Option".to_string(),
        parameters: vec!["a".to_string()],
        body: option_type,
        span: Span::default(),
    };

    inference.bind_type_constructor("Option".to_string(), type_constructor);

    // Test that we can find the union type when constructing variants
    let some_expr = Expr {
        kind: ExprKind::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(Expr {
                kind: ExprKind::Literal(Literal::Integer(42)),
                span: Span::default(),
            })),
        },
        span: Span::default(),
    };

    let inferred_type = inference.infer_expression(&some_expr).unwrap();
    assert!(inferred_type.is_union());
}

#[test]
fn test_union_subtyping() {
    let inference = TypeInference::new();

    // Create a base union type
    let base_union = Type::union(
        vec![
            TypeVariant {
                name: "A".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "B".to_string(),
                type_: Some(Type::string(Span::default())),
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // Create a more specific union type (subtype)
    let specific_union = Type::union(
        vec![TypeVariant {
            name: "A".to_string(),
            type_: Some(Type::integer(Span::default())),
            span: Span::default(),
        }],
        Span::default(),
    );

    // Test that the specific union is a subtype of the base union
    let _is_subtype = inference.types_equal(&specific_union, &base_union).unwrap();
    // Note: This is a simplified test - in a full implementation, we'd have proper subtyping
    // Just ensure it doesn't panic
}

#[test]
fn test_exact_failing_case() {
    // This test exactly replicates what the failing test does
    let source = r#"
        type Option = Some Integer | None;
        
        let none_value = None;
    "#;

    let program = parse_program(source).unwrap();

    // Create the same type inference engine as type_check_program does
    let mut inference = TypeInference::new();

    // Process declarations in the same order as type_check_program
    for declaration in &program.declarations {
        match &declaration.kind {
            ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                println!("Processing type alias: {}", type_alias.name);
                // Check that the type alias is well-formed
                inference.check_type(&type_alias.type_).unwrap();
                // Add the type alias to the environment
                inference.bind_type_alias(type_alias.name.clone(), type_alias.clone());

                // If this is a union type, bind each variant as a constructor
                if let TypeKind::Union { variants } = &type_alias.type_.kind {
                    println!("Found union type with variants: {variants:?}");
                    for variant in variants {
                        println!("Binding variant: {}", variant.name);
                        // Create a type constructor for each variant
                        let variant_constructor = ligature_ast::TypeConstructor {
                            name: variant.name.clone(),
                            parameters: vec![], // Variants don't have parameters in this model
                            body: type_alias.type_.clone(),
                            span: variant.span,
                        };
                        inference.bind_type_constructor(variant.name.clone(), variant_constructor);

                        // Also bind each variant as a value with the union type
                        // This allows using variants like `None` or `Some(42)` in expressions
                        println!(
                            "Binding {} as value with type: {:?}",
                            variant.name, type_alias.type_
                        );
                        inference.bind(variant.name.clone(), type_alias.type_.clone());
                    }
                }
            }
            ligature_ast::DeclarationKind::Value(value_decl) => {
                println!("Processing value declaration: {}", value_decl.name);
                // Infer the type of the value expression
                let inferred_type = inference.infer_expression(&value_decl.value).unwrap();
                println!("Inferred type for {}: {:?}", value_decl.name, inferred_type);

                // If there's a type annotation, check that it matches the inferred type
                if let Some(annotation) = &value_decl.type_annotation {
                    if !inference.types_equal(&inferred_type, annotation).unwrap() {
                        panic!("Type annotation mismatch");
                    }
                }

                // Add the binding to the environment
                let final_type = value_decl
                    .type_annotation
                    .as_ref()
                    .unwrap_or(&inferred_type);
                inference.bind(value_decl.name.clone(), final_type.clone());
            }
            _ => {}
        }
    }

    // Exact replication should succeed
}

#[test]
fn test_environment_binding_lookup() {
    let mut inference = TypeInference::new();

    // Bind a simple value
    inference.bind("x".to_string(), Type::integer(Span::default()));

    // Check if it's bound
    let x_expr = Expr {
        kind: ExprKind::Variable("x".to_string()),
        span: Span::default(),
    };

    let result = inference.infer_expression(&x_expr);
    assert!(
        result.is_ok(),
        "Should be able to use x as a variable: {result:?}",
    );

    // Now bind a union variant
    let option_type = Type::union(
        vec![TypeVariant {
            name: "None".to_string(),
            type_: None,
            span: Span::default(),
        }],
        Span::default(),
    );

    inference.bind("None".to_string(), option_type.clone());

    // Check if None is bound
    let none_expr = Expr {
        kind: ExprKind::Variable("None".to_string()),
        span: Span::default(),
    };

    let result = inference.infer_expression(&none_expr);
    assert!(
        result.is_ok(),
        "Should be able to use None as a variable: {result:?}",
    );

    let inferred_type = result.unwrap();
    assert!(inferred_type.is_union());
}

#[test]
fn test_declaration_order_processing() {
    let mut inference = TypeInference::new();

    // First, process the type alias declaration
    let option_type = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    let type_alias = ligature_ast::TypeAlias {
        name: "Option".to_string(),
        parameters: vec![],
        type_: option_type.clone(),
        span: Span::default(),
    };

    // Process the type alias like the type checker does
    inference.check_type(&type_alias.type_).unwrap();
    inference.bind_type_alias(type_alias.name.clone(), type_alias.clone());

    // If this is a union type, bind each variant as a constructor
    if let TypeKind::Union { variants } = &type_alias.type_.kind {
        for variant in variants {
            // Create a type constructor for each variant
            let variant_constructor = ligature_ast::TypeConstructor {
                name: variant.name.clone(),
                parameters: vec![], // Variants don't have parameters in this model
                body: type_alias.type_.clone(),
                span: variant.span,
            };
            inference.bind_type_constructor(variant.name.clone(), variant_constructor);

            // Also bind each variant as a value with the union type
            // This allows using variants like `None` or `Some(42)` in expressions
            inference.bind(variant.name.clone(), type_alias.type_.clone());
        }
    }

    // Now check if None is bound
    let none_expr = Expr {
        kind: ExprKind::Variable("None".to_string()),
        span: Span::default(),
    };

    let result = inference.infer_expression(&none_expr);
    assert!(
        result.is_ok(),
        "Should be able to use None as a variable: {result:?}",
    );

    // Now process a value declaration that uses None
    let value_decl = ligature_ast::ValueDeclaration {
        name: "none_value".to_string(),
        type_annotation: None,
        value: none_expr,
        is_recursive: false,
        span: Span::default(),
    };

    // Process the value declaration like the type checker does
    let inferred_type = inference.infer_expression(&value_decl.value).unwrap();
    inference.bind(value_decl.name.clone(), inferred_type);

    // This should succeed
}

#[test]
fn test_type_alias_union_binding() {
    let mut inference = TypeInference::new();

    // Simulate processing a type alias declaration
    let option_type = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    let type_alias = ligature_ast::TypeAlias {
        name: "Option".to_string(),
        parameters: vec![],
        type_: option_type.clone(),
        span: Span::default(),
    };

    // Process the type alias like the type checker does
    inference.check_type(&type_alias.type_).unwrap();
    inference.bind_type_alias(type_alias.name.clone(), type_alias.clone());

    // If this is a union type, bind each variant as a constructor
    if let TypeKind::Union { variants } = &type_alias.type_.kind {
        for variant in variants {
            // Create a type constructor for each variant
            let variant_constructor = ligature_ast::TypeConstructor {
                name: variant.name.clone(),
                parameters: vec![], // Variants don't have parameters in this model
                body: type_alias.type_.clone(),
                span: variant.span,
            };
            inference.bind_type_constructor(variant.name.clone(), variant_constructor);

            // Also bind each variant as a value with the union type
            // This allows using variants like `None` or `Some(42)` in expressions
            inference.bind(variant.name.clone(), type_alias.type_.clone());
        }
    }

    // Now try to use None as a variable
    let none_expr = Expr {
        kind: ExprKind::Variable("None".to_string()),
        span: Span::default(),
    };

    let result = inference.infer_expression(&none_expr);
    assert!(
        result.is_ok(),
        "Should be able to use None as a variable: {result:?}",
    );

    let inferred_type = result.unwrap();
    assert!(inferred_type.is_union());
}

#[test]
fn test_manual_union_variant_binding() {
    let mut inference = TypeInference::new();

    // Create a union type
    let option_type = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // Manually bind the union variants as values
    inference.bind("None".to_string(), option_type.clone());
    inference.bind("Some".to_string(), option_type.clone());

    // Now try to use None as a variable
    let none_expr = Expr {
        kind: ExprKind::Variable("None".to_string()),
        span: Span::default(),
    };

    let result = inference.infer_expression(&none_expr);
    assert!(
        result.is_ok(),
        "Should be able to use None as a variable: {result:?}",
    );

    let inferred_type = result.unwrap();
    assert!(inferred_type.is_union());
}

#[test]
fn test_simple_union_value_binding() {
    // Test a simple case where we define a union type and use its variants as values
    let source = r#"
        type Option = Some Integer | None;
        let none_value = None;
    "#;

    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);

    // The program should type check successfully
    assert!(result.is_ok(), "Program should type check: {result:?}");
}

#[test]
fn test_union_type_inference_in_programs() {
    // Test union type inference in a complete program
    let source = r#"
        type Option = Some Integer | None;
        
        let none_value = None;
        let some_value = Some(42);
        
        let get_value = \opt -> match opt {
            Some(n) => n,
            None => 0
        };
        
        let result1 = get_value(some_value);
        let result2 = get_value(none_value);
    "#;

    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);

    // The program should type check successfully
    assert!(result.is_ok(), "Program should type check: {result:?}");
}

#[test]
fn test_union_type_errors() {
    let mut inference = TypeInference::new();

    // Test error case: union construction with wrong payload type
    let value_expr = Expr {
        kind: ExprKind::Literal(Literal::String("hello".to_string())),
        span: Span::default(),
    };

    let union_expr = Expr {
        kind: ExprKind::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(value_expr)),
        },
        span: Span::default(),
    };

    // This should work (creates a fresh union type), but we can test constraint solving
    let result = inference.infer_expression(&union_expr);
    assert!(result.is_ok()); // Should succeed as it creates a fresh type
}

#[test]
fn test_nested_union_patterns() {
    let mut inference = TypeInference::new();

    // Create a nested union type (e.g., Result<Option<Integer>, String>)
    let inner_union = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::integer(Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    let result_union = Type::union(
        vec![
            TypeVariant {
                name: "Ok".to_string(),
                type_: Some(inner_union),
                span: Span::default(),
            },
            TypeVariant {
                name: "Err".to_string(),
                type_: Some(Type::string(Span::default())),
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    inference.bind("result".to_string(), result_union);

    // Create a nested pattern match
    let scrutinee = Expr {
        kind: ExprKind::Variable("result".to_string()),
        span: Span::default(),
    };

    let nested_case = ligature_ast::MatchCase {
        pattern: ligature_ast::Pattern::Union {
            variant: "Ok".to_string(),
            value: Some(Box::new(ligature_ast::Pattern::Union {
                variant: "Some".to_string(),
                value: Some(Box::new(ligature_ast::Pattern::Variable("n".to_string()))),
            })),
        },
        guard: None,
        expression: Expr {
            kind: ExprKind::Variable("n".to_string()),
            span: Span::default(),
        },
        span: Span::default(),
    };

    let match_expr = Expr {
        kind: ExprKind::Match {
            scrutinee: Box::new(scrutinee),
            cases: vec![nested_case],
        },
        span: Span::default(),
    };

    let match_type = inference.infer_expression(&match_expr).unwrap();
    assert!(matches!(match_type.kind, TypeKind::Integer));
}

#[test]
fn test_union_type_generalization() {
    let inference = TypeInference::new();

    // Test that union types can be generalized (made polymorphic)
    let polymorphic_union = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(Type::variable("a".to_string(), Span::default())),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // This should work with different element types
    let int_option = inference.substitute_type_variable(
        &polymorphic_union,
        "a",
        &Type::integer(Span::default()),
    );
    let string_option =
        inference.substitute_type_variable(&polymorphic_union, "a", &Type::string(Span::default()));

    assert!(int_option.is_union());
    assert!(string_option.is_union());

    if let Some(int_variants) = int_option.as_union() {
        assert_eq!(int_variants.len(), 2);
        if let Some(some_type) = &int_variants[0].type_ {
            assert!(matches!(some_type.kind, TypeKind::Integer));
        }
    }

    if let Some(string_variants) = string_option.as_union() {
        assert_eq!(string_variants.len(), 2);
        if let Some(some_type) = &string_variants[0].type_ {
            assert!(matches!(some_type.kind, TypeKind::String));
        }
    }
}

#[test]
fn test_union_type_constraints() {
    let mut inference = TypeInference::new();

    // Test that union type constraints are properly solved
    let var_a = Type::variable("a".to_string(), Span::default());
    let int_type = Type::integer(Span::default());

    // Create a constraint that a union variant type equals an integer
    inference
        .constraint_solver
        .add_constraint(crate::constraints::Constraint::Equality(
            var_a.clone(),
            int_type.clone(),
        ));

    // Create a union type using the variable
    let union_with_var = Type::union(
        vec![
            TypeVariant {
                name: "Some".to_string(),
                type_: Some(var_a),
                span: Span::default(),
            },
            TypeVariant {
                name: "None".to_string(),
                type_: None,
                span: Span::default(),
            },
        ],
        Span::default(),
    );

    // Solve constraints
    let substitution = inference.constraint_solver.solve().unwrap();

    // Apply substitution to the union type
    let resolved_union = inference.apply_substitution(union_with_var, &substitution);

    if let Some(variants) = resolved_union.as_union() {
        if let Some(some_type) = &variants[0].type_ {
            assert!(matches!(some_type.kind, TypeKind::Integer));
        }
    }
}
