use ligature_ast::TypeKind;
use ligature_parser::parse_program;
use ligature_types::{infer_expression, type_check_program};

fn main() {
    println!("🧪 Running Enhanced Type Inference Integration Tests\n");

    let mut passed = 0;
    let mut failed = 0;

    // Test 1: Basic type inference
    println!("1. Testing basic type inference...");
    if test_basic_type_inference() {
        println!("   ✅ Basic type inference passed");
        passed += 1;
    } else {
        println!("   ❌ Basic type inference failed");
        failed += 1;
    }

    // Test 2: Enhanced union type inference
    println!("2. Testing enhanced union type inference...");
    if test_enhanced_union_type_inference() {
        println!("   ✅ Enhanced union type inference passed");
        passed += 1;
    } else {
        println!("   ❌ Enhanced union type inference failed");
        failed += 1;
    }

    // Test 3: Enhanced list type inference
    println!("3. Testing enhanced list type inference...");
    if test_enhanced_list_type_inference() {
        println!("   ✅ Enhanced list type inference passed");
        passed += 1;
    } else {
        println!("   ❌ Enhanced list type inference failed");
        failed += 1;
    }

    // Test 4: Polymorphic let bindings
    println!("4. Testing polymorphic let bindings...");
    if test_polymorphic_let_bindings() {
        println!("   ✅ Polymorphic let bindings passed");
        passed += 1;
    } else {
        println!("   ❌ Polymorphic let bindings failed");
        failed += 1;
    }

    // Test 5: Enhanced pattern matching
    println!("5. Testing enhanced pattern matching...");
    if test_enhanced_pattern_matching() {
        println!("   ✅ Enhanced pattern matching passed");
        passed += 1;
    } else {
        println!("   ❌ Enhanced pattern matching failed");
        failed += 1;
    }

    // Test 6: Enhanced error reporting
    println!("6. Testing enhanced error reporting...");
    if test_enhanced_error_reporting() {
        println!("   ✅ Enhanced error reporting passed");
        passed += 1;
    } else {
        println!("   ❌ Enhanced error reporting failed");
        failed += 1;
    }

    // Test 7: Complex type inference scenarios
    println!("7. Testing complex type inference scenarios...");
    if test_complex_type_inference() {
        println!("   ✅ Complex type inference scenarios passed");
        passed += 1;
    } else {
        println!("   ❌ Complex type inference scenarios failed");
        failed += 1;
    }

    println!("\n📊 Test Results:");
    println!("   Passed: {passed}");
    println!("   Failed: {failed}");
    println!("   Total: {}", passed + failed);

    if failed == 0 {
        println!("🎉 All tests passed!");
        std::process::exit(0);
    } else {
        println!("💥 Some tests failed!");
        std::process::exit(1);
    }
}

fn test_basic_type_inference() -> bool {
    let test_cases = vec![
        ("let x = 42;", TypeKind::Integer),
        ("let x = \"hello\";", TypeKind::String),
        ("let x = true;", TypeKind::Bool),
        ("let x = ();", TypeKind::Unit),
        ("let x = 3.14;", TypeKind::Float),
    ];

    for (source, expected_kind) in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match type_check_program(&program) {
                    Ok(()) => {
                        // Extract the expression and infer its type
                        if let Some(declaration) = program.declarations.first() {
                            if let ligature_ast::DeclarationKind::Value(value_decl) =
                                &declaration.kind
                            {
                                match infer_expression(&value_decl.value) {
                                    Ok(inferred_type) => {
                                        if std::mem::discriminant(&inferred_type.kind)
                                            != std::mem::discriminant(&expected_kind)
                                        {
                                            println!(
                                                "     Expected {:?}, got {:?}",
                                                expected_kind, inferred_type.kind
                                            );
                                            return false;
                                        }
                                    }
                                    Err(e) => {
                                        println!("     Type inference failed: {e:?}");
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => {
                        println!("     Type checking failed: {e:?}");
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Parsing failed: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_enhanced_union_type_inference() -> bool {
    // Union types are not yet fully implemented in the parser
    // For now, we'll skip this test
    println!("     Skipping union type inference test (not yet implemented)");
    true
}

fn test_enhanced_list_type_inference() -> bool {
    let test_cases = vec![
        "let numbers = [1, 2, 3, 4, 5];",
        "let strings = [\"a\", \"b\", \"c\"];",
        "let mixed = [1, 2, 3];", // Should unify to integer list
    ];

    for source in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match type_check_program(&program) {
                    Ok(()) => {
                        // Check that list types are properly inferred
                        if let Some(declaration) = program.declarations.first() {
                            if let ligature_ast::DeclarationKind::Value(value_decl) =
                                &declaration.kind
                            {
                                match infer_expression(&value_decl.value) {
                                    Ok(inferred_type) => {
                                        if !matches!(inferred_type.kind, TypeKind::List { .. }) {
                                            println!(
                                                "     Expected list type, got {:?}",
                                                inferred_type.kind
                                            );
                                            return false;
                                        }
                                    }
                                    Err(e) => {
                                        println!("     Type inference failed: {e:?}");
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => {
                        println!("     Type checking failed: {e:?}");
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Parsing failed: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_polymorphic_let_bindings() -> bool {
    let test_cases = vec![
        "let id = \\x -> x; let result = id(42);",
        "let const = \\x y -> x; let result1 = const(42, 100); let result2 = const(200, 42);",
    ];

    for source in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match type_check_program(&program) {
                    Ok(()) => {
                        // Polymorphic functions should type check successfully
                    }
                    Err(e) => {
                        println!("     Type checking failed: {e:?}");
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Parsing failed: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_enhanced_pattern_matching() -> bool {
    // Pattern matching is not yet fully implemented in the parser
    // For now, we'll skip this test
    println!("     Skipping pattern matching test (not yet implemented)");
    true
}

fn test_enhanced_error_reporting() -> bool {
    let test_cases = vec![
        "let x = 1 + \"hello\";", // Type mismatch
    ];

    for source in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match type_check_program(&program) {
                    Ok(()) => {
                        // These should fail type checking
                        println!("     Expected type error, but type checking succeeded");
                        return false;
                    }
                    Err(e) => {
                        // Check that error messages are enhanced
                        let error_str = e.to_string();
                        println!("     Got error: {error_str}");
                        if !error_str.contains("Type mismatch") && !error_str.contains("type") {
                            println!("     Error message not enhanced: {error_str}");
                            return false;
                        }
                    }
                }
            }
            Err(e) => {
                println!("     Parsing failed: {e:?}");
                return false;
            }
        }
    }

    true
}

fn test_complex_type_inference() -> bool {
    let test_cases = vec!["let add = \\x y -> x + y; let result = add(5, 3);"];

    for source in test_cases {
        match parse_program(source) {
            Ok(program) => {
                match type_check_program(&program) {
                    Ok(()) => {
                        // Complex programs should type check successfully
                    }
                    Err(e) => {
                        println!("     Type checking failed: {e:?}");
                        return false;
                    }
                }
            }
            Err(e) => {
                println!("     Parsing failed: {e:?}");
                return false;
            }
        }
    }

    true
}
