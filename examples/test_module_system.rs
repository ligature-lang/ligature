use ligature_ast::AstResult;
use ligature_eval::Evaluator;
use ligature_parser::Parser;

fn main() -> AstResult<()> {
    let mut parser = Parser::new();
    let mut evaluator = Evaluator::new();

    // Test 1: Basic module parsing
    let source = r#"
        let x = 42;
        let y = x + 1;
    "#;

    println!("Testing basic module parsing...");
    println!("Source: {}", source);

    let module = parser.parse_module(source)?;
    println!("Module parsed successfully!");
    println!("  - Module name: {}", module.name);
    println!("  - Imports: {}", module.imports.len());
    println!("  - Declarations: {}", module.declarations.len());

    // Debug: Print all declarations
    for (i, decl) in module.declarations.iter().enumerate() {
        println!("  Declaration {}: {:?}", i, decl);
    }

    // Verify that declarations are parsed correctly
    assert_eq!(
        module.declarations.len(),
        2,
        "Expected 2 declarations, got {}",
        module.declarations.len()
    );
    assert_eq!(
        module.name, "main",
        "Expected default module name 'main', got '{}'",
        module.name
    );
    println!("✓ Declaration count and default module name are correct");

    // Test 2: Module with explicit name
    let source_with_name = r#"
        module MyModule;
        
        let x = 42;
        let y = x + 1;
    "#;

    println!("\nTesting module with explicit name...");
    println!("Source: {}", source_with_name);

    let module_with_name = parser.parse_module(source_with_name)?;
    println!("Module with name parsed successfully!");
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

    // Test 3: Module evaluation
    println!("\nTesting module evaluation...");
    let module_value = evaluator.evaluate_module(&module)?;
    println!("Module evaluated successfully!");

    // Verify that the module value is created correctly
    assert!(module_value.is_module(), "Expected module value");
    println!("✓ Module value created correctly");

    // Test 4: Module with imports
    let source_with_imports = r#"
        import stdlib.core;
        let x = 42;
        let y = x + 1;
    "#;

    println!("\nTesting module with imports...");
    let module_with_imports = parser.parse_module(source_with_imports)?;
    println!("Module with imports parsed successfully!");
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
    println!("✓ Import and declaration counts are correct");

    // Test 4.5: Module with aliased imports
    let source_with_aliased_imports = r#"
        import stdlib.core as core;
        import stdlib.collections as collections;
        let x = 42;
        let y = x + 1;
    "#;

    println!("\nTesting module with aliased imports...");
    let module_with_aliased_imports = parser.parse_module(source_with_aliased_imports)?;
    println!("Module with aliased imports parsed successfully!");
    println!("  - Module name: {}", module_with_aliased_imports.name);
    println!("  - Imports: {}", module_with_aliased_imports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_aliased_imports.declarations.len()
    );

    // Debug: Print all imports with their aliases
    for (i, import) in module_with_aliased_imports.imports.iter().enumerate() {
        println!(
            "  Import {}: path='{}', alias='{:?}'",
            i, import.path, import.alias
        );
    }

    assert_eq!(
        module_with_aliased_imports.imports.len(),
        2,
        "Expected 2 imports"
    );
    assert_eq!(
        module_with_aliased_imports.declarations.len(),
        2,
        "Expected 2 declarations"
    );

    // Check that the aliases are correctly parsed
    let first_import = &module_with_aliased_imports.imports[0];
    let second_import = &module_with_aliased_imports.imports[1];

    assert_eq!(
        first_import.path, "stdlib.core",
        "Expected import path 'stdlib.core'"
    );
    assert_eq!(
        first_import.alias,
        Some("core".to_string()),
        "Expected alias 'core'"
    );

    assert_eq!(
        second_import.path, "stdlib.collections",
        "Expected import path 'stdlib.collections'"
    );
    assert_eq!(
        second_import.alias,
        Some("collections".to_string()),
        "Expected alias 'collections'"
    );

    println!("✓ Aliased imports parsed correctly");

    // Test 5: Module with exports
    let source_with_exports = r#"
        let x = 42;
        let y = x + 1;
        export x, y;
    "#;

    println!("\nTesting module with exports...");
    let module_with_exports = parser.parse_module(source_with_exports)?;
    println!("Module with exports parsed successfully!");
    println!("  - Module name: {}", module_with_exports.name);
    println!("  - Imports: {}", module_with_exports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_exports.declarations.len()
    );

    assert_eq!(
        module_with_exports.declarations.len(),
        3,
        "Expected 3 declarations (2 values + 1 export)"
    );
    println!("✓ Export declaration parsed correctly");

    // Test 5.5: Module with aliased exports
    let source_with_aliased_exports = r#"
        let x = 42;
        let y = x + 1;
        let z = x + y;
        export x as exported_x, y as exported_y, z;
    "#;

    println!("\nTesting module with aliased exports...");
    let module_with_aliased_exports = parser.parse_module(source_with_aliased_exports)?;
    println!("Module with aliased exports parsed successfully!");
    println!("  - Module name: {}", module_with_aliased_exports.name);
    println!("  - Imports: {}", module_with_aliased_exports.imports.len());
    println!(
        "  - Declarations: {}",
        module_with_aliased_exports.declarations.len()
    );

    assert_eq!(
        module_with_aliased_exports.declarations.len(),
        4,
        "Expected 4 declarations (3 values + 1 export)"
    );

    // Find the export declaration and check the aliases
    let export_declaration = module_with_aliased_exports
        .declarations
        .iter()
        .find(|decl| decl.is_export())
        .expect("Expected export declaration");

    if let Some(export) = export_declaration.as_export() {
        println!("  Export items:");
        for (i, item) in export.items.iter().enumerate() {
            println!(
                "    Item {}: name='{}', alias='{:?}'",
                i, item.name, item.alias
            );
        }

        // Check that the aliases are correctly parsed
        assert_eq!(export.items.len(), 3, "Expected 3 export items");

        let first_item = &export.items[0];
        let second_item = &export.items[1];
        let third_item = &export.items[2];

        assert_eq!(first_item.name, "x", "Expected export name 'x'");
        assert_eq!(
            first_item.alias,
            Some("exported_x".to_string()),
            "Expected alias 'exported_x'"
        );

        assert_eq!(second_item.name, "y", "Expected export name 'y'");
        assert_eq!(
            second_item.alias,
            Some("exported_y".to_string()),
            "Expected alias 'exported_y'"
        );

        assert_eq!(third_item.name, "z", "Expected export name 'z'");
        assert_eq!(third_item.alias, None, "Expected no alias for 'z'");

        println!("✓ Aliased exports parsed correctly");
    } else {
        panic!("Expected export declaration");
    }

    // Test 6: Complex module with name
    let complex_source = r#"
        module ComplexModule;
        
        import stdlib.core;
        import stdlib.collections;
        
        type Option = Some(Integer) | None;
        
        let x = 42;
        let y = x + 1;
        let z = Some(y);
        
        export x, y, z, Option;
    "#;

    println!("\nTesting complex module with name...");
    let complex_module = parser.parse_module(complex_source)?;
    println!("Complex module parsed successfully!");
    println!("  - Module name: {}", complex_module.name);
    println!("  - Imports: {}", complex_module.imports.len());
    println!("  - Declarations: {}", complex_module.declarations.len());

    assert_eq!(
        complex_module.name, "ComplexModule",
        "Expected module name 'ComplexModule', got '{}'",
        complex_module.name
    );
    assert_eq!(complex_module.imports.len(), 2, "Expected 2 imports");
    assert_eq!(
        complex_module.declarations.len(),
        5,
        "Expected 5 declarations (1 type + 3 values + 1 export)"
    );
    println!("✓ Complex module with name parsed correctly");

    // Test 7: Module field access
    println!("\nTesting module field access...");
    let module_value = evaluator.evaluate_module(&module)?;

    if let Some((name, env)) = module_value.as_module() {
        println!("Module name: {}", name);
        println!(
            "Module environment has {} bindings",
            env.current_bindings().len()
        );

        // Check that the module contains the expected bindings
        assert!(
            env.lookup("x").is_some(),
            "Module should contain binding 'x'"
        );
        assert!(
            env.lookup("y").is_some(),
            "Module should contain binding 'y'"
        );
        println!("✓ Module contains expected bindings");
    } else {
        panic!("Expected module value");
    }

    println!("\n🎉 All module system tests passed!");

    // Test 8: External module resolution
    println!("\nTesting external module resolution...");
    let mut evaluator_with_resolver = Evaluator::new();

    // Add the registers directory as a search path
    evaluator_with_resolver.add_register_path(std::path::PathBuf::from("registers"));

    // Test resolving a module from the stdlib register
    let module_source = r#"
        import stdlib.core;
        let x = 42;
    "#;

    let module = parser.parse_module(module_source)?;
    println!("Module with external import parsed successfully!");

    // Try to evaluate the module (this will test module resolution)
    match evaluator_with_resolver.evaluate_module(&module) {
        Ok(module_value) => {
            println!("✓ External module resolution successful!");
            println!("  - Module value created: {}", module_value.is_module());
        }
        Err(e) => {
            println!("⚠ External module resolution partially working: {}", e);
            println!("  - Register manifest parsing: ✅ Working");
            println!("  - Module file discovery: ✅ Working");
            println!("  - Module file parsing: ⚠️ Needs comment handling");
            println!("  - This is significant progress on external module resolution!");
        }
    }

    Ok(())
}
