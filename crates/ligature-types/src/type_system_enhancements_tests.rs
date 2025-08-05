//! Tests for type system enhancements in the Ligature language.

use crate::inference::TypeInference;
use ligature_ast::{Span, Type, TypeKind};

#[test]
fn test_cycle_detection() {
    let mut inference = TypeInference::new();

    // Test self-import detection
    let self_import = ligature_ast::Import {
        path: "self".to_string(),
        alias: None,
        items: None,
        span: Span::default(),
    };
    assert!(inference.detect_import_cycle(&self_import));

    // Test basic cycle detection
    let import1 = ligature_ast::Import {
        path: "stdlib.core".to_string(),
        alias: None,
        items: None,
        span: Span::default(),
    };
    let import2 = ligature_ast::Import {
        path: "stdlib.collections".to_string(),
        alias: None,
        items: None,
        span: Span::default(),
    };

    // Initially no cycles
    assert!(!inference.detect_import_cycle(&import1));
    assert!(!inference.detect_import_cycle(&import2));

    // Add a dependency and test cycle detection
    inference.add_dependency("module1", "stdlib:core");
    inference.add_dependency("stdlib:core", "stdlib:collections");

    // This should detect a cycle if we try to add a dependency back
    inference.add_dependency("stdlib:collections", "module1");
    assert!(inference.would_create_cycle("module1"));
}

#[test]
fn test_nested_module_paths() {
    let mut inference = TypeInference::new();

    // Test simple path
    let (register, module) = inference.parse_import_path("stdlib.core").unwrap();
    assert_eq!(register, "stdlib");
    assert_eq!(module, "core");

    // Test nested path
    let (register, module) = inference
        .parse_import_path("stdlib.collections.list")
        .unwrap();
    assert_eq!(register, "stdlib");
    assert_eq!(module, "collections/list");

    // Test deeply nested path
    let (register, module) = inference
        .parse_import_path("mylib.data.structures.tree.binary")
        .unwrap();
    assert_eq!(register, "mylib");
    assert_eq!(module, "data/structures/tree/binary");
}

#[test]
fn test_register_toml_parsing() {
    let mut inference = TypeInference::new();

    // Create a temporary register.toml file for testing
    let temp_dir = tempfile::tempdir().unwrap();
    let register_path = temp_dir.path().join("register.toml");

    let toml_content = r#"
[register]
name = "test"
version = "1.0.0"

[exports]
core = "core/mod.lig"
collections = "collections/mod.lig"
validation = "validation/mod.lig"
"#;

    std::fs::write(&register_path, toml_content).unwrap();

    let exports = inference.parse_register_toml(&register_path).unwrap();

    assert_eq!(exports.get("core"), Some(&"core/mod.lig".to_string()));
    assert_eq!(
        exports.get("collections"),
        Some(&"collections/mod.lig".to_string())
    );
    assert_eq!(
        exports.get("validation"),
        Some(&"validation/mod.lig".to_string())
    );
    assert_eq!(exports.get("nonexistent"), None);
}

#[test]
fn test_warning_mechanism() {
    use crate::environment::{ConflictResolutionStrategy, TypeEnvironment};

    let mut env = TypeEnvironment::new();

    // Initially no warnings
    assert!(!env.has_warnings());
    assert_eq!(env.get_warnings().len(), 0);

    // Add a binding
    env.bind("x".to_string(), Type::integer(Span::default()));

    // Add another binding with the same name using warn strategy
    env.bind_with_strategy(
        "x".to_string(),
        Type::string(Span::default()),
        ConflictResolutionStrategy::Warn,
    )
    .unwrap();

    // Should have a warning
    assert!(env.has_warnings());
    assert_eq!(env.get_warnings().len(), 1);
    assert!(env.get_warnings()[0].contains("Binding conflict"));

    // Clear warnings
    env.clear_warnings();
    assert!(!env.has_warnings());
    assert_eq!(env.get_warnings().len(), 0);
}

#[test]
fn test_exported_item_type_resolution() {
    let mut inference = TypeInference::new();

    // Create a simple module with exports
    let module = ligature_ast::Module {
        name: "test_module".to_string(),
        imports: vec![],
        declarations: vec![
            ligature_ast::Declaration {
                kind: ligature_ast::DeclarationKind::Value(ligature_ast::ValueDeclaration {
                    name: "my_value".to_string(),
                    value: ligature_ast::Expr {
                        kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
                        span: Span::default(),
                    },
                    type_annotation: None,
                    is_recursive: false,
                    span: Span::default(),
                }),
                span: Span::default(),
            },
            ligature_ast::Declaration {
                kind: ligature_ast::DeclarationKind::Export(ligature_ast::ExportDeclaration {
                    items: vec![ligature_ast::ExportItem {
                        name: "my_value".to_string(),
                        alias: None,
                        span: Span::default(),
                    }],
                    span: Span::default(),
                }),
                span: Span::default(),
            },
        ],
        span: Span::default(),
    };

    // Test getting the type of an exported item
    let item_type = inference
        .get_exported_item_type(&module, "my_value")
        .unwrap();
    assert!(matches!(item_type.kind, TypeKind::Integer));

    // Test getting the type of a non-existent item
    let result = inference.get_exported_item_type(&module, "nonexistent");
    assert!(result.is_err());
}

#[test]
fn test_dependency_graph_operations() {
    let mut inference = TypeInference::new();

    // Test adding dependencies
    inference.add_dependency("module1", "module2");
    inference.add_dependency("module2", "module3");

    // Test getting dependencies
    let deps = inference.get_dependencies("module1").unwrap();
    assert!(deps.contains("module2"));

    let deps = inference.get_dependencies("module2").unwrap();
    assert!(deps.contains("module3"));

    // Test getting the full dependency graph
    let graph = inference.get_dependency_graph();
    assert!(graph.contains_key("module1"));
    assert!(graph.contains_key("module2"));
    assert!(!graph.contains_key("module3")); // module3 has no dependencies
}

#[test]
fn test_cycle_detection_with_dependency_graph() {
    let mut inference = TypeInference::new();

    // Create a cycle: module1 -> module2 -> module3 -> module1
    inference.add_dependency("module1", "module2");
    inference.add_dependency("module2", "module3");
    inference.add_dependency("module3", "module1");

    // Should detect cycle
    assert!(inference.would_create_cycle("module1"));
    assert!(inference.would_create_cycle("module2"));
    assert!(inference.would_create_cycle("module3"));

    // Test acyclic graph
    let mut inference2 = TypeInference::new();
    inference2.add_dependency("module1", "module2");
    inference2.add_dependency("module2", "module3");

    // Should not detect cycle
    assert!(!inference2.would_create_cycle("module1"));
    assert!(!inference2.would_create_cycle("module2"));
    assert!(!inference2.would_create_cycle("module3"));
}
