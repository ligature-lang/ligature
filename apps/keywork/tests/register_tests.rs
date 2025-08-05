use keywork::register::Register;
use std::path::Path;

#[test]
fn test_load_stdlib_register() {
    let stdlib_path = Path::new("../../registers/stdlib");
    let register = Register::load(stdlib_path).expect("Failed to load stdlib register");

    assert_eq!(register.manifest.name, "stdlib");
    assert_eq!(register.manifest.version, "1.0.0");
    assert_eq!(register.manifest.description, "Ligature Standard Library");
    assert_eq!(
        register.manifest.authors,
        vec!["Ligature Team <team@ligature.dev>"]
    );
    assert_eq!(register.manifest.license, "Apache-2.0");
    assert_eq!(
        register.manifest.repository,
        Some("https://github.com/ligature-lang/ligature".to_string())
    );

    // Check exports
    assert_eq!(
        register.exports.get("core"),
        Some(&"core/mod.lig".to_string())
    );
    assert_eq!(
        register.exports.get("collections"),
        Some(&"collections/mod.lig".to_string())
    );
    assert_eq!(
        register.exports.get("validation"),
        Some(&"validation/mod.lig".to_string())
    );

    // Check metadata
    assert!(register.metadata.is_some());
    let metadata = register.metadata.unwrap();
    assert_eq!(metadata.tags, vec!["standard-library", "core"]);

    // Check dependencies (should be empty for stdlib)
    assert!(register.dependencies.is_empty());
}

#[test]
fn test_load_test_register() {
    let test_register_path = Path::new("../../crates/test-register");
    let register = Register::load(test_register_path).expect("Failed to load test-register");

    assert_eq!(register.manifest.name, "test-register");
    assert_eq!(register.manifest.version, "0.1.0");
    assert_eq!(register.manifest.description, "A Ligature register");
    assert_eq!(
        register.manifest.authors,
        vec!["Your Name <your.email@example.com>"]
    );
    assert_eq!(register.manifest.license, "Apache-2.0");
    assert_eq!(register.manifest.repository, None);

    // Check that dependencies and exports are empty (as expected for this template)
    assert!(register.dependencies.is_empty());
    assert!(register.exports.is_empty());

    // Check metadata
    assert!(register.metadata.is_some());
    let metadata = register.metadata.unwrap();
    assert!(metadata.tags.is_empty());
}

#[test]
fn test_load_nonexistent_register() {
    let nonexistent_path = Path::new("../../nonexistent-register");
    let result = Register::load(nonexistent_path);
    assert!(result.is_err());

    let error = result.unwrap_err();
    assert!(error.to_string().contains("No register.toml found"));
}

#[test]
fn test_register_validation() {
    let stdlib_path = Path::new("../../registers/stdlib");
    let register = Register::load(stdlib_path).expect("Failed to load stdlib register");

    // Test basic validation
    assert!(!register.manifest.name.is_empty());
    assert!(!register.manifest.version.is_empty());
    assert!(!register.manifest.description.is_empty());
    assert!(!register.manifest.authors.is_empty());
    assert!(!register.manifest.license.is_empty());

    // Test version format validation
    assert!(register.is_valid_version(&register.manifest.version));
    assert!(!register.is_valid_version("invalid"));
    assert!(!register.is_valid_version("1.0"));
    assert!(!register.is_valid_version("1.0.0.0"));
}
