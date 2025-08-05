use keywork::dependency::Semver;

#[test]
fn test_semver_parsing() {
    // Test basic version parsing
    let version = Semver::parse("1.2.3").unwrap();
    assert_eq!(version.major, 1);
    assert_eq!(version.minor, 2);
    assert_eq!(version.patch, 3);
    assert_eq!(version.pre_release, None);
    assert_eq!(version.build, None);

    // Test with leading 'v'
    let version = Semver::parse("v2.0.0").unwrap();
    assert_eq!(version.major, 2);
    assert_eq!(version.minor, 0);
    assert_eq!(version.patch, 0);

    // Test with pre-release
    let version = Semver::parse("1.0.0-alpha").unwrap();
    assert_eq!(version.major, 1);
    assert_eq!(version.minor, 0);
    assert_eq!(version.patch, 0);
    assert_eq!(version.pre_release, Some("alpha".to_string()));

    // Test with build metadata
    let version = Semver::parse("1.0.0+build.123").unwrap();
    assert_eq!(version.major, 1);
    assert_eq!(version.minor, 0);
    assert_eq!(version.patch, 0);
    assert_eq!(version.build, Some("build.123".to_string()));

    // Test with both pre-release and build
    let version = Semver::parse("1.0.0-alpha+build.123").unwrap();
    assert_eq!(version.major, 1);
    assert_eq!(version.minor, 0);
    assert_eq!(version.patch, 0);
    assert_eq!(version.pre_release, Some("alpha".to_string()));
    assert_eq!(version.build, Some("build.123".to_string()));
}

#[test]
fn test_semver_constraints() {
    let version = Semver::parse("1.2.3").unwrap();

    // Test exact version matching
    assert!(version.satisfies_constraint("1.2.3"));
    assert!(!version.satisfies_constraint("1.2.4"));

    // Test greater than
    assert!(version.satisfies_constraint(">1.2.0"));
    assert!(version.satisfies_constraint(">1.0.0"));
    assert!(!version.satisfies_constraint(">1.2.3"));
    assert!(!version.satisfies_constraint(">2.0.0"));

    // Test greater than or equal
    assert!(version.satisfies_constraint(">=1.2.3"));
    assert!(version.satisfies_constraint(">=1.2.0"));
    assert!(!version.satisfies_constraint(">=1.2.4"));

    // Test less than
    assert!(version.satisfies_constraint("<2.0.0"));
    assert!(version.satisfies_constraint("<1.3.0"));
    assert!(!version.satisfies_constraint("<1.2.3"));
    assert!(!version.satisfies_constraint("<1.0.0"));

    // Test less than or equal
    assert!(version.satisfies_constraint("<=1.2.3"));
    assert!(version.satisfies_constraint("<=1.3.0"));
    assert!(!version.satisfies_constraint("<=1.2.2"));

    // Test tilde range (~1.2.3 means >=1.2.3 and <1.3.0)
    assert!(version.satisfies_constraint("~1.2.3"));
    assert!(version.satisfies_constraint("~1.2.0"));
    assert!(!version.satisfies_constraint("~1.3.0"));
    assert!(!version.satisfies_constraint("~1.1.0"));

    // Test caret range (^1.2.3 means >=1.2.3 and <2.0.0)
    assert!(version.satisfies_constraint("^1.2.3"));
    assert!(version.satisfies_constraint("^1.0.0"));
    assert!(!version.satisfies_constraint("^2.0.0"));
    assert!(!version.satisfies_constraint("^0.9.0"));

    // Test wildcards
    assert!(version.satisfies_constraint("*"));
    assert!(version.satisfies_constraint("x"));
    assert!(version.satisfies_constraint("X"));
    assert!(version.satisfies_constraint("latest"));
}

#[test]
fn test_semver_ordering() {
    let v1_0_0 = Semver::parse("1.0.0").unwrap();
    let v1_1_0 = Semver::parse("1.1.0").unwrap();
    let v1_1_1 = Semver::parse("1.1.1").unwrap();
    let v2_0_0 = Semver::parse("2.0.0").unwrap();

    assert!(v1_0_0 < v1_1_0);
    assert!(v1_1_0 < v1_1_1);
    assert!(v1_1_1 < v2_0_0);
    assert!(v2_0_0 > v1_1_1);
    assert!(v1_1_1 > v1_1_0);
    assert!(v1_1_0 > v1_0_0);

    assert!(v1_0_0 <= v1_0_0);
    assert!(v1_0_0 >= v1_0_0);
    assert!(v1_0_0 == v1_0_0);
}

#[test]
fn test_invalid_semver() {
    // Test invalid formats
    assert!(Semver::parse("1.2").is_err());
    assert!(Semver::parse("1").is_err());
    assert!(Semver::parse("invalid").is_err());
    assert!(Semver::parse("1.2.3.4").is_err());
}
