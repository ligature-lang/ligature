use std::time::Instant;

use ligature_ast::{AstResult, Pattern, Span};
use ligature_eval::{Evaluator, Value};

fn main() -> AstResult<()> {
    println!("Testing advanced union pattern matching...");

    let evaluator = Evaluator::new();

    // Test 1: Performance testing with deep nested unions
    println!("\n=== Test 1: Performance Testing ===");

    // Create a deeply nested union: Some(Some(Some(Some(42))))
    let mut current_value = Value::integer(42, Span::default());
    for _ in 0..4 {
        current_value = Value::union("Some".to_string(), Some(current_value), Span::default());
    }

    // Create a deep pattern to match it
    let mut current_pattern = Pattern::Variable("x".to_string());
    for _ in 0..4 {
        current_pattern = Pattern::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(current_pattern)),
        };
    }

    let start = Instant::now();
    let mut bindings = std::collections::HashMap::new();
    let matches_deep =
        evaluator.pattern_matches_with_bindings(&current_pattern, &current_value, &mut bindings)?;
    let duration = start.elapsed();

    println!("✓ Deep nested pattern matching: {matches_deep} (took {duration:?})");
    println!("✓ Variable binding 'x' = {:?}", bindings.get("x"));

    // Test 2: Union pattern matching with complex nested structures
    println!("\n=== Test 2: Complex Nested Structures ===");

    // Create a complex structure: Some({ status: Success(200), data: Some("hello") })
    let mut complex_record = std::collections::HashMap::new();
    complex_record.insert(
        "status".to_string(),
        Value::union(
            "Success".to_string(),
            Some(Value::integer(200, Span::default())),
            Span::default(),
        ),
    );
    complex_record.insert(
        "data".to_string(),
        Value::union(
            "Some".to_string(),
            Some(Value::string("hello".to_string(), Span::default())),
            Span::default(),
        ),
    );

    let complex_union = Value::union(
        "Some".to_string(),
        Some(Value::record(complex_record, Span::default())),
        Span::default(),
    );

    let complex_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Record {
            fields: vec![
                ligature_ast::RecordPatternField {
                    name: "status".to_string(),
                    pattern: Pattern::Union {
                        variant: "Success".to_string(),
                        value: Some(Box::new(Pattern::Variable("code".to_string()))),
                    },
                    span: Span::default(),
                },
                ligature_ast::RecordPatternField {
                    name: "data".to_string(),
                    pattern: Pattern::Union {
                        variant: "Some".to_string(),
                        value: Some(Box::new(Pattern::Variable("content".to_string()))),
                    },
                    span: Span::default(),
                },
            ],
        })),
    };

    let mut complex_bindings = std::collections::HashMap::new();
    let matches_complex = evaluator.pattern_matches_with_bindings(
        &complex_pattern,
        &complex_union,
        &mut complex_bindings,
    )?;
    println!("✓ Complex nested pattern matching: {matches_complex}");
    println!(
        "✓ Variable binding 'code' = {:?}",
        complex_bindings.get("code")
    );
    println!(
        "✓ Variable binding 'content' = {:?}",
        complex_bindings.get("content")
    );

    // Test 3: Union pattern matching with multiple variants
    println!("\n=== Test 3: Multiple Variant Testing ===");

    let success_value = Value::union(
        "Success".to_string(),
        Some(Value::string("ok".to_string(), Span::default())),
        Span::default(),
    );
    let error_value = Value::union(
        "Error".to_string(),
        Some(Value::string("failed".to_string(), Span::default())),
        Span::default(),
    );
    let loading_value = Value::union("Loading".to_string(), None, Span::default());

    let patterns = [
        Pattern::Union {
            variant: "Success".to_string(),
            value: Some(Box::new(Pattern::Variable("msg".to_string()))),
        },
        Pattern::Union {
            variant: "Error".to_string(),
            value: Some(Box::new(Pattern::Variable("err".to_string()))),
        },
        Pattern::Union {
            variant: "Loading".to_string(),
            value: None,
        },
    ];

    for (i, pattern) in patterns.iter().enumerate() {
        let mut test_bindings = std::collections::HashMap::new();
        let matches_success =
            evaluator.pattern_matches_with_bindings(pattern, &success_value, &mut test_bindings)?;
        let matches_error =
            evaluator.pattern_matches_with_bindings(pattern, &error_value, &mut test_bindings)?;
        let matches_loading =
            evaluator.pattern_matches_with_bindings(pattern, &loading_value, &mut test_bindings)?;

        println!(
            "✓ Pattern {}: Success={}, Error={}, Loading={}",
            i + 1,
            matches_success,
            matches_error,
            matches_loading
        );
    }

    // Test 4: Union pattern matching with literal constraints
    println!("\n=== Test 4: Literal Constraints ===");

    let some_42 = Value::union(
        "Some".to_string(),
        Some(Value::integer(42, Span::default())),
        Span::default(),
    );
    let some_100 = Value::union(
        "Some".to_string(),
        Some(Value::integer(100, Span::default())),
        Span::default(),
    );

    let literal_42_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Literal(ligature_ast::Literal::Integer(
            42,
        )))),
    };

    let matches_42_42 = evaluator.pattern_matches(&literal_42_pattern, &some_42)?;
    let matches_42_100 = evaluator.pattern_matches(&literal_42_pattern, &some_100)?;

    println!("✓ Some(42) pattern matches Some(42): {matches_42_42}");
    println!("✓ Some(42) pattern matches Some(100): {matches_42_100}");

    // Test 5: Union pattern matching with wildcards
    println!("\n=== Test 5: Wildcard Patterns ===");

    let wildcard_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Wildcard)),
    };

    let matches_wildcard_42 = evaluator.pattern_matches(&wildcard_pattern, &some_42)?;
    let matches_wildcard_100 = evaluator.pattern_matches(&wildcard_pattern, &some_100)?;
    let matches_wildcard_none = evaluator.pattern_matches(
        &wildcard_pattern,
        &Value::union("None".to_string(), None, Span::default()),
    )?;

    println!("✓ Some(_) pattern matches Some(42): {matches_wildcard_42}");
    println!("✓ Some(_) pattern matches Some(100): {matches_wildcard_100}");
    println!("✓ Some(_) pattern matches None: {matches_wildcard_none}");

    // Test 6: Union pattern matching with list patterns
    println!("\n=== Test 6: List Pattern Integration ===");

    let list_value = Value::list(
        vec![
            Value::union(
                "Some".to_string(),
                Some(Value::integer(1, Span::default())),
                Span::default(),
            ),
            Value::union("None".to_string(), None, Span::default()),
            Value::union(
                "Some".to_string(),
                Some(Value::integer(3, Span::default())),
                Span::default(),
            ),
        ],
        Span::default(),
    );

    let list_pattern = Pattern::List {
        elements: vec![
            Pattern::Union {
                variant: "Some".to_string(),
                value: Some(Box::new(Pattern::Variable("first".to_string()))),
            },
            Pattern::Union {
                variant: "None".to_string(),
                value: None,
            },
            Pattern::Union {
                variant: "Some".to_string(),
                value: Some(Box::new(Pattern::Variable("third".to_string()))),
            },
        ],
    };

    let mut list_bindings = std::collections::HashMap::new();
    let matches_list =
        evaluator.pattern_matches_with_bindings(&list_pattern, &list_value, &mut list_bindings)?;
    println!("✓ List with union patterns matching: {matches_list}");
    println!(
        "✓ Variable binding 'first' = {:?}",
        list_bindings.get("first")
    );
    println!(
        "✓ Variable binding 'third' = {:?}",
        list_bindings.get("third")
    );

    println!("\n✓ All advanced union pattern matching tests completed successfully!");
    Ok(())
}
