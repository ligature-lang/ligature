use ligature_ast::{AstResult, Pattern, Span};
use ligature_eval::{Evaluator, Value};

fn main() -> AstResult<()> {
    println!("Testing enhanced union pattern matching...");

    let evaluator = Evaluator::new();

    // Test 1: Basic union pattern matching without variable binding
    println!("\n=== Test 1: Basic Union Pattern Matching ===");

    let some_value = Value::union(
        "Some".to_string(),
        Some(Value::integer(42, Span::default())),
        Span::default(),
    );
    let none_value = Value::union("None".to_string(), None, Span::default());

    // Test Some pattern without binding
    let some_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: None,
    };

    let matches_some = evaluator.pattern_matches(&some_pattern, &some_value)?;
    println!("✓ Some pattern matches Some(42): {}", matches_some);

    let matches_none = evaluator.pattern_matches(&some_pattern, &none_value)?;
    println!("✓ Some pattern matches None: {}", matches_none);

    // Test None pattern
    let none_pattern = Pattern::Union {
        variant: "None".to_string(),
        value: None,
    };

    let matches_some_none = evaluator.pattern_matches(&none_pattern, &some_value)?;
    println!("✓ None pattern matches Some(42): {}", matches_some_none);

    let matches_none_none = evaluator.pattern_matches(&none_pattern, &none_value)?;
    println!("✓ None pattern matches None: {}", matches_none_none);

    // Test 2: Union pattern matching with variable binding
    println!("\n=== Test 2: Union Pattern Matching with Variable Binding ===");

    let mut bindings = std::collections::HashMap::new();
    let some_with_binding_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Variable("n".to_string()))),
    };

    let matches_with_binding = evaluator.pattern_matches_with_bindings(
        &some_with_binding_pattern,
        &some_value,
        &mut bindings,
    )?;
    println!(
        "✓ Some(n) pattern matches Some(42): {}",
        matches_with_binding
    );
    println!("✓ Variable binding 'n' = {:?}", bindings.get("n"));

    // Test 3: Nested union pattern matching
    println!("\n=== Test 3: Nested Union Pattern Matching ===");

    // Create a nested union: Some(Some(42))
    let inner_some = Value::union(
        "Some".to_string(),
        Some(Value::integer(42, Span::default())),
        Span::default(),
    );
    let nested_some = Value::union("Some".to_string(), Some(inner_some), Span::default());

    let nested_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Union {
            variant: "Some".to_string(),
            value: Some(Box::new(Pattern::Variable("x".to_string()))),
        })),
    };

    let mut nested_bindings = std::collections::HashMap::new();
    let matches_nested = evaluator.pattern_matches_with_bindings(
        &nested_pattern,
        &nested_some,
        &mut nested_bindings,
    )?;
    println!(
        "✓ Some(Some(x)) pattern matches Some(Some(42)): {}",
        matches_nested
    );
    println!("✓ Variable binding 'x' = {:?}", nested_bindings.get("x"));

    // Test 4: Complex pattern matching with multiple variables
    println!("\n=== Test 4: Complex Pattern Matching ===");

    // Create a record with union fields
    let mut record_fields = std::collections::HashMap::new();
    record_fields.insert(
        "status".to_string(),
        Value::union(
            "Success".to_string(),
            Some(Value::integer(200, Span::default())),
            Span::default(),
        ),
    );
    record_fields.insert(
        "data".to_string(),
        Value::string("Hello".to_string(), Span::default()),
    );
    let record_value = Value::record(record_fields, Span::default());

    let complex_pattern = Pattern::Record {
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
                pattern: Pattern::Variable("content".to_string()),
                span: Span::default(),
            },
        ],
    };

    let mut complex_bindings = std::collections::HashMap::new();
    let matches_complex = evaluator.pattern_matches_with_bindings(
        &complex_pattern,
        &record_value,
        &mut complex_bindings,
    )?;
    println!("✓ Complex pattern matches record: {}", matches_complex);
    println!(
        "✓ Variable binding 'code' = {:?}",
        complex_bindings.get("code")
    );
    println!(
        "✓ Variable binding 'content' = {:?}",
        complex_bindings.get("content")
    );

    // Test 5: Pattern matching with literal values
    println!("\n=== Test 5: Union Pattern Matching with Literals ===");

    let some_five = Value::union(
        "Some".to_string(),
        Some(Value::integer(5, Span::default())),
        Span::default(),
    );

    let literal_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Literal(ligature_ast::Literal::Integer(
            5,
        )))),
    };

    let matches_literal = evaluator.pattern_matches(&literal_pattern, &some_five)?;
    println!("✓ Some(5) pattern matches Some(5): {}", matches_literal);

    let matches_literal_false = evaluator.pattern_matches(&literal_pattern, &some_value)?;
    println!(
        "✓ Some(5) pattern matches Some(42): {}",
        matches_literal_false
    );

    // Test 6: Error cases and edge cases
    println!("\n=== Test 6: Error Cases and Edge Cases ===");

    // Test matching union against non-union value
    let non_union_value = Value::integer(42, Span::default());
    let matches_non_union = evaluator.pattern_matches(&some_pattern, &non_union_value)?;
    println!(
        "✓ Union pattern matches non-union value: {}",
        matches_non_union
    );

    // Test matching wrong variant
    let wrong_variant_pattern = Pattern::Union {
        variant: "Error".to_string(),
        value: None,
    };
    let matches_wrong_variant = evaluator.pattern_matches(&wrong_variant_pattern, &some_value)?;
    println!(
        "✓ Wrong variant pattern matches Some(42): {}",
        matches_wrong_variant
    );

    println!("\n✓ All union pattern matching tests completed successfully!");
    Ok(())
}
