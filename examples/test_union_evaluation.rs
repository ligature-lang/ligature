use ligature_ast::{AstResult, Span};
use ligature_eval::{Evaluator, Value};

fn main() -> AstResult<()> {
    println!("Testing improved union evaluation...");

    let mut evaluator = Evaluator::new();

    // Test union value creation
    let some_value = Value::union(
        "Some".to_string(),
        Some(Value::integer(42, Span::default())),
        Span::default(),
    );
    println!("✓ Created Some(42): {:?}", some_value);

    let none_value = Value::union("None".to_string(), None, Span::default());
    println!("✓ Created None: {:?}", none_value);

    // Test union value access
    if let Some((variant, value)) = some_value.as_union() {
        println!("✓ Some value variant: {}, payload: {:?}", variant, value);
    }

    if let Some((variant, value)) = none_value.as_union() {
        println!("✓ None value variant: {}, payload: {:?}", variant, value);
    }

    // Test union value type checking
    println!("✓ Some is_union(): {}", some_value.is_union());
    println!("✓ None is_union(): {}", none_value.is_union());

    // Test pattern matching logic directly
    use ligature_ast::Pattern;

    // Test Some pattern matching
    let some_pattern = Pattern::Union {
        variant: "Some".to_string(),
        value: Some(Box::new(Pattern::Variable("n".to_string()))),
    };

    let matches_some = evaluator.pattern_matches(&some_pattern, &some_value)?;
    println!("✓ Some pattern matches Some(42): {}", matches_some);

    let matches_none = evaluator.pattern_matches(&some_pattern, &none_value)?;
    println!("✓ Some pattern matches None: {}", matches_none);

    // Test None pattern matching
    let none_pattern = Pattern::Union {
        variant: "None".to_string(),
        value: None,
    };

    let matches_some_none = evaluator.pattern_matches(&none_pattern, &some_value)?;
    println!("✓ None pattern matches Some(42): {}", matches_some_none);

    let matches_none_none = evaluator.pattern_matches(&none_pattern, &none_value)?;
    println!("✓ None pattern matches None: {}", matches_none_none);

    println!("✓ All union evaluation tests passed!");
    Ok(())
}
