use ligature_parser::parse_program;
use embouchure_checker::type_check_program;
use ligature_types::TypeInference;
use ligature_ast::{Type, TypeKind, TypeVariant, Span};

fn main() {
    // Test the simple case
    let source = r#"
        type Option = Some Integer | None;
        
        let none_value = None;
    "#;
    
    let program = parse_program(source).unwrap();
    println!("Parsed program successfully");
    
    let mut inference = TypeInference::new();
    
    // Process the type alias first
    for declaration in &program.declarations {
        match &declaration.kind {
            ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                println!("Processing type alias: {}", type_alias.name);
                inference.check_type(&type_alias.type_)?;
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
                        println!("Binding {} as value with type: {variant.name, type_alias.type_:?}");
                        inference.bind(variant.name.clone(), type_alias.type_.clone());
                    }
                }
            }
            _ => {}
        }
    }
    
    // Now check if None is bound
    println!("Checking if None is bound...");
    match inference.environment.lookup("None") {
        Some(ty) => println!("None is bound with type: {ty:?}"),
        None => println!("None is NOT bound!"),
    }
    
    // Try to type check the program
    let result = type_check_program(&program);
    println!("Type check result: {result:?}");
} 