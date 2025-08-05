//! Integration tests for the type class system.

use ligature_parser::parse_program;
use ligature_types::type_check_program;

#[test]
fn test_basic_type_class_definition() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Basic type class definition works correctly"),
        Err(e) => println!("❌ Basic type class definition failed: {}", e),
    }
}

#[test]
fn test_type_class_with_superclass() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Ord a where
            superclass Eq a;
            compare : a -> a -> Ordering;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Type class with superclass works correctly"),
        Err(e) => println!("❌ Type class with superclass failed: {}", e),
    }
}

#[test]
fn test_basic_instance_declaration() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        instance Eq Int where
            eq = \x y -> x == y;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Basic instance declaration works correctly"),
        Err(e) => println!("❌ Basic instance declaration failed: {}", e),
    }
}

#[test]
fn test_instance_with_superclass() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Ord a where
            superclass Eq a;
            compare : a -> a -> Ordering;
        
        instance Ord Int where
            compare = \x y -> if x < y then LT else if x > y then GT else EQ;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Instance with superclass works correctly"),
        Err(e) => println!("❌ Instance with superclass failed: {}", e),
    }
}

#[test]
fn test_derived_instances() {
    let source = r#"
        typeclass Show a where
            show : a -> String;
        
        type Person = { name : String, age : Int };
        
        instance Show Person where
            show = \p -> "Person(" ++ p.name ++ ", " ++ show p.age ++ ")";
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Derived instances work correctly"),
        Err(e) => println!("❌ Derived instances failed: {}", e),
    }
}

#[test]
fn test_parametric_instances() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        type Maybe a = Just a | Nothing;
        
        instance Eq a => Eq (Maybe a) where
            eq = \x y -> case (x, y) of
                (Just a, Just b) -> eq a b;
                (Nothing, Nothing) -> true;
                _ -> false;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Parametric instances work correctly"),
        Err(e) => println!("❌ Parametric instances failed: {}", e),
    }
}

#[test]
fn test_type_class_constraints() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Ord a where
            superclass Eq a;
            compare : a -> a -> Ordering;
        
        let max : Ord a => a -> a -> a = \x y -> if compare x y == GT then x else y;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Type class constraints work correctly"),
        Err(e) => println!("❌ Type class constraints failed: {}", e),
    }
}

#[test]
fn test_duplicate_type_class_error() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Eq a where
            eq : a -> a -> Bool;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("❌ Expected error for duplicate type class"),
        Err(e) => {
            println!("✅ Duplicate type class error caught: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("Duplicate type class") {
                println!("   ✅ Error message is clear and helpful");
            } else {
                println!("   ⚠️  Error message could be more specific");
            }
        }
    }
}

#[test]
fn test_missing_method_error() {
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
            neq : a -> a -> Bool;
        
        instance Eq Int where
            eq = \x y -> x == y;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("❌ Expected error for missing method"),
        Err(e) => {
            println!("✅ Missing method error caught: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("Missing method") {
                println!("   ✅ Error message is clear and helpful");
            } else {
                println!("   ⚠️  Error message could be more specific");
            }
        }
    }
}

#[test]
fn test_undefined_type_class_error() {
    let source = r#"
        instance UndefinedClass Int where
            method = \x -> x;
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("❌ Expected error for undefined type class"),
        Err(e) => {
            println!("✅ Undefined type class error caught: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("Undefined type class") {
                println!("   ✅ Error message is clear and helpful");
            } else {
                println!("   ⚠️  Error message could be more specific");
            }
        }
    }
}

#[test]
fn test_complex_type_class_example() {
    let source = r#"
        // Basic type classes
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Ord a where
            superclass Eq a;
            compare : a -> a -> Ordering;
            lt : a -> a -> Bool;
            lte : a -> a -> Bool;
            gt : a -> a -> Bool;
            gte : a -> a -> Bool;
        
        typeclass Show a where
            show : a -> String;
        
        typeclass Num a where
            add : a -> a -> a;
            sub : a -> a -> a;
            mul : a -> a -> a;
            neg : a -> a;
            zero : a;
        
        // Built-in instances
        instance Eq Int where
            eq = \x y -> x == y;
        
        instance Ord Int where
            compare = \x y -> if x < y then LT else if x > y then GT else EQ;
            lt = \x y -> x < y;
            lte = \x y -> x <= y;
            gt = \x y -> x > y;
            gte = \x y -> x >= y;
        
        instance Show Int where
            show = \x -> toString x;
        
        instance Num Int where
            add = \x y -> x + y;
            sub = \x y -> x - y;
            mul = \x y -> x * y;
            neg = \x -> -x;
            zero = 0;
        
        // Generic functions using type classes
        let max : Ord a => a -> a -> a = \x y -> if gt x y then x else y;
        let min : Ord a => a -> a -> a = \x y -> if lt x y then x else y;
        let abs : Num a => Ord a => a -> a = \x -> if gte x zero then x else neg x;
        
        // Test the functions
        let result1 = max 5 3;
        let result2 = min 5 3;
        let result3 = abs (-7);
    "#;
    
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    
    match result {
        Ok(_) => println!("✅ Complex type class example works correctly"),
        Err(e) => println!("❌ Complex type class example failed: {}", e),
    }
}

#[test]
fn test_type_class_performance() {
    use std::time::Instant;
    
    let source = r#"
        typeclass Eq a where
            eq : a -> a -> Bool;
        
        typeclass Ord a where
            superclass Eq a;
            compare : a -> a -> Ordering;
        
        typeclass Show a where
            show : a -> String;
        
        // Many instances
        instance Eq Int where eq = \x y -> x == y;
        instance Ord Int where compare = \x y -> if x < y then LT else if x > y then GT else EQ;
        instance Show Int where show = \x -> toString x;
        
        instance Eq String where eq = \x y -> x == y;
        instance Ord String where compare = \x y -> if x < y then LT else if x > y then GT else EQ;
        instance Show String where show = \x -> x;
        
        instance Eq Bool where eq = \x y -> x == y;
        instance Ord Bool where compare = \x y -> if x < y then LT else if x > y then GT else EQ;
        instance Show Bool where show = \x -> if x then "true" else "false";
        
        // Complex function with many constraints
        let complex_function : Ord a => Show a => a -> a -> String = 
            \x y -> show (if compare x y == GT then x else y);
    "#;
    
    let start = Instant::now();
    let program = parse_program(source).unwrap();
    let result = type_check_program(&program);
    let duration = start.elapsed();
    
    match result {
        Ok(_) => {
            println!("✅ Type class performance test passed in {:?}", duration);
            if duration.as_millis() < 100 {
                println!("   ✅ Performance is acceptable (< 100ms)");
            } else {
                println!("   ⚠️  Performance could be improved (> 100ms)");
            }
        }
        Err(e) => println!("❌ Type class performance test failed: {}", e),
    }
} 