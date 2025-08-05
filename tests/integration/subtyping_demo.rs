//! Subtyping and Error Reporting Demo
//! 
//! This file demonstrates the enhanced subtyping and error reporting features
//! that were implemented as part of the Medium Priority Type System Stabilization.

use ligature_parser::parse_program;
use ligature_types::type_check_program;

#[test]
fn demo_enhanced_subtyping() {
    println!("=== Enhanced Subtyping Demo ===");
    
    // 1. Record width subtyping (supertype has more fields)
    println!("\n1. Record Width Subtyping:");
    let program = parse_program(r#"
        let user = { name = "Alice", age = 30, email = "alice@example.com" };
        let basic_user: { name: String, age: Integer } = user;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ Record width subtyping works correctly"),
        Err(e) => println!("❌ Record width subtyping failed: {}", e),
    }

    // 2. Record depth subtyping (field types are in subtype relationship)
    println!("\n2. Record Depth Subtyping:");
    let program = parse_program(r#"
        let user = { name = "Alice", age = 30 };
        let flexible_user: { name: String, age: Float } = user;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ Record depth subtyping works correctly"),
        Err(e) => println!("❌ Record depth subtyping failed: {}", e),
    }

    // 3. Function subtyping (contravariant/covariant)
    println!("\n3. Function Subtyping:");
    let program = parse_program(r#"
        let add_int = \x y -> x + y;
        let add_number: Integer -> Integer -> Integer = add_int;
        let flexible_add: Float -> Float -> Float = add_number;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ Function subtyping works correctly"),
        Err(e) => println!("❌ Function subtyping failed: {}", e),
    }

    // 4. List subtyping
    println!("\n4. List Subtyping:");
    let program = parse_program(r#"
        let int_list = [1, 2, 3];
        let number_list: [Float] = int_list;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ List subtyping works correctly"),
        Err(e) => println!("❌ List subtyping failed: {}", e),
    }
}

#[test]
fn demo_enhanced_error_reporting() {
    println!("\n=== Enhanced Error Reporting Demo ===");
    
    // 1. Record subtyping error with detailed context
    println!("\n1. Record Subtyping Error:");
    let program = parse_program(r#"
        let user = { name = "Alice" };
        let full_user: { name: String, age: Integer, email: String } = user;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("❌ Expected error but got success"),
        Err(e) => {
            println!("✅ Record subtyping error caught:");
            println!("   Error: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("missing") || error_msg.contains("required field") {
                println!("   ✅ Error message includes helpful context");
            } else {
                println!("   ⚠️  Error message could be more specific");
            }
        }
    }

    // 2. Type mismatch with better error context
    println!("\n2. Type Mismatch Error:");
    let program = parse_program(r#"
        let x = 5 + "hello";
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("❌ Expected error but got success"),
        Err(e) => {
            println!("✅ Type mismatch error caught:");
            println!("   Error: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("type mismatch") || error_msg.contains("cannot unify") {
                println!("   ✅ Error message is clear and helpful");
            } else {
                println!("   ⚠️  Error message could be more specific");
            }
        }
    }

    // 3. Function application error
    println!("\n3. Function Application Error:");
    let program = parse_program(r#"
        let add = \x y -> x + y;
        let result = add 5 "hello";
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("❌ Expected error but got success"),
        Err(e) => {
            println!("✅ Function application error caught:");
            println!("   Error: {}", e);
            let error_msg = e.to_string();
            if error_msg.contains("function") || error_msg.contains("parameter") || error_msg.contains("argument") {
                println!("   ✅ Error message provides function context");
            } else {
                println!("   ⚠️  Error message could provide more context");
            }
        }
    }
}

#[test]
fn demo_complex_subtyping_scenarios() {
    println!("\n=== Complex Subtyping Scenarios Demo ===");
    
    // 1. Nested record subtyping
    println!("\n1. Nested Record Subtyping:");
    let program = parse_program(r#"
        let user = { 
            name = "Alice", 
            age = 30, 
            preferences = { theme = "dark", notifications = true }
        };
        let basic_user: { 
            name: String, 
            age: Float, 
            preferences: { theme: String } 
        } = user;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ Complex nested record subtyping works correctly"),
        Err(e) => println!("❌ Complex nested record subtyping failed: {}", e),
    }

    // 2. Function with record parameters
    println!("\n2. Function with Record Parameters:");
    let program = parse_program(r#"
        let process_user = \user -> user.name;
        let user = { name = "Alice", age = 30 };
        let result = process_user user;
        let flexible_process: { name: String, age: Float } -> String = process_user;
    "#).unwrap();
    
    match type_check_program(&program) {
        Ok(_) => println!("✅ Function with record parameters works correctly"),
        Err(e) => println!("❌ Function with record parameters failed: {}", e),
    }
} 