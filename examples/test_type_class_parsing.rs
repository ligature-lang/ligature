use ligature_parser::parse_program;

fn main() {
    let source = r#"
        typeclass Eq 'a where
            eq : 'a -> 'a -> Bool;
    "#;
    
    match parse_program(source) {
        Ok(program) => {
            println!("✅ Parsing successful!");
            println!("Declarations: {}", program.declarations.len());
            for decl in &program.declarations {
                println!("Declaration: {decl:?}");
            }
        }
        Err(e) => {
            println!("❌ Parsing failed: {}", e);
        }
    }
} 