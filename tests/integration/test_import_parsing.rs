use ligature_parser::Parser;
use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut parser = Parser::new();
    
    // Read the test file
    let source = fs::read_to_string("registers/_scratch/test_selective_imports.lig")?;
    
    println!("Testing selective import parsing...");
    println!("Source:\n{}", source);
    
    // Try to parse the module
    match parser.parse_module(&source) {
        Ok(module) => {
            println!("✓ Module parsed successfully!");
            println!("  - Module name: {}", module.name);
            println!("  - Imports: {}", module.imports.len());
            
            for (i, import) in module.imports.iter().enumerate() {
                println!("  Import {}: path='{}', alias='{:?}', items='{:?}'", 
                    i, import.path, import.alias, import.items);
            }
            
            println!("  - Declarations: {}", module.declarations.len());
        }
        Err(e) => {
            println!("✗ Parse error: {:?}", e);
            return Err(Box::new(e));
        }
    }
    
    Ok(())
} 