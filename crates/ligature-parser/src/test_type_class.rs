use ligature_parser::grammar::LigatureParser;

use pest::Parser as PestParser;

fn main() {
    // Test if the grammar compiles by parsing a simple program
    let simple_program = "let x = 1;";
    match LigatureParser::parse(ligature_parser::grammar::Rule::program, simple_program) {
        Ok(pairs) => {
            println!("✅ Simple program parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!("❌ Simple program failed: {e}");
        }
    }

    // Test if the grammar compiles by parsing a simple identifier
    let identifier_source = "Eq";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::identifier,
        identifier_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'identifier' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!("❌ 'identifier' failed: {e}");
        }
    }

    // Test parsing "instance Eq Int where" with the correct rule
    let instance_eq_int_where_source = "instance Eq Int where";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::instance_declaration_with_args,
        instance_eq_int_where_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'instance_declaration_with_args with Int where' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!(
                "❌ 'instance_declaration_with_args with Int where' failed: {e}",
            );
        }
    }

    // Test parsing "instance Eq where" with the correct rule
    let instance_eq_where_source = "instance Eq where";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::instance_declaration_no_args,
        instance_eq_where_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'instance_declaration_no_args without args where' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!(
                "❌ 'instance_declaration_no_args without args where' failed: {e}",
            );
        }
    }

    // Test parsing a method implementation in isolation
    let method_impl_source = "eq = \\x y -> x == y;";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::method_implementation,
        method_impl_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'method_implementation' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!("❌ 'method_implementation' failed: {e}");
        }
    }

    // Test parsing a complete instance declaration with method implementation
    let complete_instance_source = "instance Eq Int where eq = \\x y -> x == y;";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::instance_declaration_with_args,
        complete_instance_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'complete instance declaration' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!("❌ 'complete instance declaration' failed: {e}");
        }
    }

    // Test the type_argument rule in isolation
    let type_arg_source = "Int";
    match LigatureParser::parse(
        ligature_parser::grammar::Rule::type_argument,
        type_arg_source,
    ) {
        Ok(pairs) => {
            println!("✅ 'type_argument' parsed successfully!");
            println!("Parse tree: {pairs:#?}");
        }
        Err(e) => {
            println!("❌ 'type_argument' failed: {e}");
        }
    }
}
