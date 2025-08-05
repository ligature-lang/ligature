use ligature_parser::grammar::{LigatureParser, Rule};
use pest::Parser as PestParser;

fn main() {
    // Test what pest is actually parsing
    let result = LigatureParser::parse(Rule::expression, "if x > 0 then x else 0");
    match result {
        Ok(pairs) => {
            println!("Pest expression parsing successful:");
            for pair in pairs {
                println!("Rule: {:?}, Content: '{}'", pair.as_rule(), pair.as_str());
                for inner in pair.into_inner() {
                    println!(
                        "  Inner Rule: {:?}, Content: '{}'",
                        inner.as_rule(),
                        inner.as_str()
                    );
                    for deeper in inner.into_inner() {
                        println!(
                            "    Deeper Rule: {:?}, Content: '{}'",
                            deeper.as_rule(),
                            deeper.as_str()
                        );
                        for even_deeper in deeper.into_inner() {
                            println!(
                                "      Even Deeper Rule: {:?}, Content: '{}'",
                                even_deeper.as_rule(),
                                even_deeper.as_str()
                            );
                        }
                    }
                }
            }
        }
        Err(e) => {
            println!("Pest expression parsing failed: {:?}", e);
        }
    }

    // Test what pest is actually parsing for if expression
    let result = LigatureParser::parse(Rule::if_expression, "if x > 0 then x else 0");
    match result {
        Ok(pairs) => {
            println!("Pest if_expression parsing successful:");
            for pair in pairs {
                println!("Rule: {:?}, Content: '{}'", pair.as_rule(), pair.as_str());
                for inner in pair.into_inner() {
                    println!(
                        "  Inner Rule: {:?}, Content: '{}'",
                        inner.as_rule(),
                        inner.as_str()
                    );
                }
            }
        }
        Err(e) => {
            println!("Pest if_expression parsing failed: {:?}", e);
        }
    }
}
