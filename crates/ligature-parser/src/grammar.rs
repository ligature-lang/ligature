//! Generated grammar for the Ligature language.

use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "../../grammar.pest"]
pub struct LigatureParser;

// Re-export the pest-generated Rule enum
pub use pest::iterators::{Pair, Pairs};
