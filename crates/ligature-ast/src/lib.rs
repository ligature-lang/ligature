//! Abstract Syntax Tree definitions for the Ligature language.
//!
//! This crate defines the core data structures that represent Ligature programs
//! after parsing, including expressions, types, declarations, and metadata.

pub mod decl;
pub mod error;
pub mod expr;
pub mod span;
pub mod ty;

pub use decl::*;
pub use error::*;
pub use expr::*;
pub use span::*;
pub use ty::{Type, TypeAlias, TypeConstructor, TypeField, TypeKind, TypeVariant};

/// A complete Ligature program or module.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Program {
    /// The declarations in this program/module.
    pub declarations: Vec<Declaration>,
    /// Source location information.
    pub span: Span,
}

/// A Ligature module with imports and exports.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Module {
    /// Module name/path.
    pub name: String,
    /// Import statements.
    pub imports: Vec<Import>,
    /// The declarations in this module.
    pub declarations: Vec<Declaration>,
    /// Source location information.
    pub span: Span,
}

/// An import statement.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Import {
    /// The module path being imported.
    pub path: String,
    /// Optional alias for the imported module.
    pub alias: Option<String>,
    /// Optional list of specific items to import.
    /// If None, imports all exported items.
    pub items: Option<Vec<ImportItem>>,
    /// Source location information.
    pub span: Span,
}

/// An item being imported from a module.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ImportItem {
    /// The name of the item to import.
    pub name: String,
    /// Optional alias for the imported item.
    pub alias: Option<String>,
    /// Source location information.
    pub span: Span,
}

impl Spanned for Import {
    fn span(&self) -> Span {
        self.span
    }
}
