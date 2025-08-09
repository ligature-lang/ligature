// Copyright 2024 Ligature Language Team
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Abstract Syntax Tree (AST) for the Ligature language.
//!
//! This crate defines the AST structures used throughout the Ligature compiler,
//! including expressions, declarations, types, and error handling.

use serde::{Deserialize, Serialize};

pub mod decl;
pub mod error;
pub mod error_utils;
pub mod expr;
pub mod span;
pub mod ty;

// Re-export main types
pub use decl::{
    Declaration, DeclarationKind, ExportDeclaration, ExportItem, ImportDeclaration,
    InstanceDeclaration, MethodImplementation, MethodSignature, TypeClassConstraint,
    TypeClassDeclaration, ValueDeclaration,
};
// Re-export for backward compatibility
pub use error::LigatureResult as Result;
pub use error::{AstError, AstResult, ErrorCode, ErrorCollection, LigatureError, LigatureResult};
pub use error_utils::{
    EnhancedErrorReporter, ErrorCategory, ErrorContext, ErrorRecovery, ErrorReportConfig,
    RecoveryStrategy, error_with_context, error_with_context_and_suggestions,
    error_with_suggestions, get_error_category, get_error_code,
};
pub use expr::{
    BinaryOperator, Expr, ExprKind, Literal, MatchCase, Pattern, RecordField, RecordPatternField,
    UnaryOperator,
};
pub use span::{Span, Spanned};
pub use ty::{Type, TypeAlias, TypeConstructor, TypeField, TypeKind, TypeVariant};

/// A complete Ligature program or module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Program {
    /// The declarations in this program.
    pub declarations: Vec<Declaration>,
}

impl Program {
    /// Create a new empty program.
    pub fn new() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }

    /// Create a program with the given declarations.
    pub fn with_declarations(declarations: Vec<Declaration>) -> Self {
        Self { declarations }
    }

    /// Add a declaration to this program.
    pub fn add_declaration(&mut self, declaration: Declaration) {
        self.declarations.push(declaration);
    }

    /// Get the number of declarations in this program.
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Check if this program is empty.
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

/// Import information.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Import {
    /// The module path to import.
    pub path: String,
    /// Optional alias for the imported module.
    pub alias: Option<String>,
    /// Specific items to import (if None, imports everything).
    pub items: Option<Vec<ImportItem>>,
    /// Source location.
    pub span: Span,
}

impl Spanned for Import {
    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// An item being imported.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImportItem {
    /// The name of the item.
    pub name: String,
    /// Optional alias for the imported item.
    pub alias: Option<String>,
    /// Source location.
    pub span: Span,
}

impl Spanned for ImportItem {
    fn span(&self) -> Span {
        self.span.clone()
    }
}
