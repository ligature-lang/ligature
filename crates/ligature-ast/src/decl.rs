//! Declaration definitions for the Ligature language.

use crate::span::{Span, Spanned};
use crate::{Expr, Import, Type, TypeAlias, TypeConstructor};
use serde::{Deserialize, Serialize};

/// A Ligature declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Declaration {
    /// The kind of declaration.
    pub kind: DeclarationKind,
    /// Source location information.
    pub span: Span,
}

impl Spanned for Declaration {
    fn span(&self) -> Span {
        self.span
    }
}

/// The different kinds of declarations in Ligature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DeclarationKind {
    /// Value bindings.
    Value(ValueDeclaration),

    /// Type aliases.
    TypeAlias(TypeAlias),

    /// Type constructors.
    TypeConstructor(TypeConstructor),

    /// Module imports.
    Import(Import),

    /// Module exports.
    Export(ExportDeclaration),

    /// Type class definitions.
    TypeClass(TypeClassDeclaration),

    /// Type class instances.
    Instance(InstanceDeclaration),
}

/// A value declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueDeclaration {
    /// The name of the value.
    pub name: String,

    /// Optional type annotation.
    pub type_annotation: Option<Type>,

    /// The value expression.
    pub value: Expr,

    /// Whether this is a recursive declaration.
    pub is_recursive: bool,

    /// Source location.
    pub span: Span,
}

impl Spanned for ValueDeclaration {
    fn span(&self) -> Span {
        self.span
    }
}

/// An import declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImportDeclaration {
    /// The module path to import.
    pub path: String,

    /// Optional alias for the imported module.
    pub alias: Option<String>,

    /// Specific items to import (if None, imports everything).
    pub items: Option<Vec<ImportItem>>,

    /// Source location.
    pub span: Span,
}

impl Spanned for ImportDeclaration {
    fn span(&self) -> Span {
        self.span
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
        self.span
    }
}

/// An export declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExportDeclaration {
    /// The items being exported.
    pub items: Vec<ExportItem>,

    /// Source location.
    pub span: Span,
}

impl Spanned for ExportDeclaration {
    fn span(&self) -> Span {
        self.span
    }
}

/// An item being exported.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExportItem {
    /// The name of the item.
    pub name: String,

    /// Optional alias for the exported item.
    pub alias: Option<String>,

    /// Source location.
    pub span: Span,
}

impl Spanned for ExportItem {
    fn span(&self) -> Span {
        self.span
    }
}

/// A type class declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeClassDeclaration {
    /// The name of the type class.
    pub name: String,

    /// Type parameters.
    pub parameters: Vec<String>,

    /// Superclass constraints.
    pub superclasses: Vec<TypeClassConstraint>,

    /// Method signatures.
    pub methods: Vec<MethodSignature>,

    /// Source location.
    pub span: Span,
}

impl Spanned for TypeClassDeclaration {
    fn span(&self) -> Span {
        self.span
    }
}

/// A type class constraint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeClassConstraint {
    /// The type class name.
    pub class_name: String,

    /// The type arguments.
    pub type_arguments: Vec<Type>,

    /// Source location.
    pub span: Span,
}

impl Spanned for TypeClassConstraint {
    fn span(&self) -> Span {
        self.span
    }
}

/// A method signature in a type class.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MethodSignature {
    /// The method name.
    pub name: String,

    /// The method type.
    pub type_: Type,

    /// Source location.
    pub span: Span,
}

impl Spanned for MethodSignature {
    fn span(&self) -> Span {
        self.span
    }
}

/// An instance declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InstanceDeclaration {
    /// The type class name.
    pub class_name: String,

    /// The type arguments.
    pub type_arguments: Vec<Type>,

    /// Optional constraints for the instance.
    pub constraints: Option<Vec<TypeClassConstraint>>,

    /// Method implementations.
    pub methods: Vec<MethodImplementation>,

    /// Source location.
    pub span: Span,
}

impl Spanned for InstanceDeclaration {
    fn span(&self) -> Span {
        self.span
    }
}

/// A method implementation in an instance.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MethodImplementation {
    /// The method name.
    pub name: String,

    /// The method implementation.
    pub implementation: Expr,

    /// Source location.
    pub span: Span,
}

impl Spanned for MethodImplementation {
    fn span(&self) -> Span {
        self.span
    }
}

impl Declaration {
    /// Create a new declaration with the given kind and span.
    pub fn new(kind: DeclarationKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Create a value declaration.
    pub fn value(
        name: String,
        type_annotation: Option<Type>,
        value: Expr,
        is_recursive: bool,
        span: Span,
    ) -> Self {
        Self::new(
            DeclarationKind::Value(ValueDeclaration {
                name,
                type_annotation,
                value,
                is_recursive,
                span,
            }),
            span,
        )
    }

    /// Create a type alias declaration.
    pub fn type_alias(alias: TypeAlias) -> Self {
        let span = alias.span();
        Self::new(DeclarationKind::TypeAlias(alias), span)
    }

    /// Create a type constructor declaration.
    pub fn type_constructor(constructor: TypeConstructor) -> Self {
        let span = constructor.span();
        Self::new(DeclarationKind::TypeConstructor(constructor), span)
    }

    /// Create an import declaration.
    pub fn import(import: Import) -> Self {
        let span = import.span();
        Self::new(DeclarationKind::Import(import), span)
    }

    /// Create an export declaration.
    pub fn export(export: ExportDeclaration) -> Self {
        let span = export.span();
        Self::new(DeclarationKind::Export(export), span)
    }

    /// Create a type class declaration.
    pub fn type_class(class: TypeClassDeclaration) -> Self {
        let span = class.span();
        Self::new(DeclarationKind::TypeClass(class), span)
    }

    /// Create an instance declaration.
    pub fn instance(instance: InstanceDeclaration) -> Self {
        let span = instance.span();
        Self::new(DeclarationKind::Instance(instance), span)
    }

    /// Check if this is a value declaration.
    pub fn is_value(&self) -> bool {
        matches!(self.kind, DeclarationKind::Value(_))
    }

    /// Check if this is a type alias declaration.
    pub fn is_type_alias(&self) -> bool {
        matches!(self.kind, DeclarationKind::TypeAlias(_))
    }

    /// Check if this is a type constructor declaration.
    pub fn is_type_constructor(&self) -> bool {
        matches!(self.kind, DeclarationKind::TypeConstructor(_))
    }

    /// Check if this is an import declaration.
    pub fn is_import(&self) -> bool {
        matches!(self.kind, DeclarationKind::Import(_))
    }

    /// Check if this is an export declaration.
    pub fn is_export(&self) -> bool {
        matches!(self.kind, DeclarationKind::Export(_))
    }

    /// Check if this is a type class declaration.
    pub fn is_type_class(&self) -> bool {
        matches!(self.kind, DeclarationKind::TypeClass(_))
    }

    /// Check if this is an instance declaration.
    pub fn is_instance(&self) -> bool {
        matches!(self.kind, DeclarationKind::Instance(_))
    }

    /// Get the value declaration if this is one.
    pub fn as_value(&self) -> Option<&ValueDeclaration> {
        match &self.kind {
            DeclarationKind::Value(value) => Some(value),
            _ => None,
        }
    }

    /// Get the type alias if this is one.
    pub fn as_type_alias(&self) -> Option<&TypeAlias> {
        match &self.kind {
            DeclarationKind::TypeAlias(alias) => Some(alias),
            _ => None,
        }
    }

    /// Get the type constructor if this is one.
    pub fn as_type_constructor(&self) -> Option<&TypeConstructor> {
        match &self.kind {
            DeclarationKind::TypeConstructor(constructor) => Some(constructor),
            _ => None,
        }
    }

    /// Get the import declaration if this is one.
    pub fn as_import(&self) -> Option<&Import> {
        match &self.kind {
            DeclarationKind::Import(import) => Some(import),
            _ => None,
        }
    }

    /// Get the export declaration if this is one.
    pub fn as_export(&self) -> Option<&ExportDeclaration> {
        match &self.kind {
            DeclarationKind::Export(export) => Some(export),
            _ => None,
        }
    }

    /// Get the type class declaration if this is one.
    pub fn as_type_class(&self) -> Option<&TypeClassDeclaration> {
        match &self.kind {
            DeclarationKind::TypeClass(class) => Some(class),
            _ => None,
        }
    }

    /// Get the instance declaration if this is one.
    pub fn as_instance(&self) -> Option<&InstanceDeclaration> {
        match &self.kind {
            DeclarationKind::Instance(instance) => Some(instance),
            _ => None,
        }
    }
}
