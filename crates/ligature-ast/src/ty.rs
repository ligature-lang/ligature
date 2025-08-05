//! Type definitions for the Ligature language.

use crate::decl::TypeClassConstraint;
use crate::span::{Span, Spanned};
use serde::{Deserialize, Serialize};

/// A Ligature type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Type {
    /// The kind of type.
    pub kind: TypeKind,
    /// Source location information.
    pub span: Span,
}

impl Spanned for Type {
    fn span(&self) -> Span {
        self.span
    }
}

/// The different kinds of types in Ligature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeKind {
    /// Unit type ().
    Unit,

    /// Boolean type.
    Bool,

    /// String type.
    String,

    /// Integer type.
    Integer,

    /// Floating-point type.
    Float,

    /// Type variable (for polymorphism).
    Variable(String),

    /// Function type.
    Function {
        parameter: Box<Type>,
        return_type: Box<Type>,
    },

    /// Record type.
    Record { fields: Vec<TypeField> },

    /// Union type (sum type).
    Union { variants: Vec<TypeVariant> },

    /// List type.
    List(Box<Type>),

    /// Universal quantification (forall).
    ForAll { parameter: String, body: Box<Type> },

    /// Existential quantification (exists).
    Exists { parameter: String, body: Box<Type> },

    /// Dependent function type (Pi type).
    Pi {
        parameter: String,
        parameter_type: Box<Type>,
        return_type: Box<Type>,
    },

    /// Dependent pair type (Sigma type).
    Sigma {
        parameter: String,
        parameter_type: Box<Type>,
        return_type: Box<Type>,
    },

    /// Type application.
    Application {
        function: Box<Type>,
        argument: Box<Type>,
    },

    /// Module type.
    Module { name: String },

    /// Constrained type (type class constraint).
    Constrained {
        constraint: Box<TypeClassConstraint>,
        type_: Box<Type>,
    },
}

/// A field in a record type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeField {
    /// Field name.
    pub name: String,
    /// Field type.
    pub type_: Type,
    /// Source location.
    pub span: Span,
}

impl Spanned for TypeField {
    fn span(&self) -> Span {
        self.span
    }
}

/// A variant in a union type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeVariant {
    /// Variant name.
    pub name: String,
    /// Optional associated type.
    pub type_: Option<Type>,
    /// Source location.
    pub span: Span,
}

impl Spanned for TypeVariant {
    fn span(&self) -> Span {
        self.span
    }
}

/// Type constructor for creating new types.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeConstructor {
    /// Constructor name.
    pub name: String,
    /// Type parameters.
    pub parameters: Vec<String>,
    /// Constructor body.
    pub body: Type,
    /// Source location.
    pub span: Span,
}

impl Spanned for TypeConstructor {
    fn span(&self) -> Span {
        self.span
    }
}

/// Type alias for creating type synonyms.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeAlias {
    /// Alias name.
    pub name: String,
    /// Type parameters.
    pub parameters: Vec<String>,
    /// The type being aliased.
    pub type_: Type,
    /// Source location.
    pub span: Span,
}

impl Spanned for TypeAlias {
    fn span(&self) -> Span {
        self.span
    }
}

impl Type {
    /// Create a new type with the given kind and span.
    pub fn new(kind: TypeKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Create a unit type.
    pub fn unit(span: Span) -> Self {
        Self::new(TypeKind::Unit, span)
    }

    /// Create a boolean type.
    pub fn bool(span: Span) -> Self {
        Self::new(TypeKind::Bool, span)
    }

    /// Create a string type.
    pub fn string(span: Span) -> Self {
        Self::new(TypeKind::String, span)
    }

    /// Create an integer type.
    pub fn integer(span: Span) -> Self {
        Self::new(TypeKind::Integer, span)
    }

    /// Create a float type.
    pub fn float(span: Span) -> Self {
        Self::new(TypeKind::Float, span)
    }

    /// Create a type variable.
    pub fn variable(name: String, span: Span) -> Self {
        Self::new(TypeKind::Variable(name), span)
    }

    /// Create a function type.
    pub fn function(parameter: Type, return_type: Type, span: Span) -> Self {
        Self::new(
            TypeKind::Function {
                parameter: Box::new(parameter),
                return_type: Box::new(return_type),
            },
            span,
        )
    }

    /// Create a record type.
    pub fn record(fields: Vec<TypeField>, span: Span) -> Self {
        Self::new(TypeKind::Record { fields }, span)
    }

    /// Create a union type.
    pub fn union(variants: Vec<TypeVariant>, span: Span) -> Self {
        Self::new(TypeKind::Union { variants }, span)
    }

    /// Create a list type.
    pub fn list(element_type: Type, span: Span) -> Self {
        Self::new(TypeKind::List(Box::new(element_type)), span)
    }

    /// Create a module type.
    pub fn module(name: String, span: Span) -> Self {
        Self::new(TypeKind::Module { name }, span)
    }

    /// Check if this type is a function type.
    pub fn is_function(&self) -> bool {
        matches!(self.kind, TypeKind::Function { .. })
    }

    /// Check if this type is a record type.
    pub fn is_record(&self) -> bool {
        matches!(self.kind, TypeKind::Record { .. })
    }

    /// Check if this type is a union type.
    pub fn is_union(&self) -> bool {
        matches!(self.kind, TypeKind::Union { .. })
    }

    /// Check if this type is a list type.
    pub fn is_list(&self) -> bool {
        matches!(self.kind, TypeKind::List(_))
    }

    /// Check if this type is a type variable.
    pub fn is_variable(&self) -> bool {
        matches!(self.kind, TypeKind::Variable(_))
    }

    /// Check if this type is a module type.
    pub fn is_module(&self) -> bool {
        matches!(self.kind, TypeKind::Module { .. })
    }

    /// Get the name if this is a type variable.
    pub fn as_variable(&self) -> Option<&str> {
        match &self.kind {
            TypeKind::Variable(name) => Some(name),
            _ => None,
        }
    }

    /// Get the parameter and return type if this is a function type.
    pub fn as_function(&self) -> Option<(&Type, &Type)> {
        match &self.kind {
            TypeKind::Function {
                parameter,
                return_type,
            } => Some((parameter, return_type)),
            _ => None,
        }
    }

    /// Get the element type if this is a list type.
    pub fn as_list(&self) -> Option<&Type> {
        match &self.kind {
            TypeKind::List(element_type) => Some(element_type),
            _ => None,
        }
    }

    /// Get the fields if this is a record type.
    pub fn as_record(&self) -> Option<&[TypeField]> {
        match &self.kind {
            TypeKind::Record { fields } => Some(fields),
            _ => None,
        }
    }

    /// Get the variants if this is a union type.
    pub fn as_union(&self) -> Option<&[TypeVariant]> {
        match &self.kind {
            TypeKind::Union { variants } => Some(variants),
            _ => None,
        }
    }
}
