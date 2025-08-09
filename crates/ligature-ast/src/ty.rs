//! Type definitions for the Ligature language.

use serde::{Deserialize, Serialize};

use crate::Expr;
use crate::span::{Span, Spanned};

// Type aliases for common type components
pub type RefinementComponents<'a> = (&'a Type, &'a Expr, &'a Option<String>);
pub type ConstraintTypeComponents<'a> = (&'a Type, &'a [Constraint]);

/// Constraints that can be applied to types.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constraint {
    /// Value constraint: expression must be true
    ValueConstraint(Box<Expr>),

    /// Range constraint: value must be in range
    RangeConstraint {
        min: Option<Box<Expr>>,
        max: Option<Box<Expr>>,
        inclusive: bool,
    },

    /// Pattern constraint: value must match pattern
    PatternConstraint { pattern: String, regex: bool },

    /// Custom constraint: user-defined validation function
    CustomConstraint {
        function: String,
        arguments: Vec<Box<Expr>>,
    },

    /// Cross-field constraint: depends on multiple fields
    CrossFieldConstraint {
        fields: Vec<String>,
        predicate: Box<Expr>,
    },
}

/// A Ligature type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Type {
    /// The kind of type.
    pub kind: TypeKind,
    /// Source location information.
    pub span: Span,
}

impl Spanned for Type {
    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// The different kinds of types in Ligature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
        constraint: Box<crate::decl::TypeClassConstraint>,
        type_: Box<Type>,
    },

    /// Refinement type: base_type where predicate
    Refinement {
        base_type: Box<Type>,
        predicate: Box<Expr>,
        predicate_name: Option<String>,
    },

    /// Constraint type: type with additional constraints
    ConstraintType {
        base_type: Box<Type>,
        constraints: Vec<Constraint>,
    },
}

/// A field in a record type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
        self.span.clone()
    }
}

/// A variant in a union type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
        self.span.clone()
    }
}

/// A type constructor.
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
        self.span.clone()
    }
}

/// A type alias.
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
        self.span.clone()
    }
}

// Convenience methods for creating types
impl Type {
    /// Create a new type.
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

    /// Create a refinement type.
    pub fn refinement(
        base_type: Type,
        predicate: Expr,
        predicate_name: Option<String>,
        span: Span,
    ) -> Self {
        Self::new(
            TypeKind::Refinement {
                base_type: Box::new(base_type),
                predicate: Box::new(predicate),
                predicate_name,
            },
            span,
        )
    }

    /// Create a constraint type.
    pub fn constraint_type(base_type: Type, constraints: Vec<Constraint>, span: Span) -> Self {
        Self::new(
            TypeKind::ConstraintType {
                base_type: Box::new(base_type),
                constraints,
            },
            span,
        )
    }

    /// Check if this is a function type.
    pub fn is_function(&self) -> bool {
        matches!(self.kind, TypeKind::Function { .. })
    }

    /// Check if this is a record type.
    pub fn is_record(&self) -> bool {
        matches!(self.kind, TypeKind::Record { .. })
    }

    /// Check if this is a union type.
    pub fn is_union(&self) -> bool {
        matches!(self.kind, TypeKind::Union { .. })
    }

    /// Check if this is a list type.
    pub fn is_list(&self) -> bool {
        matches!(self.kind, TypeKind::List(_))
    }

    /// Check if this is a type variable.
    pub fn is_variable(&self) -> bool {
        matches!(self.kind, TypeKind::Variable(_))
    }

    /// Check if this is a module type.
    pub fn is_module(&self) -> bool {
        matches!(self.kind, TypeKind::Module { .. })
    }

    /// Check if this is a refinement type.
    pub fn is_refinement(&self) -> bool {
        matches!(self.kind, TypeKind::Refinement { .. })
    }

    /// Check if this is a constraint type.
    pub fn is_constraint_type(&self) -> bool {
        matches!(self.kind, TypeKind::ConstraintType { .. })
    }

    /// Get the variable name if this is a type variable.
    pub fn as_variable(&self) -> Option<&str> {
        match &self.kind {
            TypeKind::Variable(name) => Some(name),
            _ => None,
        }
    }

    /// Get the parameter and return types if this is a function type.
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

    /// Get the refinement components if this is a refinement type.
    pub fn as_refinement(&self) -> Option<RefinementComponents<'_>> {
        match &self.kind {
            TypeKind::Refinement {
                base_type,
                predicate,
                predicate_name,
            } => Some((base_type, predicate, predicate_name)),
            _ => None,
        }
    }

    /// Get the constraint type components if this is a constraint type.
    pub fn as_constraint_type(&self) -> Option<ConstraintTypeComponents<'_>> {
        match &self.kind {
            TypeKind::ConstraintType {
                base_type,
                constraints,
            } => Some((base_type, constraints)),
            _ => None,
        }
    }
}
