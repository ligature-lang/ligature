//! Expression definitions for the Ligature language.

use crate::span::{Span, Spanned};
use crate::Type;
use serde::{Deserialize, Serialize};

/// A Ligature expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    /// The kind of expression.
    pub kind: ExprKind,
    /// Source location information.
    pub span: Span,
}

impl Spanned for Expr {
    fn span(&self) -> Span {
        self.span
    }
}

/// The different kinds of expressions in Ligature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExprKind {
    /// Literal values.
    Literal(Literal),

    /// Variable references.
    Variable(String),

    /// Function application.
    Application {
        function: Box<Expr>,
        argument: Box<Expr>,
    },

    /// Function abstraction (lambda).
    Abstraction {
        parameter: String,
        parameter_type: Option<Box<Type>>,
        body: Box<Expr>,
    },

    /// Let bindings.
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },

    /// Record construction.
    Record { fields: Vec<RecordField> },

    /// Record field access.
    FieldAccess { record: Box<Expr>, field: String },

    /// Union construction.
    Union {
        variant: String,
        value: Option<Box<Expr>>,
    },

    /// Pattern matching (case expressions).
    Match {
        scrutinee: Box<Expr>,
        cases: Vec<MatchCase>,
    },

    /// Conditional expressions.
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    /// Binary operations.
    BinaryOp {
        operator: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// Unary operations.
    UnaryOp {
        operator: UnaryOperator,
        operand: Box<Expr>,
    },

    /// Type annotations.
    Annotated {
        expression: Box<Expr>,
        type_annotation: Box<Type>,
    },
}

/// Literal values in Ligature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Literal {
    /// String literals.
    String(String),

    /// Integer literals.
    Integer(i64),

    /// Floating-point literals.
    Float(f64),

    /// Boolean literals.
    Boolean(bool),

    /// Unit value.
    Unit,

    /// List literals.
    List(Vec<Expr>),
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOperator {
    // Arithmetic
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,

    // Comparison
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,

    // Logical
    And,
    Or,

    // String
    Concat,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOperator {
    Not,
    Negate,
}

/// A record field.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RecordField {
    /// Field name.
    pub name: String,
    /// Field value.
    pub value: Expr,
    /// Source location.
    pub span: Span,
}

impl Spanned for RecordField {
    fn span(&self) -> Span {
        self.span
    }
}

/// A match case in a pattern matching expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MatchCase {
    /// Pattern to match against.
    pub pattern: Pattern,
    /// Optional guard condition (when clause).
    pub guard: Option<Expr>,
    /// Expression to evaluate if pattern matches.
    pub expression: Expr,
    /// Source location.
    pub span: Span,
}

impl Spanned for MatchCase {
    fn span(&self) -> Span {
        self.span
    }
}

/// Patterns for pattern matching.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern {
    /// Wildcard pattern (matches anything).
    Wildcard,

    /// Variable pattern (binds to variable).
    Variable(String),

    /// Literal pattern.
    Literal(Literal),

    /// Record pattern.
    Record { fields: Vec<RecordPatternField> },

    /// Union variant pattern.
    Union {
        variant: String,
        value: Option<Box<Pattern>>,
    },

    /// List pattern.
    List { elements: Vec<Pattern> },
}

/// A field in a record pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RecordPatternField {
    /// Field name.
    pub name: String,
    /// Pattern for the field value.
    pub pattern: Pattern,
    /// Source location.
    pub span: Span,
}

impl Spanned for RecordPatternField {
    fn span(&self) -> Span {
        self.span
    }
}
