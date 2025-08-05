//! Error types for the Ligature parser.

use ligature_ast::{AstError, Span};
use thiserror::Error;

/// Errors that can occur during parsing.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    #[error("Syntax error: {message}")]
    SyntaxError { message: String, span: Span },

    #[error("Unexpected token: {token}")]
    UnexpectedToken { token: String, span: Span },

    #[error("Expected token: {expected}, found: {found}")]
    ExpectedToken {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Invalid literal: {literal}")]
    InvalidLiteral { literal: String, span: Span },

    #[error("Invalid identifier: {identifier}")]
    InvalidIdentifier { identifier: String, span: Span },

    #[error("Unterminated string literal")]
    UnterminatedString { span: Span },

    #[error("Unterminated comment")]
    UnterminatedComment { span: Span },

    #[error("Invalid escape sequence: {sequence}")]
    InvalidEscapeSequence { sequence: String, span: Span },

    #[error("Parser internal error: {message}")]
    InternalError { message: String, span: Span },
}

impl ParserError {
    /// Get the span associated with this error.
    pub fn span(&self) -> Span {
        match self {
            ParserError::SyntaxError { span, .. } => *span,
            ParserError::UnexpectedToken { span, .. } => *span,
            ParserError::ExpectedToken { span, .. } => *span,
            ParserError::InvalidLiteral { span, .. } => *span,
            ParserError::InvalidIdentifier { span, .. } => *span,
            ParserError::UnterminatedString { span } => *span,
            ParserError::UnterminatedComment { span } => *span,
            ParserError::InvalidEscapeSequence { span, .. } => *span,
            ParserError::InternalError { span, .. } => *span,
        }
    }

    /// Convert to an AST error.
    pub fn into_ast_error(self) -> AstError {
        match self {
            ParserError::SyntaxError { message, span } => AstError::ParseError { message, span },
            ParserError::UnexpectedToken { token, span } => AstError::ParseError {
                message: format!("Unexpected token: {token}"),
                span,
            },
            ParserError::ExpectedToken {
                expected,
                found,
                span,
            } => AstError::ParseError {
                message: format!("Expected {expected}, found {found}"),
                span,
            },
            ParserError::InvalidLiteral { literal, span } => AstError::ParseError {
                message: format!("Invalid literal: {literal}"),
                span,
            },
            ParserError::InvalidIdentifier { identifier, span } => AstError::InvalidIdentifier {
                name: identifier,
                span,
            },
            ParserError::UnterminatedString { span } => AstError::ParseError {
                message: "Unterminated string literal".to_string(),
                span,
            },
            ParserError::UnterminatedComment { span } => AstError::ParseError {
                message: "Unterminated comment".to_string(),
                span,
            },
            ParserError::InvalidEscapeSequence { sequence, span } => AstError::ParseError {
                message: format!("Invalid escape sequence: {sequence}"),
                span,
            },
            ParserError::InternalError { message, span } => {
                AstError::InternalError { message, span }
            }
        }
    }
}

impl From<ParserError> for AstError {
    fn from(error: ParserError) -> Self {
        error.into_ast_error()
    }
}
