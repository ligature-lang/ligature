//! Error types for the Ligature parser.

use ligature_ast::{ErrorCode, LigatureError, Span};
use ligature_error::{StandardError, StandardResult};
use thiserror::Error;

/// Main result type for parser operations using standardized error handling.
pub type ParserResult<T> = StandardResult<T>;

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
            ParserError::SyntaxError { span, .. } => span.clone(),
            ParserError::UnexpectedToken { span, .. } => span.clone(),
            ParserError::ExpectedToken { span, .. } => span.clone(),
            ParserError::InvalidLiteral { span, .. } => span.clone(),
            ParserError::InvalidIdentifier { span, .. } => span.clone(),
            ParserError::UnterminatedString { span } => span.clone(),
            ParserError::UnterminatedComment { span } => span.clone(),
            ParserError::InvalidEscapeSequence { span, .. } => span.clone(),
            ParserError::InternalError { span, .. } => span.clone(),
        }
    }

    /// Convert to a LigatureError with context.
    pub fn into_ligature_error(self) -> LigatureError {
        match self {
            ParserError::SyntaxError { message, span } => LigatureError::Parse {
                code: ErrorCode::E1001,
                message,
                span,
                suggestions: vec![
                    "Check for syntax errors".to_string(),
                    "Verify all brackets and parentheses are balanced".to_string(),
                    "Make sure all expressions are properly terminated".to_string(),
                ],
            },
            ParserError::UnexpectedToken { token, span } => LigatureError::Parse {
                code: ErrorCode::E1002,
                message: format!("Unexpected token: {token}"),
                span,
                suggestions: vec![
                    "Check for typos or invalid characters".to_string(),
                    "Verify the token is valid in this context".to_string(),
                    "Make sure you're using the correct syntax".to_string(),
                ],
            },
            ParserError::ExpectedToken {
                expected,
                found,
                span,
            } => LigatureError::Parse {
                code: ErrorCode::E1003,
                message: format!("Expected {expected}, found {found}"),
                span,
                suggestions: vec![
                    format!("Replace '{}' with '{}'", found, expected),
                    "Check the syntax rules for this construct".to_string(),
                    "Make sure all required tokens are present".to_string(),
                ],
            },
            ParserError::InvalidLiteral { literal, span } => LigatureError::Parse {
                code: ErrorCode::E1004,
                message: format!("Invalid literal: {literal}"),
                span,
                suggestions: vec![
                    "Check the literal format".to_string(),
                    "Verify the literal is within valid ranges".to_string(),
                    "Make sure the literal follows the correct syntax".to_string(),
                ],
            },
            ParserError::InvalidIdentifier { identifier, span } => {
                LigatureError::InvalidIdentifier {
                    code: ErrorCode::E1005,
                    name: identifier,
                    span,
                }
            }
            ParserError::UnterminatedString { span } => LigatureError::Parse {
                code: ErrorCode::E1006,
                message: "Unterminated string literal".to_string(),
                span,
                suggestions: vec![
                    "Add a closing quote".to_string(),
                    "Check for escaped quotes within the string".to_string(),
                    "Make sure the string is properly closed".to_string(),
                ],
            },
            ParserError::UnterminatedComment { span } => LigatureError::Parse {
                code: ErrorCode::E1007,
                message: "Unterminated comment".to_string(),
                span,
                suggestions: vec![
                    "Add a closing comment marker".to_string(),
                    "Check for nested comments".to_string(),
                    "Make sure all comments are properly closed".to_string(),
                ],
            },
            ParserError::InvalidEscapeSequence { sequence, span } => LigatureError::Parse {
                code: ErrorCode::E1008,
                message: format!("Invalid escape sequence: {sequence}"),
                span,
                suggestions: vec![
                    "Use a valid escape sequence".to_string(),
                    "Common escapes: \\n, \\t, \\r, \\\", \\\\".to_string(),
                    "Check the escape sequence documentation".to_string(),
                ],
            },
            ParserError::InternalError { message, span } => LigatureError::InternalError {
                code: ErrorCode::I6001,
                message,
                span,
            },
        }
    }

    /// Add context to the error.
    pub fn with_context(self, context: &str) -> LigatureError {
        let mut error = self.into_ligature_error();
        if let LigatureError::Parse { suggestions, .. } = &mut error {
            suggestions.insert(0, context.to_string());
        }
        error
    }
}

impl From<ParserError> for LigatureError {
    fn from(error: ParserError) -> Self {
        error.into_ligature_error()
    }
}

// Removed conflicting From<ParserError> for anyhow::Error implementation
// Use StandardError::Ligature(error.into_ligature_error()) instead

/// Parser with enhanced error handling capabilities.
pub struct Parser {
    source: String,
    error_collector: ligature_ast::ErrorCollection,
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser {
    /// Create a new parser.
    pub fn new() -> Self {
        Self {
            source: String::new(),
            error_collector: ligature_ast::ErrorCollection::new(),
        }
    }

    /// Create a new parser with source.
    pub fn with_source(source: String) -> Self {
        Self {
            source,
            error_collector: ligature_ast::ErrorCollection::new(),
        }
    }

    /// Create a new parser with custom error collection limits.
    pub fn with_error_limit(source: String, max_errors: usize) -> Self {
        Self {
            source,
            error_collector: ligature_ast::ErrorCollection::with_max_errors(max_errors),
        }
    }

    /// Parse an expression with error context.
    pub fn parse_expression(&mut self, input: &str) -> ParserResult<ligature_ast::Expr> {
        let tokens = self.lex(input)?;

        let ast = self.parse_tokens(&tokens)?;

        Ok(ast)
    }

    /// Parse a program with error context and recovery.
    pub fn parse_program(&mut self, input: &str) -> ParserResult<ligature_ast::Program> {
        self.source = input.to_string();

        let _program = self.parse_expression(input)?;

        Ok(ligature_ast::Program {
            declarations: vec![],
        })
    }

    /// Parse a program with error recovery - continues parsing even if errors occur.
    pub fn parse_program_with_recovery(
        &mut self,
        input: &str,
    ) -> ParserResult<ligature_ast::Program> {
        self.source = input.to_string();

        // Try to parse the program
        match self.parse_program(input) {
            Ok(program) => Ok(program),
            Err(e) => {
                // Add the error to our collection
                // Convert anyhow error to LigatureError
                self.error_collector.push(LigatureError::InternalError {
                    code: ErrorCode::I6001,
                    message: e.to_string(),
                    span: Span::default(),
                });

                // Return a partial result if we have some valid content
                if !self.error_collector.is_empty() {
                    // Return a minimal valid program
                    Ok(ligature_ast::Program {
                        declarations: vec![],
                    })
                } else {
                    Err(e)
                }
            }
        }
    }

    /// Get all collected errors.
    pub fn get_errors(&self) -> &ligature_ast::ErrorCollection {
        &self.error_collector
    }

    /// Check if any errors occurred during parsing.
    pub fn has_errors(&self) -> bool {
        self.error_collector.has_errors()
    }

    /// Generate a formatted error report.
    pub fn error_report(&self) -> String {
        if self.error_collector.is_empty() {
            return "No errors found".to_string();
        }

        let mut reporter = ligature_ast::error::ErrorReporter::new(self.source.clone());

        for error in &self.error_collector.errors {
            reporter.add_error(error.clone());
        }

        reporter.report()
    }

    /// Lex the input into tokens with error context.
    fn lex(&self, input: &str) -> ParserResult<Vec<Token>> {
        let mut tokens = Vec::new();
        let mut pos = 0;

        while pos < input.len() {
            let token = self.lex_token(&input[pos..])?;
            let length = token.length;
            tokens.push(token);
            pos += length;
        }

        Ok(tokens)
    }

    /// Lex a single token with detailed error context.
    fn lex_token(&self, input: &str) -> ParserResult<Token> {
        if input.is_empty() {
            return Err(StandardError::validation_error("Unexpected end of input"));
        }

        let first_char = input.chars().next().unwrap();

        match first_char {
            '0'..='9' => self.lex_number(input),
            'a'..='z' | 'A'..='Z' | '_' => self.lex_identifier(input),
            '"' => self.lex_string(input),
            '+' | '-' | '*' | '/' => self.lex_operator(input),
            '(' | ')' | '{' | '}' | '[' | ']' => self.lex_delimiter(input),
            _ => {
                let span = Span::simple(0, 1);
                Err(StandardError::Ligature(
                    ParserError::UnexpectedToken {
                        token: first_char.to_string(),
                        span,
                    }
                    .into_ligature_error(),
                ))
            }
        }
    }

    // Placeholder implementations for lexing methods
    fn lex_number(&self, _input: &str) -> ParserResult<Token> {
        // Implementation would go here
        Ok(Token { length: 1 })
    }

    fn lex_identifier(&self, _input: &str) -> ParserResult<Token> {
        // Implementation would go here
        Ok(Token { length: 1 })
    }

    fn lex_string(&self, _input: &str) -> ParserResult<Token> {
        // Implementation would go here
        Ok(Token { length: 1 })
    }

    fn lex_operator(&self, _input: &str) -> ParserResult<Token> {
        // Implementation would go here
        Ok(Token { length: 1 })
    }

    fn lex_delimiter(&self, _input: &str) -> ParserResult<Token> {
        // Implementation would go here
        Ok(Token { length: 1 })
    }

    fn parse_tokens(&self, _tokens: &[Token]) -> ParserResult<ligature_ast::Expr> {
        // Implementation would go here
        // For now, return a placeholder expression
        Ok(ligature_ast::Expr {
            kind: ligature_ast::ExprKind::Literal(ligature_ast::Literal::Integer(42)),
            span: Span::default(),
        })
    }
}

/// Simple token representation for the parser.
#[derive(Debug, Clone)]
struct Token {
    length: usize,
}
