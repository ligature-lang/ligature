//! Error context and enhanced error handling.

/// Context for error information.
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub operation: String,
    pub file: Option<String>,
    pub line: Option<u32>,
    pub expression: Option<String>,
    pub expected_type: Option<String>,
    pub actual_type: Option<String>,
    pub additional_info: Option<String>,
}

impl ErrorContext {
    pub fn new(operation: String) -> Self {
        Self {
            operation,
            file: None,
            line: None,
            expression: None,
            expected_type: None,
            actual_type: None,
            additional_info: None,
        }
    }

    pub fn with_file(mut self, file: String) -> Self {
        self.file = Some(file);
        self
    }

    pub fn with_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    pub fn with_expression(mut self, expression: String) -> Self {
        self.expression = Some(expression);
        self
    }

    pub fn with_types(mut self, expected: String, actual: String) -> Self {
        self.expected_type = Some(expected);
        self.actual_type = Some(actual);
        self
    }

    pub fn with_info(mut self, info: String) -> Self {
        self.additional_info = Some(info);
        self
    }
}

/// Enhanced error with context.
#[derive(Debug, Clone)]
pub struct BatonErrorWithContext {
    pub error: crate::error::BatonError,
    pub context: ErrorContext,
}

impl std::fmt::Display for BatonErrorWithContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.error)?;
        if let Some(file) = &self.context.file {
            write!(f, " (file: {file})")?;
        }
        if let Some(line) = self.context.line {
            write!(f, " (line: {line})")?;
        }
        if let Some(expression) = &self.context.expression {
            write!(f, " (expression: {expression})")?;
        }
        if let Some(info) = &self.context.additional_info {
            write!(f, " (info: {info})")?;
        }
        Ok(())
    }
}

impl std::error::Error for BatonErrorWithContext {}

/// Result type for Baton operations with context.
pub type BatonResultWithContext<T> = Result<T, BatonErrorWithContext>;
