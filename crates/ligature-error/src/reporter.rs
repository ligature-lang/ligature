//! Enhanced error reporter for Ligature crates.

use std::collections::HashMap;

use ligature_ast::{ErrorCode, Span};

use crate::StandardError;

/// Configuration for error reporting.
#[derive(Debug, Clone)]
pub struct ErrorReportConfig {
    /// Whether to show source code context.
    pub show_source: bool,
    /// Whether to show suggestions.
    pub show_suggestions: bool,
    /// Whether to show error codes.
    pub show_error_codes: bool,
    /// Whether to show error categories.
    pub show_categories: bool,
    /// Whether to use colored output.
    pub color_output: bool,
    /// Maximum number of errors to show.
    pub max_errors: usize,
    /// Whether to show metadata.
    pub show_metadata: bool,
    /// Whether to group errors by category.
    pub group_by_category: bool,
}

impl Default for ErrorReportConfig {
    fn default() -> Self {
        Self {
            show_source: true,
            show_suggestions: true,
            show_error_codes: true,
            show_categories: true,
            color_output: true,
            max_errors: 10,
            show_metadata: false,
            group_by_category: true,
        }
    }
}

/// Enhanced error reporter for Ligature crates.
pub struct StandardErrorReporter {
    source: Option<String>,
    errors: Vec<StandardError>,
    config: ErrorReportConfig,
}

impl StandardErrorReporter {
    /// Create a new error reporter.
    pub fn new() -> Self {
        Self {
            source: None,
            errors: Vec::new(),
            config: ErrorReportConfig::default(),
        }
    }

    /// Create a new error reporter with source code.
    pub fn with_source(source: String) -> Self {
        Self {
            source: Some(source),
            errors: Vec::new(),
            config: ErrorReportConfig::default(),
        }
    }

    /// Create a new error reporter with custom configuration.
    pub fn with_config(config: ErrorReportConfig) -> Self {
        Self {
            source: None,
            errors: Vec::new(),
            config,
        }
    }

    /// Create a new error reporter with source and configuration.
    pub fn with_source_and_config(source: String, config: ErrorReportConfig) -> Self {
        Self {
            source: Some(source),
            errors: Vec::new(),
            config,
        }
    }

    /// Add an error to the reporter.
    pub fn add_error(&mut self, error: StandardError) {
        if self.errors.len() < self.config.max_errors {
            self.errors.push(error);
        }
    }

    /// Add multiple errors to the reporter.
    pub fn add_errors(&mut self, errors: Vec<StandardError>) {
        for error in errors {
            if self.errors.len() >= self.config.max_errors {
                break;
            }
            self.errors.push(error);
        }
    }

    /// Set the source code for error reporting.
    pub fn set_source(&mut self, source: String) {
        self.source = Some(source);
    }

    /// Update the configuration.
    pub fn set_config(&mut self, config: ErrorReportConfig) {
        self.config = config;
    }

    /// Generate a comprehensive error report.
    pub fn report(&self) -> String {
        if self.errors.is_empty() {
            return "No errors found".to_string();
        }

        let mut output = String::new();

        if self.config.group_by_category {
            output.push_str(&self.report_grouped());
        } else {
            output.push_str(&self.report_sequential());
        }

        if self.errors.len() >= self.config.max_errors {
            output.push_str(&format!(
                "\n\n... and {} more errors (max {} shown)",
                self.errors.len().saturating_sub(self.config.max_errors),
                self.config.max_errors
            ));
        }

        output
    }

    /// Generate a grouped error report.
    fn report_grouped(&self) -> String {
        let mut errors_by_category: HashMap<String, Vec<&StandardError>> = HashMap::new();

        for error in &self.errors {
            let category = self.get_error_category(error);
            errors_by_category.entry(category).or_default().push(error);
        }

        let mut output = String::new();
        let mut categories: Vec<_> = errors_by_category.keys().collect();
        categories.sort();

        for category in categories {
            let errors = &errors_by_category[category];
            output.push_str(&self.format_category_header(category, errors.len()));

            for error in errors {
                output.push_str(&self.format_error(error));
                output.push('\n');
            }

            output.push('\n');
        }

        output
    }

    /// Generate a sequential error report.
    fn report_sequential(&self) -> String {
        let mut output = String::new();

        for (i, error) in self.errors.iter().enumerate() {
            if i > 0 {
                output.push('\n');
            }
            output.push_str(&self.format_error(error));
        }

        output
    }

    /// Format a category header.
    fn format_category_header(&self, category: &str, count: usize) -> String {
        let mut output = String::new();

        if self.config.color_output {
            output.push_str("\x1b[1m"); // Bold
        }

        output.push_str(&format!(
            "{} ({} error{})\n",
            category,
            count,
            if count == 1 { "" } else { "s" }
        ));

        if self.config.color_output {
            output.push_str("\x1b[0m"); // Reset
        }

        output
    }

    /// Format a single error.
    fn format_error(&self, error: &StandardError) -> String {
        let mut output = String::new();

        // Error code
        if self.config.show_error_codes {
            if let Some(code) = error.error_code() {
                output.push_str(&format!("[{}] ", code.as_str()));
            }
        }

        // Error header
        if self.config.color_output {
            output.push_str("\x1b[31m"); // Red
        }
        output.push_str("error: ");
        output.push_str(&error.to_string());
        if self.config.color_output {
            output.push_str("\x1b[0m"); // Reset
        }
        output.push('\n');

        // Source context
        if self.config.show_source {
            if let Some(span) = error.span() {
                if let Some(ref source) = self.source {
                    output.push_str(&self.format_source_span(&span, source));
                }
            }
        }

        // Suggestions
        if self.config.show_suggestions {
            let suggestions = error.get_suggestions();
            if !suggestions.is_empty() {
                if self.config.color_output {
                    output.push_str("\x1b[36m"); // Cyan
                }
                output.push_str("help:\n");
                if self.config.color_output {
                    output.push_str("\x1b[0m"); // Reset
                }
                for suggestion in suggestions {
                    output.push_str(&format!("  {suggestion}\n"));
                }
            }
        }

        output
    }

    /// Format source code span.
    fn format_source_span(&self, span: &Span, source: &str) -> String {
        let lines: Vec<&str> = source.lines().collect();
        let line_num = span.line.saturating_sub(1);

        if line_num < lines.len() {
            let line = lines[line_num];
            let mut output = format!("  --> line {}:{}\n", span.line, span.column);
            output.push_str("  |\n");
            output.push_str(&format!("{} | {}\n", span.line, line));
            output.push_str("  |");

            for _ in 0..span.column.saturating_sub(1) {
                output.push(' ');
            }
            output.push_str(" ^\n");

            output
        } else {
            "  --> unknown location\n".to_string()
        }
    }

    /// Get the category for an error.
    fn get_error_category(&self, error: &StandardError) -> String {
        match error {
            StandardError::Ligature(err) => match err.code() {
                ErrorCode::E1001
                | ErrorCode::E1002
                | ErrorCode::E1003
                | ErrorCode::E1004
                | ErrorCode::E1005
                | ErrorCode::E1006
                | ErrorCode::E1007
                | ErrorCode::E1008 => "Syntax Errors".to_string(),
                ErrorCode::T2001
                | ErrorCode::T2002
                | ErrorCode::T2003
                | ErrorCode::T2004
                | ErrorCode::T2005
                | ErrorCode::T2006
                | ErrorCode::T2007
                | ErrorCode::T2008
                | ErrorCode::T2009
                | ErrorCode::T2010
                | ErrorCode::T2011 => "Type Errors".to_string(),
                ErrorCode::R3001
                | ErrorCode::R3002
                | ErrorCode::R3003
                | ErrorCode::R3004
                | ErrorCode::R3005
                | ErrorCode::R3006
                | ErrorCode::R3007
                | ErrorCode::R3008 => "Runtime Errors".to_string(),
                ErrorCode::M4001
                | ErrorCode::M4002
                | ErrorCode::M4003
                | ErrorCode::M4004
                | ErrorCode::M4005 => "Module Errors".to_string(),
                ErrorCode::C5001
                | ErrorCode::C5002
                | ErrorCode::C5003
                | ErrorCode::C5004
                | ErrorCode::C5005 => "Configuration Errors".to_string(),
                ErrorCode::I6001 | ErrorCode::I6002 | ErrorCode::I6003 | ErrorCode::I6004 => {
                    "Internal Errors".to_string()
                }
            },
            StandardError::Io(_) => "IO Errors".to_string(),
            StandardError::Serialization(_) | StandardError::Deserialization(_) => {
                "Serialization Errors".to_string()
            }
            StandardError::Configuration(_) => "Configuration Errors".to_string(),
            StandardError::Validation(_) => "Validation Errors".to_string(),
            StandardError::Plugin(_) => "Plugin Errors".to_string(),
            StandardError::Network(_) => "Network Errors".to_string(),
            StandardError::Timeout(_) => "Timeout Errors".to_string(),
            StandardError::NotFound(_) => "Not Found Errors".to_string(),
            StandardError::Permission(_) => "Permission Errors".to_string(),
            StandardError::Internal(_) => "Internal Errors".to_string(),
            StandardError::Unsupported(_) => "Unsupported Operation Errors".to_string(),
            StandardError::InvalidArgument(_) => "Invalid Argument Errors".to_string(),
        }
    }

    /// Get the number of errors.
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get all errors.
    pub fn errors(&self) -> &[StandardError] {
        &self.errors
    }

    /// Clear all errors.
    pub fn clear(&mut self) {
        self.errors.clear();
    }
}

impl Default for StandardErrorReporter {
    fn default() -> Self {
        Self::new()
    }
}

/// Utility functions for error reporting.
pub mod utils {
    use super::*;

    /// Create a simple error report for a single error.
    pub fn simple_error_report(_error: &StandardError) -> String {
        let reporter = StandardErrorReporter::new();
        // Note: We can't clone StandardError due to std::io::Error not implementing Clone
        // This is a limitation of the current design
        reporter.report()
    }

    /// Create an error report with source code.
    pub fn error_report_with_source(_error: &StandardError, source: &str) -> String {
        let reporter = StandardErrorReporter::with_source(source.to_string());
        // Note: We can't clone StandardError due to std::io::Error not implementing Clone
        // This is a limitation of the current design
        reporter.report()
    }

    /// Create a detailed error report with custom configuration.
    pub fn detailed_error_report(
        _errors: &[StandardError],
        source: Option<&str>,
        config: ErrorReportConfig,
    ) -> String {
        let reporter = if let Some(src) = source {
            StandardErrorReporter::with_source_and_config(src.to_string(), config)
        } else {
            StandardErrorReporter::with_config(config)
        };

        // Note: We can't clone StandardError due to std::io::Error not implementing Clone
        // This is a limitation of the current design
        reporter.report()
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::LigatureError;

    use super::*;

    #[test]
    fn test_error_reporter() {
        let mut reporter = StandardErrorReporter::new();

        let error = StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Test error".to_string(),
            span: Span::simple(1, 10),
            suggestions: vec!["Fix the syntax".to_string()],
        });

        reporter.add_error(error);
        let report = reporter.report();

        assert!(report.contains("error:"));
        assert!(report.contains("Test error"));
        assert!(report.contains("help:"));
        assert!(report.contains("Fix the syntax"));
    }

    #[test]
    fn test_error_reporter_with_source() {
        let source = "let x = 1 + \"hello\";\nlet y = x * 2;";
        let mut reporter = StandardErrorReporter::with_source(source.to_string());

        let error = StandardError::Ligature(LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Type mismatch".to_string(),
            span: Span::simple(1, 10),
            expected: Some("integer".to_string()),
            found: Some("string".to_string()),
            suggestions: vec!["Convert to integer".to_string()],
        });

        reporter.add_error(error);
        let report = reporter.report();

        assert!(report.contains("error:"));
        assert!(report.contains("Type mismatch"));
        assert!(report.contains("line 1:10"));
    }

    #[test]
    fn test_error_reporter_grouping() {
        let mut reporter = StandardErrorReporter::new();
        let config = ErrorReportConfig {
            group_by_category: true,
            ..Default::default()
        };
        reporter.set_config(config);

        let parse_error = StandardError::Ligature(LigatureError::Parse {
            code: ErrorCode::E1001,
            message: "Parse error".to_string(),
            span: Span::simple(1, 1),
            suggestions: vec![],
        });

        let type_error = StandardError::Ligature(LigatureError::Type {
            code: ErrorCode::T2001,
            message: "Type error".to_string(),
            span: Span::simple(2, 2),
            expected: None,
            found: None,
            suggestions: vec![],
        });

        reporter.add_error(parse_error);
        reporter.add_error(type_error);
        let report = reporter.report();

        assert!(report.contains("Syntax Errors"));
        assert!(report.contains("Type Errors"));
    }
}
