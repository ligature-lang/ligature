//! Source location and span tracking for error reporting.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// A span represents a region of source code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    /// Start position (inclusive).
    pub start: usize,
    /// End position (exclusive).
    pub end: usize,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
    /// File path (optional).
    pub file: Option<PathBuf>,
}

impl Span {
    /// Create a new span.
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
            file: None,
        }
    }

    /// Create a span from start and end positions (line/column will be computed).
    pub fn from_positions(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            line: 1, // Will be computed during parsing
            column: 1,
            file: None,
        }
    }

    /// Create a simple span with line and column positions.
    pub fn simple(line: usize, column: usize) -> Self {
        Self {
            start: 0,
            end: 0,
            line,
            column,
            file: None,
        }
    }

    /// Add location information to the span.
    pub fn with_location(mut self, line: usize, column: usize) -> Self {
        self.line = line;
        self.column = column;
        self
    }

    /// Add file information to the span.
    pub fn with_file(mut self, file: PathBuf) -> Self {
        self.file = Some(file);
        self
    }

    /// Merge two spans into a single span covering both.
    pub fn merge(self, other: Span) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: self.column.min(other.column),
            file: self.file.or(other.file),
        }
    }

    /// Check if this span contains the given position.
    pub fn contains(&self, pos: usize) -> bool {
        self.start <= pos && pos < self.end
    }

    /// Get the length of this span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check if this span is empty.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Check if this span is valid.
    pub fn is_valid(&self) -> bool {
        self.start <= self.end
    }

    /// Display the span with source context.
    pub fn display(&self, _source: &str) -> String {
        if let Some(file) = &self.file {
            format!("{}:{}:{}", file.display(), self.line, self.column)
        } else {
            format!("line {}:{}", self.line, self.column)
        }
    }

    /// Format the span with source code highlighting.
    pub fn format_with_source(&self, source: &str) -> String {
        let lines: Vec<&str> = source.lines().collect();
        let line_num = self.line.saturating_sub(1);

        if line_num < lines.len() {
            let line = lines[line_num];
            let mut output = format!("  --> line {}:{}\n", self.line, self.column);
            output.push_str("  |\n");
            output.push_str(&format!("{} | {}\n", self.line, line));
            output.push_str("  |");

            for _ in 0..self.column.saturating_sub(1) {
                output.push(' ');
            }
            output.push_str(" ^\n");

            output
        } else {
            format!("  --> unknown location\n")
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self {
            start: 0,
            end: 0,
            line: 1,
            column: 1,
            file: None,
        }
    }
}

/// A trait for AST nodes that have source location information.
pub trait Spanned {
    /// Get the span of this node.
    fn span(&self) -> Span;
}
