//! Source location and span tracking for error reporting.

use serde::{Deserialize, Serialize};

/// A span represents a region of source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    /// Start position (inclusive).
    pub start: usize,
    /// End position (exclusive).
    pub end: usize,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
}

impl Span {
    /// Create a new span.
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    /// Create a span from start and end positions (line/column will be computed).
    pub fn from_positions(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            line: 1, // Will be computed during parsing
            column: 1,
        }
    }

    /// Merge two spans into a single span covering both.
    pub fn merge(self, other: Span) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: self.column.min(other.column),
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
}

impl Default for Span {
    fn default() -> Self {
        Self {
            start: 0,
            end: 0,
            line: 1,
            column: 1,
        }
    }
}

/// A trait for AST nodes that have source location information.
pub trait Spanned {
    /// Get the span of this node.
    fn span(&self) -> Span;
}
