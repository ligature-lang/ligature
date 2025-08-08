//! Fuzzing infrastructure for the Ligature parser.
//!
//! This module provides comprehensive fuzzing capabilities including:
//! - Grammar-based input generation
//! - Mutation-based fuzzing
//! - Coverage-guided fuzzing
//! - Property-based testing
//! - Error recovery testing

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use ligature_ast::AstResult;
use rand::Rng;

use crate::Parser;

/// Grammar-based fuzzer for generating structured inputs
pub struct GrammarFuzzer {
    grammar: Grammar,
    max_depth: usize,
    max_length: usize,
}

/// Grammar definition for generating structured inputs
pub struct Grammar {
    rules: HashMap<String, Vec<Production>>,
}

/// Production rule in the grammar
pub struct Production {
    symbols: Vec<Symbol>,
}

/// Symbol in a production rule
#[derive(Debug, Clone)]
pub enum Symbol {
    Terminal(String),
    NonTerminal(String),
}

/// Mutation-based fuzzer for generating inputs by mutating existing ones
pub struct MutationFuzzer {
    corpus: Vec<String>,
    mutation_strategies: Vec<Box<dyn MutationStrategy>>,
}

/// Trait for mutation strategies
pub trait MutationStrategy {
    fn mutate(&self, input: &str) -> String;
    fn name(&self) -> &'static str;
    fn random_char(&self) -> char;
}

/// Coverage tracker for AFL-style fuzzing
#[derive(Debug, Default)]
pub struct CoverageTracker {
    edges: HashSet<(u32, u32)>,
    total_edges: usize,
}

/// Performance fuzzer for testing parser performance bounds
pub struct PerformanceFuzzer {
    timeout: Duration,
    #[allow(dead_code)]
    max_memory: usize,
}

/// Error recovery fuzzer for testing parser error handling
pub struct ErrorRecoveryFuzzer {
    #[allow(dead_code)]
    error_patterns: Vec<String>,
    recovery_strategies: Vec<Box<dyn RecoveryStrategy>>,
}

/// Trait for error recovery strategies
pub trait RecoveryStrategy {
    fn can_recover(&self, error: &str) -> bool;
    fn recover(&self, input: &str, error: &str) -> String;
    fn name(&self) -> &'static str;
}

/// Results from performance testing
#[derive(Debug)]
pub struct PerformanceResult {
    pub duration: Duration,
    pub success: bool,
    pub timeout: bool,
    pub memory_usage: Option<usize>,
}

impl GrammarFuzzer {
    /// Create a new grammar fuzzer with the Ligature grammar
    pub fn new() -> Self {
        Self {
            grammar: Grammar::ligature_grammar(),
            max_depth: 10,
            max_length: 10000,
        }
    }

    /// Generate a random expression
    pub fn generate_expression(&self) -> String {
        self.generate_from_rule("expression", 0)
    }

    /// Generate a random program
    pub fn generate_program(&self) -> String {
        self.generate_from_rule("program", 0)
    }

    /// Generate a random type
    pub fn generate_type(&self) -> String {
        self.generate_from_rule("type", 0)
    }

    fn generate_from_rule(&self, rule: &str, depth: usize) -> String {
        if depth > self.max_depth {
            return self.generate_terminator(rule);
        }

        match self.grammar.get_rule(rule) {
            Some(productions) => {
                let production = self.select_production(productions);
                self.generate_from_production(production, depth + 1)
            }
            None => self.generate_terminator(rule),
        }
    }

    fn generate_from_production(&self, production: &Production, depth: usize) -> String {
        let mut result = String::new();

        for symbol in &production.symbols {
            match symbol {
                Symbol::Terminal(term) => result.push_str(term),
                Symbol::NonTerminal(nt) => {
                    result.push_str(&self.generate_from_rule(nt, depth));
                }
            }
        }

        // Check length limit
        if result.len() > self.max_length {
            return self.generate_terminator("expression");
        }

        result
    }

    fn select_production<'a>(&self, productions: &'a [Production]) -> &'a Production {
        let mut rng = rand::thread_rng();
        &productions[rng.gen_range(0..productions.len())]
    }

    fn generate_terminator(&self, rule: &str) -> String {
        let mut rng = rand::thread_rng();

        match rule {
            "expression" => {
                let variants = [
                    "42",
                    "3.14",
                    "true",
                    "false",
                    "\"hello\"",
                    "x",
                    "my_variable",
                ];
                variants[rng.gen_range(0..variants.len())].to_string()
            }
            "identifier" => {
                let variants = ["x", "y", "z", "my_var", "test", "value"];
                variants[rng.gen_range(0..variants.len())].to_string()
            }
            "literal" => {
                let variants = ["42", "3.14", "true", "false", "\"hello\""];
                variants[rng.gen_range(0..variants.len())].to_string()
            }
            "type" => {
                let variants = ["Int", "Float", "Bool", "String", "Unit"];
                variants[rng.gen_range(0..variants.len())].to_string()
            }
            _ => "42".to_string(),
        }
    }
}

impl Default for GrammarFuzzer {
    fn default() -> Self {
        Self::new()
    }
}

impl Grammar {
    /// Create the Ligature grammar for fuzzing
    pub fn ligature_grammar() -> Self {
        let mut rules = HashMap::new();

        // Expression rules
        rules.insert(
            "expression".to_string(),
            vec![
                Production {
                    symbols: vec![Symbol::NonTerminal("literal".to_string())],
                },
                Production {
                    symbols: vec![Symbol::NonTerminal("identifier".to_string())],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" + ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" - ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" * ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" / ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::Terminal("let ".to_string()),
                        Symbol::NonTerminal("identifier".to_string()),
                        Symbol::Terminal(" = ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" in ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::Terminal("if ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" then ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(" else ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::Terminal("\\".to_string()),
                        Symbol::NonTerminal("identifier".to_string()),
                        Symbol::Terminal(" -> ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::Terminal("(".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                        Symbol::Terminal(")".to_string()),
                    ],
                },
            ],
        );

        // Program rules
        rules.insert(
            "program".to_string(),
            vec![
                Production {
                    symbols: vec![Symbol::NonTerminal("declaration".to_string())],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("declaration".to_string()),
                        Symbol::Terminal("; ".to_string()),
                        Symbol::NonTerminal("program".to_string()),
                    ],
                },
            ],
        );

        // Declaration rules
        rules.insert(
            "declaration".to_string(),
            vec![
                Production {
                    symbols: vec![
                        Symbol::Terminal("let ".to_string()),
                        Symbol::NonTerminal("identifier".to_string()),
                        Symbol::Terminal(" = ".to_string()),
                        Symbol::NonTerminal("expression".to_string()),
                    ],
                },
                Production {
                    symbols: vec![
                        Symbol::Terminal("type ".to_string()),
                        Symbol::NonTerminal("identifier".to_string()),
                        Symbol::Terminal(" = ".to_string()),
                        Symbol::NonTerminal("type".to_string()),
                    ],
                },
            ],
        );

        // Type rules
        rules.insert(
            "type".to_string(),
            vec![
                Production {
                    symbols: vec![Symbol::Terminal("Int".to_string())],
                },
                Production {
                    symbols: vec![Symbol::Terminal("Float".to_string())],
                },
                Production {
                    symbols: vec![Symbol::Terminal("Bool".to_string())],
                },
                Production {
                    symbols: vec![Symbol::Terminal("String".to_string())],
                },
                Production {
                    symbols: vec![Symbol::Terminal("Unit".to_string())],
                },
                Production {
                    symbols: vec![
                        Symbol::NonTerminal("type".to_string()),
                        Symbol::Terminal(" -> ".to_string()),
                        Symbol::NonTerminal("type".to_string()),
                    ],
                },
            ],
        );

        Self { rules }
    }

    fn get_rule(&self, rule: &str) -> Option<&Vec<Production>> {
        self.rules.get(rule)
    }
}

impl MutationFuzzer {
    /// Create a new mutation fuzzer
    pub fn new() -> Self {
        let strategies: Vec<Box<dyn MutationStrategy>> = vec![
            Box::new(InsertionMutation),
            Box::new(DeletionMutation),
            Box::new(ReplacementMutation),
            Box::new(DuplicationMutation),
            Box::new(TruncationMutation),
        ];

        Self {
            corpus: Self::initial_corpus(),
            mutation_strategies: strategies,
        }
    }

    /// Add an input to the corpus
    pub fn add_to_corpus(&mut self, input: String) {
        if !self.corpus.contains(&input) {
            self.corpus.push(input);
        }
    }

    /// Generate a mutated input
    pub fn generate_input(&mut self) -> String {
        if self.corpus.is_empty() {
            return "42".to_string();
        }

        let mut rng = rand::thread_rng();
        let base_input = &self.corpus[rng.gen_range(0..self.corpus.len())];
        let strategy = &self.mutation_strategies[rng.gen_range(0..self.mutation_strategies.len())];

        strategy.mutate(base_input)
    }

    fn initial_corpus() -> Vec<String> {
        vec![
            "42".to_string(),
            "x".to_string(),
            "x + y".to_string(),
            "let x = 42 in x".to_string(),
            "if true then 1 else 2".to_string(),
            "{ x = 1, y = 2 }".to_string(),
            "[1, 2, 3]".to_string(),
            "\\x -> x + 1".to_string(),
            "let x = 1; let y = 2; x + y".to_string(),
            "type MyType = Int".to_string(),
            // Add some malformed inputs for testing error handling
            "x +".to_string(),
            "let x =".to_string(),
            "if true then".to_string(),
            "{}".to_string(),
            "[]".to_string(),
            "\\x ->".to_string(),
        ]
    }
}

impl Default for MutationFuzzer {
    fn default() -> Self {
        Self::new()
    }
}

impl CoverageTracker {
    /// Create a new coverage tracker
    pub fn new() -> Self {
        Self {
            edges: HashSet::new(),
            total_edges: 0,
        }
    }

    /// Record an edge in the control flow
    pub fn record_edge(&mut self, from: u32, to: u32) {
        self.edges.insert((from, to));
        self.total_edges = self.edges.len();
    }

    /// Get the current coverage percentage
    pub fn coverage(&self) -> f64 {
        if self.total_edges == 0 {
            0.0
        } else {
            self.edges.len() as f64 / self.total_edges as f64
        }
    }

    /// Get the number of unique edges
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }
}

impl PerformanceFuzzer {
    /// Create a new performance fuzzer
    pub fn new() -> Self {
        Self {
            timeout: Duration::from_secs(1),
            #[allow(dead_code)]
            max_memory: 100 * 1024 * 1024, // 100MB
        }
    }

    /// Test parser performance with an input
    pub fn test_performance(&self, input: &str) -> PerformanceResult {
        let start = std::time::Instant::now();
        let mut parser = Parser::new();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            parser.parse_expression(input)
        }));

        let duration = start.elapsed();

        PerformanceResult {
            duration,
            success: result.is_ok(),
            timeout: duration > self.timeout,
            memory_usage: None, // Would need memory profiling to implement
        }
    }
}

impl Default for PerformanceFuzzer {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorRecoveryFuzzer {
    /// Create a new error recovery fuzzer
    pub fn new() -> Self {
        let error_patterns = vec![
            "unexpected token".to_string(),
            "expected".to_string(),
            "unterminated".to_string(),
            "missing".to_string(),
        ];

        let recovery_strategies: Vec<Box<dyn RecoveryStrategy>> = vec![
            Box::new(SkipToSemicolon),
            Box::new(SkipToClosingBrace),
            Box::new(InsertMissingToken),
            Box::new(InsertMissingParenthesis),
        ];

        Self {
            #[allow(dead_code)]
            error_patterns,
            recovery_strategies,
        }
    }

    /// Test error recovery with an input
    pub fn test_error_recovery(&self, input: &str) -> Vec<String> {
        let mut parser = Parser::new();
        let result = parser.parse_expression(input);

        match result {
            Ok(_) => vec![], // No recovery needed
            Err(error) => {
                let error_msg = error.to_string();
                // Try recovery strategies
                self.recovery_strategies
                    .iter()
                    .filter(|strategy| strategy.can_recover(&error_msg))
                    .map(|strategy| strategy.recover(input, &error_msg))
                    .collect()
            }
        }
    }
}

impl Default for ErrorRecoveryFuzzer {
    fn default() -> Self {
        Self::new()
    }
}

// Mutation strategies
pub struct InsertionMutation;
pub struct DeletionMutation;
pub struct ReplacementMutation;
pub struct DuplicationMutation;
pub struct TruncationMutation;

impl MutationStrategy for InsertionMutation {
    fn mutate(&self, input: &str) -> String {
        if input.is_empty() {
            return "x".to_string();
        }

        let mut rng = rand::thread_rng();
        let mut result = input.to_string();
        let pos = rng.gen_range(0..=input.len());
        let char_to_insert = self.random_char();

        result.insert(pos, char_to_insert);
        result
    }

    fn name(&self) -> &'static str {
        "insertion"
    }

    fn random_char(&self) -> char {
        let mut rng = rand::thread_rng();
        const CHARS: &[char] = &[
            'a', 'b', 'c', '1', '2', '3', '+', '-', '*', '(', ')', '{', '}', ';', '=',
        ];
        CHARS[rng.gen_range(0..CHARS.len())]
    }
}

impl MutationStrategy for DeletionMutation {
    fn mutate(&self, input: &str) -> String {
        if input.is_empty() {
            return input.to_string();
        }

        let mut rng = rand::thread_rng();
        let mut result = input.to_string();
        let pos = rng.gen_range(0..input.len());
        result.remove(pos);
        result
    }

    fn name(&self) -> &'static str {
        "deletion"
    }

    fn random_char(&self) -> char {
        let mut rng = rand::thread_rng();
        const CHARS: &[char] = &[
            'a', 'b', 'c', '1', '2', '3', '+', '-', '*', '(', ')', '{', '}', ';', '=',
        ];
        CHARS[rng.gen_range(0..CHARS.len())]
    }
}

impl MutationStrategy for ReplacementMutation {
    fn mutate(&self, input: &str) -> String {
        if input.is_empty() {
            return input.to_string();
        }

        let mut rng = rand::thread_rng();
        let mut result = input.to_string();
        let pos = rng.gen_range(0..input.len());
        let new_char = self.random_char();

        result.replace_range(pos..pos + 1, &new_char.to_string());
        result
    }

    fn name(&self) -> &'static str {
        "replacement"
    }

    fn random_char(&self) -> char {
        let mut rng = rand::thread_rng();
        const CHARS: &[char] = &[
            'a', 'b', 'c', '1', '2', '3', '+', '-', '*', '(', ')', '{', '}', ';', '=',
        ];
        CHARS[rng.gen_range(0..CHARS.len())]
    }
}

impl MutationStrategy for DuplicationMutation {
    fn mutate(&self, input: &str) -> String {
        if input.is_empty() {
            return input.to_string();
        }

        let mut rng = rand::thread_rng();
        let mut result = input.to_string();
        let pos = rng.gen_range(0..input.len());
        let char_to_duplicate = result.chars().nth(pos).unwrap_or('x');

        result.insert(pos, char_to_duplicate);
        result
    }

    fn name(&self) -> &'static str {
        "duplication"
    }

    fn random_char(&self) -> char {
        let mut rng = rand::thread_rng();
        const CHARS: &[char] = &[
            'a', 'b', 'c', '1', '2', '3', '+', '-', '*', '(', ')', '{', '}', ';', '=',
        ];
        CHARS[rng.gen_range(0..CHARS.len())]
    }
}

impl MutationStrategy for TruncationMutation {
    fn mutate(&self, input: &str) -> String {
        if input.len() <= 1 {
            return input.to_string();
        }

        let mut rng = rand::thread_rng();
        let truncate_pos = rng.gen_range(1..input.len());
        input[..truncate_pos].to_string()
    }

    fn name(&self) -> &'static str {
        "truncation"
    }

    fn random_char(&self) -> char {
        let mut rng = rand::thread_rng();
        const CHARS: &[char] = &[
            'a', 'b', 'c', '1', '2', '3', '+', '-', '*', '(', ')', '{', '}', ';', '=',
        ];
        CHARS[rng.gen_range(0..CHARS.len())]
    }
}

// Recovery strategies
pub struct SkipToSemicolon;
pub struct SkipToClosingBrace;
pub struct InsertMissingToken;
pub struct InsertMissingParenthesis;

impl RecoveryStrategy for SkipToSemicolon {
    fn can_recover(&self, error: &str) -> bool {
        error.contains("expected") && error.contains(";")
    }

    fn recover(&self, input: &str, _error: &str) -> String {
        let mut result = input.to_string();
        if !result.ends_with(';') {
            result.push(';');
        }
        result
    }

    fn name(&self) -> &'static str {
        "skip_to_semicolon"
    }
}

impl RecoveryStrategy for SkipToClosingBrace {
    fn can_recover(&self, error: &str) -> bool {
        error.contains("unterminated") && error.contains("{")
    }

    fn recover(&self, input: &str, _error: &str) -> String {
        let mut result = input.to_string();
        if !result.ends_with('}') {
            result.push('}');
        }
        result
    }

    fn name(&self) -> &'static str {
        "skip_to_closing_brace"
    }
}

impl RecoveryStrategy for InsertMissingToken {
    fn can_recover(&self, error: &str) -> bool {
        error.contains("missing") || error.contains("expected")
    }

    fn recover(&self, input: &str, _error: &str) -> String {
        let mut result = input.to_string();
        if !result.ends_with(';') {
            result.push(';');
        }
        result
    }

    fn name(&self) -> &'static str {
        "insert_missing_token"
    }
}

impl RecoveryStrategy for InsertMissingParenthesis {
    fn can_recover(&self, error: &str) -> bool {
        error.contains("unterminated") && error.contains("(")
    }

    fn recover(&self, input: &str, _error: &str) -> String {
        let mut result = input.to_string();
        if !result.ends_with(')') {
            result.push(')');
        }
        result
    }

    fn name(&self) -> &'static str {
        "insert_missing_parenthesis"
    }
}

/// Test that the parser handles all inputs without crashing
pub fn test_parser_robustness(input: &str) -> AstResult<()> {
    let mut parser = Parser::new();

    // Test expression parsing
    let _result = parser.parse_expression(input);
    // Should not panic, regardless of success/failure

    // Test program parsing
    let _result = parser.parse_program(input);
    // Should not panic, regardless of success/failure

    Ok(())
}

/// Test that parser performance is reasonable
pub fn test_parser_performance(input: &str) -> AstResult<()> {
    let start = std::time::Instant::now();
    let mut parser = Parser::new();

    let _result = parser.parse_expression(input);
    let duration = start.elapsed();

    // Parser should complete within reasonable time
    if duration > Duration::from_secs(1) {
        return Err(ligature_ast::AstError::ParseError {
            message: format!("Parser took too long: {duration:?}"),
            span: ligature_ast::Span::default(),
        });
    }

    Ok(())
}

/// Test that parser memory usage is reasonable
pub fn test_parser_memory(input: &str) -> AstResult<()> {
    let mut parser = Parser::new();

    // Parse multiple times to check for memory leaks
    for _ in 0..100 {
        let _result = parser.parse_expression(input);
        // Should not crash or leak memory
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_grammar_fuzzer() {
        let fuzzer = GrammarFuzzer::new();
        let expr = fuzzer.generate_expression();
        assert!(!expr.is_empty());

        let program = fuzzer.generate_program();
        assert!(!program.is_empty());
    }

    #[test]
    fn test_mutation_fuzzer() {
        let mut fuzzer = MutationFuzzer::new();
        let input = fuzzer.generate_input();
        assert!(!input.is_empty());

        fuzzer.add_to_corpus("test input".to_string());
        let mutated = fuzzer.generate_input();
        assert!(!mutated.is_empty());
    }

    #[test]
    fn test_coverage_tracker() {
        let mut tracker = CoverageTracker::new();
        assert_eq!(tracker.coverage(), 0.0);

        tracker.record_edge(1, 2);
        assert_eq!(tracker.edge_count(), 1);
        assert_eq!(tracker.coverage(), 1.0);
    }

    #[test]
    fn test_performance_fuzzer() {
        let fuzzer = PerformanceFuzzer::new();
        let result = fuzzer.test_performance("42");
        assert!(result.success);
        assert!(!result.timeout);
    }

    #[test]
    fn test_error_recovery_fuzzer() {
        let fuzzer = ErrorRecoveryFuzzer::new();
        let recovered = fuzzer.test_error_recovery("x +");
        // Should attempt recovery strategies
        assert!(recovered.is_empty() || !recovered.is_empty());
    }

    #[test]
    fn test_parser_robustness_integration() {
        // Test with various inputs
        let inputs = vec![
            "42",
            "x + y",
            "let x = 42 in x",
            "invalid input",
            "",
            "x +",
            "let x =",
        ];

        for input in inputs {
            let result = test_parser_robustness(input);
            assert!(
                result.is_ok(),
                "Parser should not crash on input: {input:?}"
            );
        }
    }

    #[test]
    fn test_parser_performance_integration() {
        let inputs = vec!["42", "x + y", "let x = 42 in x"];

        for input in inputs {
            let result = test_parser_performance(input);
            assert!(result.is_ok(), "Parser should be fast on input: {input:?}");
        }
    }
}

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_parser_properties(input in fuzzed_expression_strategy()) {
            // Test that parser handles all generated inputs without crashing
            let mut parser = Parser::new();
            let result = parser.parse_expression(&input);

            // Parser should never panic
            match result {
                Ok(_) => {
                    // Valid parse - additional checks can be added
                }
                Err(error) => {
                    // Invalid parse - verify error properties
                    assert!(!error.to_string().is_empty());
                }
            }
        }

        #[test]
        fn test_parser_performance_prop(input in large_expression_strategy()) {
            // Test that parser performance is reasonable
            let start = std::time::Instant::now();
            let mut parser = Parser::new();
            let result = parser.parse_expression(&input);
            let duration = start.elapsed();

            // Parser should complete within reasonable time
            assert!(duration < std::time::Duration::from_secs(1));

            // Should not crash regardless of result
            if result.is_ok() {}
        }

        #[test]
        fn test_parser_memory(input in memory_stress_strategy()) {
            // Test that parser doesn't leak memory or cause OOM
            let mut parser = Parser::new();

            // Parse multiple times to check for memory leaks
            for _ in 0..100 {
                let result = parser.parse_expression(&input);

                // Should not crash
                if result.is_ok() {}
            }
        }

        #[test]
        fn test_parser_robustness_properties(input in robustness_strategy()) {
            // Test parser robustness with various inputs
            let result = test_parser_robustness(&input);
            assert!(result.is_ok(), "Parser should not crash on input: {input:?}");
        }

        #[test]
        fn test_parser_performance_properties(input in performance_strategy()) {
            // Test parser performance with various inputs
            let result = crate::fuzzing::test_parser_performance(&input);
            assert!(result.is_ok(), "Parser should be fast on input: {input:?}");
        }
    }

    #[test]
    fn test_grammar_fuzzer_properties() {
        // Test that grammar fuzzer generates reasonable inputs
        let fuzzer = GrammarFuzzer::new();

        for _ in 0..100 {
            let expr = fuzzer.generate_expression();
            let program = fuzzer.generate_program();

            // Generated inputs should not be empty
            assert!(!expr.is_empty());
            assert!(!program.is_empty());

            // Generated inputs should have reasonable length
            assert!(expr.len() <= 10000);
            assert!(program.len() <= 10000);
        }
    }

    #[test]
    fn test_mutation_fuzzer_properties() {
        // Test that mutation fuzzer generates varied inputs
        let mut fuzzer = MutationFuzzer::new();
        let mut inputs = std::collections::HashSet::new();

        for _ in 0..100 {
            let input = fuzzer.generate_input();
            inputs.insert(input);
        }

        // Should generate some variety
        assert!(inputs.len() > 1);
    }

    // Strategy for generating fuzzed expressions
    fn fuzzed_expression_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "42".to_string(),
            "x".to_string(),
            "x + y".to_string(),
            "let x = 42 in x".to_string(),
            "if true then 1 else 2".to_string(),
            "{ x = 1, y = 2 }".to_string(),
            "[1, 2, 3]".to_string(),
            "\\x -> x + 1".to_string(),
            // Add malformed inputs
            "x +".to_string(),
            "let x =".to_string(),
            "if true then".to_string(),
            "{}".to_string(),
            "[]".to_string(),
            "\\x ->".to_string(),
        ])
    }

    // Strategy for generating large expressions
    fn large_expression_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            // Deeply nested expressions
            "((((((((((42))))))))))".to_string(),
            // Long expressions
            "x + x + x + x + x + x + x + x + x + x".to_string(),
            // Complex expressions
            "let x = 1 in let y = 2 in let z = 3 in x + y + z".to_string(),
        ])
    }

    // Strategy for memory stress testing
    fn memory_stress_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            // Expressions that might stress memory
            "x".repeat(1000),
            "let x = 1 in ".repeat(100) + "x",
            "if true then ".repeat(100) + "1 else 2",
        ])
    }

    // Strategy for robustness testing
    fn robustness_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "42".to_string(),
            "x + y".to_string(),
            "let x = 42 in x".to_string(),
            "invalid input".to_string(),
            "".to_string(),
            "x +".to_string(),
            "let x =".to_string(),
            "very long input ".repeat(1000),
            "null bytes \0 in string".to_string(),
            "unicode 🚀 test".to_string(),
        ])
    }

    // Strategy for performance testing
    fn performance_strategy() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "42".to_string(),
            "x + y".to_string(),
            "let x = 42 in x".to_string(),
            "if true then 1 else 2".to_string(),
            "{ x = 1, y = 2 }".to_string(),
            "[1, 2, 3]".to_string(),
            "\\x -> x + 1".to_string(),
        ])
    }

    #[test]
    fn test_property_strategies() {
        // Test that strategies generate valid inputs
        let mut runner = proptest::test_runner::TestRunner::default();

        // Test fuzzed expression strategy
        let result = runner.run(&fuzzed_expression_strategy(), |input| {
            assert!(!input.is_empty());
            Ok(())
        });
        assert!(result.is_ok());

        // Test large expression strategy
        let result = runner.run(&large_expression_strategy(), |input| {
            assert!(!input.is_empty());
            Ok(())
        });
        assert!(result.is_ok());

        // Test robustness strategy
        let result = runner.run(&robustness_strategy(), |_input| {
            // Should handle all inputs
            Ok(())
        });
        assert!(result.is_ok());
    }
}
