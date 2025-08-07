# Error Handling Improvements Proposal

## Overview

This proposal outlines a comprehensive approach to improving error handling in Ligature using the `anyhow` crate and other modern Rust error handling techniques. The goal is to provide better error messages, improved error recovery, and more robust error handling throughout the language implementation.

## Problem Statement

### Current Error Handling Limitations

Ligature's current error handling has several limitations:

1. **Inconsistent Error Types**: Different components use different error types
2. **Poor Error Messages**: Error messages may not be user-friendly or informative
3. **Limited Error Context**: Errors lack sufficient context for debugging
4. **No Error Recovery**: Limited ability to recover from errors gracefully
5. **Manual Error Propagation**: Verbose error handling code throughout the codebase

### Areas Needing Improvement

1. **Parser Errors**: Better syntax error reporting and recovery
2. **Type Errors**: More informative type checking error messages
3. **Evaluation Errors**: Runtime error handling and recovery
4. **Module Errors**: Import and module resolution error handling
5. **CLI Errors**: User-friendly error messages for command-line tools

## Design Philosophy

### Core Principles

1. **User-Friendly**: Error messages should be clear and actionable
2. **Contextual**: Errors should include relevant context and suggestions
3. **Recoverable**: Where possible, errors should allow for recovery
4. **Consistent**: Error handling should be consistent across components
5. **Debuggable**: Errors should provide sufficient information for debugging

### Error Handling Patterns

1. **Result Types**: Use `Result<T, E>` consistently
2. **Error Context**: Add context to errors using `anyhow::Context`
3. **Error Chaining**: Chain errors to preserve error history
4. **Custom Error Types**: Define specific error types for different domains
5. **Error Recovery**: Implement recovery strategies where appropriate

## Proposed Solution

### 1. Anyhow Integration

#### Core Error Type

```rust
use anyhow::{Context, Result, anyhow, bail};
use thiserror::Error;

// Main error type for Ligature
pub type LigatureResult<T> = Result<T>;

// Custom error types for specific domains
#[derive(Error, Debug)]
pub enum LigatureError {
    #[error("Parse error: {message}")]
    Parse {
        message: String,
        span: Span,
        suggestions: Vec<String>,
    },

    #[error("Type error: {message}")]
    Type {
        message: String,
        span: Span,
        expected: Option<Type>,
        found: Option<Type>,
        suggestions: Vec<String>,
    },

    #[error("Evaluation error: {message}")]
    Evaluation {
        message: String,
        span: Span,
        context: Option<String>,
    },

    #[error("Module error: {message}")]
    Module {
        message: String,
        path: Option<PathBuf>,
        cause: Option<Box<dyn std::error::Error + Send + Sync>>,
    },

    #[error("Configuration error: {message}")]
    Configuration {
        message: String,
        field: Option<String>,
        value: Option<String>,
    },
}

// Span for error locations
#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
    pub file: Option<PathBuf>,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            line: 0,
            column: 0,
            file: None,
        }
    }

    pub fn with_location(mut self, line: usize, column: usize) -> Self {
        self.line = line;
        self.column = column;
        self
    }

    pub fn with_file(mut self, file: PathBuf) -> Self {
        self.file = Some(file);
        self
    }

    pub fn is_valid(&self) -> bool {
        self.start <= self.end
    }

    pub fn display(&self, source: &str) -> String {
        if let Some(file) = &self.file {
            format!("{}:{}:{}", file.display(), self.line, self.column)
        } else {
            format!("line {}:{}", self.line, self.column)
        }
    }
}
```

#### Error Context and Chaining

```rust
use anyhow::{Context, Result};

pub struct Parser {
    source: String,
    errors: Vec<LigatureError>,
}

impl Parser {
    pub fn parse_expression(&mut self, input: &str) -> LigatureResult<Expr> {
        let tokens = self.lex(input)
            .context("Failed to tokenize input")?;

        let ast = self.parse_tokens(&tokens)
            .context("Failed to parse tokens into AST")?;

        Ok(ast)
    }

    pub fn parse_program(&mut self, input: &str) -> LigatureResult<Program> {
        let program = self.parse_expression(input)
            .context("Failed to parse program")
            .with_context(|| format!("Input: {}", input))?;

        Ok(Program {
            declarations: vec![program],
        })
    }

    fn lex(&self, input: &str) -> LigatureResult<Vec<Token>> {
        // Lexer implementation with error context
        let mut tokens = Vec::new();
        let mut pos = 0;

        while pos < input.len() {
            let token = self.lex_token(&input[pos..])
                .with_context(|| format!("Failed to lex token at position {}", pos))?;

            tokens.push(token);
            pos += token.length;
        }

        Ok(tokens)
    }

    fn lex_token(&self, input: &str) -> LigatureResult<Token> {
        // Token lexing with detailed error context
        if input.is_empty() {
            bail!("Unexpected end of input");
        }

        let first_char = input.chars().next().unwrap();

        match first_char {
            '0'..='9' => self.lex_number(input),
            'a'..='z' | 'A'..='Z' | '_' => self.lex_identifier(input),
            '"' => self.lex_string(input),
            '+' | '-' | '*' | '/' => self.lex_operator(input),
            '(' | ')' | '{' | '}' | '[' | ']' => self.lex_delimiter(input),
            _ => {
                let span = Span::new(0, 1);
                Err(LigatureError::Parse {
                    message: format!("Unexpected character: '{}'", first_char),
                    span,
                    suggestions: vec![
                        "Expected a number, identifier, or operator".to_string(),
                        "Check for typos or invalid characters".to_string(),
                    ],
                }.into())
            }
        }
    }
}
```

### 2. Type System Error Handling

#### Type Error Context

```rust
pub struct TypeChecker {
    environment: TypeEnvironment,
    errors: Vec<LigatureError>,
}

impl TypeChecker {
    pub fn check_expression(&mut self, expr: &Expr) -> LigatureResult<Type> {
        match expr {
            Expr::Literal(lit) => self.check_literal(lit),
            Expr::Identifier(id) => self.check_identifier(id),
            Expr::BinaryOp { left, op, right } => {
                self.check_binary_operation(left, op, right)
            }
            Expr::Function { params, body } => {
                self.check_function(params, body)
            }
            Expr::Application { func, args } => {
                self.check_application(func, args)
            }
            _ => {
                let span = expr.span();
                Err(LigatureError::Type {
                    message: "Unsupported expression type".to_string(),
                    span,
                    expected: None,
                    found: None,
                    suggestions: vec![
                        "This expression type is not yet supported".to_string(),
                        "Consider using a different expression form".to_string(),
                    ],
                }.into())
            }
        }
    }

    fn check_binary_operation(
        &mut self,
        left: &Expr,
        op: &BinaryOp,
        right: &Expr,
    ) -> LigatureResult<Type> {
        let left_type = self.check_expression(left)
            .with_context(|| "Failed to type check left operand")?;

        let right_type = self.check_expression(right)
            .with_context(|| "Failed to type check right operand")?;

        // Check operator compatibility
        match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                if left_type != Type::Integer || right_type != Type::Integer {
                    let span = left.span().merge(right.span());
                    return Err(LigatureError::Type {
                        message: format!("Cannot apply operator '{}' to types '{}' and '{}'",
                                       op, left_type, right_type),
                        span,
                        expected: Some(Type::Integer),
                        found: Some(left_type),
                        suggestions: vec![
                            "Both operands must be integers".to_string(),
                            format!("Consider converting '{}' to integer", right_type),
                        ],
                    }.into());
                }
                Ok(Type::Integer)
            }
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                if left_type != right_type {
                    let span = left.span().merge(right.span());
                    return Err(LigatureError::Type {
                        message: format!("Cannot compare types '{}' and '{}'", left_type, right_type),
                        span,
                        expected: Some(left_type.clone()),
                        found: Some(right_type),
                        suggestions: vec![
                            "Both operands must have the same type".to_string(),
                            "Consider converting one operand to match the other".to_string(),
                        ],
                    }.into());
                }
                Ok(Type::Boolean)
            }
        }
    }

    fn check_function(
        &mut self,
        params: &[Parameter],
        body: &Expr,
    ) -> LigatureResult<Type> {
        // Create new scope for function parameters
        let mut new_env = self.environment.clone();

        for param in params {
            new_env.bind(param.name.clone(), param.type_.clone())
                .with_context(|| format!("Failed to bind parameter '{}'", param.name))?;
        }

        // Type check body in new environment
        let old_env = std::mem::replace(&mut self.environment, new_env);
        let body_type = self.check_expression(body)
            .with_context(|| "Failed to type check function body")?;
        self.environment = old_env;

        // Construct function type
        let param_types: Vec<Type> = params.iter().map(|p| p.type_.clone()).collect();
        Ok(Type::Function {
            params: param_types,
            return_type: Box::new(body_type),
        })
    }
}
```

### 3. Evaluation Error Handling

#### Runtime Error Context

```rust
pub struct Evaluator {
    environment: EvaluationEnvironment,
    errors: Vec<LigatureError>,
}

impl Evaluator {
    pub fn evaluate_expression(&mut self, expr: &Expr) -> LigatureResult<Value> {
        match expr {
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::Identifier(id) => self.evaluate_identifier(id),
            Expr::BinaryOp { left, op, right } => {
                self.evaluate_binary_operation(left, op, right)
            }
            Expr::Function { params, body } => {
                self.evaluate_function(params, body)
            }
            Expr::Application { func, args } => {
                self.evaluate_application(func, args)
            }
            _ => {
                let span = expr.span();
                Err(LigatureError::Evaluation {
                    message: "Unsupported expression during evaluation".to_string(),
                    span,
                    context: Some("This expression type cannot be evaluated".to_string()),
                }.into())
            }
        }
    }

    fn evaluate_binary_operation(
        &mut self,
        left: &Expr,
        op: &BinaryOp,
        right: &Expr,
    ) -> LigatureResult<Value> {
        let left_val = self.evaluate_expression(left)
            .with_context(|| "Failed to evaluate left operand")?;

        let right_val = self.evaluate_expression(right)
            .with_context(|| "Failed to evaluate right operand")?;

        match (left_val, op, right_val) {
            (Value::Integer(l), BinaryOp::Add, Value::Integer(r)) => {
                Ok(Value::Integer(l + r))
            }
            (Value::Integer(l), BinaryOp::Sub, Value::Integer(r)) => {
                Ok(Value::Integer(l - r))
            }
            (Value::Integer(l), BinaryOp::Mul, Value::Integer(r)) => {
                Ok(Value::Integer(l * r))
            }
            (Value::Integer(l), BinaryOp::Div, Value::Integer(r)) => {
                if r == 0 {
                    let span = left.span().merge(right.span());
                    return Err(LigatureError::Evaluation {
                        message: "Division by zero".to_string(),
                        span,
                        context: Some("Cannot divide by zero".to_string()),
                    }.into());
                }
                Ok(Value::Integer(l / r))
            }
            (l, op, r) => {
                let span = left.span().merge(right.span());
                Err(LigatureError::Evaluation {
                    message: format!("Cannot apply operator '{}' to values of types '{}' and '{}'",
                                   op, l.type_name(), r.type_name()),
                    span,
                    context: Some("Operator not supported for these value types".to_string()),
                }.into())
            }
        }
    }

    fn evaluate_identifier(&self, id: &str) -> LigatureResult<Value> {
        self.environment.lookup(id)
            .ok_or_else(|| {
                LigatureError::Evaluation {
                    message: format!("Undefined identifier: '{}'", id),
                    span: Span::new(0, 0), // Would need to get from AST
                    context: Some("Variable not found in current scope".to_string()),
                }
            })
    }

    fn evaluate_application(
        &mut self,
        func: &Expr,
        args: &[Expr],
    ) -> LigatureResult<Value> {
        let func_val = self.evaluate_expression(func)
            .with_context(|| "Failed to evaluate function expression")?;

        let arg_vals: LigatureResult<Vec<Value>> = args
            .iter()
            .map(|arg| self.evaluate_expression(arg))
            .collect();

        let arg_vals = arg_vals
            .with_context(|| "Failed to evaluate function arguments")?;

        match func_val {
            Value::Function { params, body, closure } => {
                if params.len() != arg_vals.len() {
                    return Err(LigatureError::Evaluation {
                        message: format!("Function expects {} arguments, but {} were provided",
                                       params.len(), arg_vals.len()),
                        span: func.span(),
                        context: Some("Check the number of arguments in function call".to_string()),
                    }.into());
                }

                // Apply function
                self.apply_function(params, body, arg_vals, closure)
            }
            _ => {
                Err(LigatureError::Evaluation {
                    message: format!("Cannot apply non-function value: {}", func_val.type_name()),
                    span: func.span(),
                    context: Some("Only functions can be applied to arguments".to_string()),
                }.into())
            }
        }
    }
}
```

### 4. Module Error Handling

#### Module Resolution Errors

```rust
pub struct ModuleResolver {
    search_paths: Vec<PathBuf>,
    cache: HashMap<PathBuf, Module>,
}

impl ModuleResolver {
    pub fn resolve_module(&self, path: &str) -> LigatureResult<Module> {
        // Try to find module file
        let module_path = self.find_module_file(path)
            .with_context(|| format!("Failed to find module: {}", path))?;

        // Load and parse module
        let source = std::fs::read_to_string(&module_path)
            .with_context(|| format!("Failed to read module file: {}", module_path.display()))?;

        let mut parser = Parser::new();
        let program = parser.parse_program(&source)
            .with_context(|| format!("Failed to parse module: {}", path))?;

        let module = Module {
            name: path.to_string(),
            declarations: program.declarations,
            path: module_path,
        };

        Ok(module)
    }

    fn find_module_file(&self, path: &str) -> LigatureResult<PathBuf> {
        // Try different file extensions
        let extensions = ["lig", "ligature"];

        for search_path in &self.search_paths {
            for ext in &extensions {
                let mut module_path = search_path.clone();
                module_path.push(format!("{}.{}", path, ext));

                if module_path.exists() {
                    return Ok(module_path);
                }
            }
        }

        // Try directory with mod.lig file
        for search_path in &self.search_paths {
            let mut module_path = search_path.clone();
            module_path.push(path);
            module_path.push("mod.lig");

            if module_path.exists() {
                return Ok(module_path);
            }
        }

        Err(LigatureError::Module {
            message: format!("Module not found: {}", path),
            path: None,
            cause: None,
        }.into())
    }
}
```

### 5. CLI Error Handling

#### User-Friendly Error Messages

```rust
use anyhow::{Context, Result};
use clap::Parser as ClapParser;

#[derive(ClapParser)]
#[command(name = "ligature")]
#[command(about = "Ligature configuration language")]
struct Cli {
    #[arg(short, long)]
    file: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,
}

impl Cli {
    pub fn run() -> Result<()> {
        let cli = Cli::parse();

        if let Some(file) = cli.file {
            Self::process_file(&file, cli.verbose)
        } else {
            Self::process_stdin(cli.verbose)
        }
    }

    fn process_file(file: &Path, verbose: bool) -> Result<()> {
        // Read file
        let source = std::fs::read_to_string(file)
            .with_context(|| format!("Failed to read file: {}", file.display()))?;

        // Parse and evaluate
        let result = Self::process_source(&source, file);

        match result {
            Ok(value) => {
                println!("{}", value);
                Ok(())
            }
            Err(e) => {
                if verbose {
                    eprintln!("Error: {:?}", e);
                } else {
                    eprintln!("Error: {}", e);
                }
                Err(e)
            }
        }
    }

    fn process_source(source: &str, file: &Path) -> Result<Value> {
        let mut parser = Parser::new();
        let program = parser.parse_program(source)
            .with_context(|| format!("Failed to parse file: {}", file.display()))?;

        let mut type_checker = TypeChecker::new();
        type_checker.check_program(&program)
            .with_context(|| "Type checking failed")?;

        let mut evaluator = Evaluator::new();
        evaluator.evaluate_program(&program)
            .with_context(|| "Evaluation failed")
    }

    fn process_stdin(verbose: bool) -> Result<()> {
        use std::io::{self, BufRead};

        let stdin = io::stdin();
        let mut handle = stdin.lock();
        let mut buffer = String::new();

        while handle.read_line(&mut buffer)? > 0 {
            let result = Self::process_source(&buffer, Path::new("<stdin>"));

            match result {
                Ok(value) => println!("{}", value),
                Err(e) => {
                    if verbose {
                        eprintln!("Error: {:?}", e);
                    } else {
                        eprintln!("Error: {}", e);
                    }
                }
            }

            buffer.clear();
        }

        Ok(())
    }
}
```

## Implementation Strategy

### Phase 1: Anyhow Integration (Immediate - 2-3 weeks)

#### Goals

- Add anyhow dependency
- Implement basic error types
- Add error context throughout codebase

#### Implementation Tasks

1. **Add Dependencies**

```toml
[dependencies]
anyhow = "1.0"
thiserror = "1.0"
```

2. **Define Error Types**

```rust
use anyhow::{Context, Result};
use thiserror::Error;

pub type LigatureResult<T> = Result<T>;

#[derive(Error, Debug)]
pub enum LigatureError {
    #[error("Parse error: {message}")]
    Parse {
        message: String,
        span: Span,
        suggestions: Vec<String>,
    },

    #[error("Type error: {message}")]
    Type {
        message: String,
        span: Span,
        expected: Option<Type>,
        found: Option<Type>,
        suggestions: Vec<String>,
    },

    #[error("Evaluation error: {message}")]
    Evaluation {
        message: String,
        span: Span,
        context: Option<String>,
    },
}
```

3. **Update Function Signatures**

```rust
// Before
pub fn parse_expression(input: &str) -> Result<Expr, ParseError> {
    // Implementation
}

// After
pub fn parse_expression(input: &str) -> LigatureResult<Expr> {
    // Implementation with context
}
```

### Phase 2: Error Context (Short-term - 4-6 weeks)

#### Goals

- Add comprehensive error context
- Implement error chaining
- Add user-friendly error messages

#### Implementation Tasks

1. **Error Context Implementation**

```rust
impl Parser {
    pub fn parse_expression(&mut self, input: &str) -> LigatureResult<Expr> {
        let tokens = self.lex(input)
            .context("Failed to tokenize input")?;

        let ast = self.parse_tokens(&tokens)
            .context("Failed to parse tokens into AST")?;

        Ok(ast)
    }
}
```

2. **User-Friendly Error Messages**

```rust
impl LigatureError {
    pub fn with_suggestions(mut self, suggestions: Vec<String>) -> Self {
        match &mut self {
            LigatureError::Parse { suggestions: s, .. } => *s = suggestions,
            LigatureError::Type { suggestions: s, .. } => *s = suggestions,
            _ => {}
        }
        self
    }

    pub fn display(&self, source: &str) -> String {
        match self {
            LigatureError::Parse { message, span, suggestions } => {
                let mut output = format!("Parse error: {}\n", message);
                output.push_str(&span.display(source));
                if !suggestions.is_empty() {
                    output.push_str("\nSuggestions:\n");
                    for suggestion in suggestions {
                        output.push_str(&format!("  - {}\n", suggestion));
                    }
                }
                output
            }
            // Similar for other error types
            _ => self.to_string(),
        }
    }
}
```

### Phase 3: Error Recovery (Medium-term - 6-8 weeks)

#### Goals

- Implement error recovery strategies
- Add error reporting improvements
- Implement error aggregation

#### Implementation Tasks

1. **Error Recovery Strategies**

```rust
pub struct ErrorRecovery {
    strategies: Vec<Box<dyn RecoveryStrategy>>,
}

pub trait RecoveryStrategy {
    fn can_recover(&self, error: &LigatureError) -> bool;
    fn recover(&self, error: &LigatureError) -> LigatureResult<()>;
}

impl ErrorRecovery {
    pub fn new() -> Self {
        let strategies: Vec<Box<dyn RecoveryStrategy>> = vec![
            Box::new(SkipToSemicolon),
            Box::new(InsertMissingToken),
            Box::new(SkipToClosingBrace),
        ];

        Self { strategies }
    }

    pub fn try_recover(&self, error: &LigatureError) -> LigatureResult<()> {
        for strategy in &self.strategies {
            if strategy.can_recover(error) {
                return strategy.recover(error);
            }
        }

        Err(error.clone().into())
    }
}
```

2. **Error Aggregation**

```rust
pub struct ErrorCollector {
    errors: Vec<LigatureError>,
    max_errors: usize,
}

impl ErrorCollector {
    pub fn new(max_errors: usize) -> Self {
        Self {
            errors: Vec::new(),
            max_errors,
        }
    }

    pub fn add_error(&mut self, error: LigatureError) -> bool {
        if self.errors.len() < self.max_errors {
            self.errors.push(error);
            true
        } else {
            false
        }
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn into_errors(self) -> Vec<LigatureError> {
        self.errors
    }
}
```

### Phase 4: Advanced Error Handling (Long-term - 8-12 weeks)

#### Goals

- Implement advanced error reporting
- Add error diagnostics
- Implement error suppression

#### Implementation Tasks

1. **Advanced Error Reporting**

```rust
pub struct ErrorReporter {
    source: String,
    errors: Vec<LigatureError>,
    config: ErrorReportConfig,
}

pub struct ErrorReportConfig {
    pub show_source: bool,
    pub show_suggestions: bool,
    pub max_errors: usize,
    pub color_output: bool,
}

impl ErrorReporter {
    pub fn new(source: String, config: ErrorReportConfig) -> Self {
        Self {
            source,
            errors: Vec::new(),
            config,
        }
    }

    pub fn add_error(&mut self, error: LigatureError) {
        self.errors.push(error);
    }

    pub fn report(&self) -> String {
        let mut output = String::new();

        for error in &self.errors {
            output.push_str(&self.format_error(error));
            output.push('\n');
        }

        output
    }

    fn format_error(&self, error: &LigatureError) -> String {
        match error {
            LigatureError::Parse { message, span, suggestions } => {
                let mut output = String::new();

                if self.config.color_output {
                    output.push_str("\x1b[31m"); // Red
                }
                output.push_str("error: ");
                output.push_str(message);
                if self.config.color_output {
                    output.push_str("\x1b[0m"); // Reset
                }
                output.push('\n');

                if self.config.show_source {
                    output.push_str(&self.format_source_span(span));
                }

                if self.config.show_suggestions && !suggestions.is_empty() {
                    output.push_str("help:\n");
                    for suggestion in suggestions {
                        output.push_str(&format!("  {}\n", suggestion));
                    }
                }

                output
            }
            // Similar for other error types
            _ => error.to_string(),
        }
    }

    fn format_source_span(&self, span: &Span) -> String {
        // Format source code with error highlighting
        let lines: Vec<&str> = self.source.lines().collect();
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
            format!("  --> unknown location\n")
        }
    }
}
```

## Configuration and Usage

### Basic Usage

```rust
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let file = std::env::args().nth(1)
        .context("No file specified")?;

    let source = std::fs::read_to_string(&file)
        .with_context(|| format!("Failed to read file: {}", file))?;

    let mut parser = Parser::new();
    let program = parser.parse_program(&source)
        .with_context(|| "Failed to parse program")?;

    println!("Parsed successfully!");
    Ok(())
}
```

### Advanced Usage

```rust
use anyhow::{Context, Result, anyhow};

fn process_config(config: &Config) -> Result<()> {
    // Validate configuration
    if config.timeout == 0 {
        return Err(anyhow!("Timeout must be greater than 0"));
    }

    if config.workers == 0 {
        return Err(anyhow!("Number of workers must be greater than 0"));
    }

    // Process configuration
    let result = process_with_config(config)
        .with_context(|| "Failed to process configuration")?;

    Ok(result)
}

fn process_with_config(config: &Config) -> Result<()> {
    // Implementation with detailed error context
    for (key, value) in &config.settings {
        validate_setting(key, value)
            .with_context(|| format!("Invalid setting: {}", key))?;
    }

    Ok(())
}
```

### CLI Integration

```rust
use clap::Parser;

#[derive(Parser)]
struct Cli {
    #[arg(short, long)]
    file: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(file) = cli.file {
        process_file(&file, cli.verbose)
    } else {
        process_stdin(cli.verbose)
    }
}

fn process_file(file: &Path, verbose: bool) -> Result<()> {
    let source = std::fs::read_to_string(file)
        .with_context(|| format!("Failed to read file: {}", file.display()))?;

    let result = process_source(&source);

    match result {
        Ok(value) => {
            println!("{}", value);
            Ok(())
        }
        Err(e) => {
            if verbose {
                eprintln!("Error: {:?}", e);
            } else {
                eprintln!("Error: {}", e);
            }
            Err(e)
        }
    }
}
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_error_context() {
    let result = parse_expression("invalid syntax");
    assert!(result.is_err());

    let error = result.unwrap_err();
    let error_string = error.to_string();

    assert!(error_string.contains("Failed to parse"));
    assert!(error_string.contains("invalid syntax"));
}

#[test]
fn test_error_chaining() {
    let result = process_file("nonexistent.lig");
    assert!(result.is_err());

    let error = result.unwrap_err();
    let error_string = error.to_string();

    assert!(error_string.contains("Failed to read file"));
    assert!(error_string.contains("nonexistent.lig"));
}
```

### Integration Tests

```rust
#[test]
fn test_error_recovery() {
    let mut parser = Parser::new();
    let mut error_collector = ErrorCollector::new(10);

    let source = "let x = 42\nlet y = x + 1\nlet z = y * 2";
    let result = parser.parse_program_with_recovery(source, &mut error_collector);

    // Should recover from some errors
    assert!(result.is_ok() || error_collector.has_errors());
}

#[test]
fn test_error_reporting() {
    let source = "let x = 42\nlet y = x + \nlet z = y * 2";
    let mut parser = Parser::new();
    let result = parser.parse_program(source);

    assert!(result.is_err());

    let error = result.unwrap_err();
    let error_string = error.to_string();

    // Should contain helpful information
    assert!(error_string.contains("unexpected end of input"));
    assert!(error_string.contains("line 2"));
}
```

## Migration Strategy

### Backward Compatibility

1. **Gradual Migration**: Update error types incrementally
2. **Feature Flags**: Enable/disable new error handling via features
3. **Fallback Support**: Maintain support for old error types during transition
4. **Documentation**: Clear migration guide for users

### Migration Path

1. **Phase 1**: Add anyhow without changing public APIs
2. **Phase 2**: Update internal error handling
3. **Phase 3**: Update public APIs with new error types
4. **Phase 4**: Remove old error handling code

### Migration Examples

```rust
// Before: Manual error handling
pub fn parse_expression(input: &str) -> Result<Expr, ParseError> {
    match parse_tokens(input) {
        Ok(tokens) => parse_ast(tokens),
        Err(e) => Err(ParseError::Tokenization(e)),
    }
}

// After: Anyhow error handling
pub fn parse_expression(input: &str) -> LigatureResult<Expr> {
    let tokens = parse_tokens(input)
        .context("Failed to tokenize input")?;

    parse_ast(tokens)
        .context("Failed to parse AST")
}
```

## Risks and Mitigations

### 1. Performance Impact

**Risk**: Error handling overhead may impact performance
**Mitigation**:

- Use error handling only when needed
- Optimize error context creation
- Profile and optimize hot paths
- Use error handling judiciously

### 2. Error Message Quality

**Risk**: Error messages may not be helpful
**Mitigation**:

- Comprehensive testing of error messages
- User feedback and iteration
- Clear documentation of error meanings
- Regular review of error messages

### 3. Error Recovery Complexity

**Risk**: Error recovery may be complex to implement
**Mitigation**:

- Start with simple recovery strategies
- Comprehensive testing of recovery
- Clear documentation of recovery behavior
- Gradual introduction of complex recovery

### 4. Backward Compatibility

**Risk**: Changes may break existing code
**Mitigation**:

- Gradual migration strategy
- Feature flags for new error handling
- Comprehensive testing
- Clear migration documentation

## Success Metrics

### Technical Metrics

1. **Error Clarity**: Reduction in user confusion about errors
2. **Error Recovery**: Success rate of error recovery
3. **Performance**: Minimal impact on performance
4. **Coverage**: Percentage of errors with helpful context

### User Experience Metrics

1. **User Satisfaction**: Feedback on error message quality
2. **Debugging Time**: Time to resolve issues
3. **Error Reports**: Reduction in unclear error reports
4. **Documentation**: Quality of error documentation

## Conclusion

This proposal provides a comprehensive approach to improving error handling in Ligature using anyhow and modern Rust error handling techniques. The gradual introduction ensures minimal disruption while providing significant benefits for error clarity and user experience.

The key benefits include:

1. **Better Error Messages**: Clear, actionable error messages
2. **Error Context**: Rich context for debugging
3. **Error Recovery**: Ability to recover from some errors
4. **Consistency**: Consistent error handling across components
5. **User Experience**: Improved developer experience

The implementation strategy provides a clear path forward with measurable milestones and comprehensive testing to ensure effectiveness and reliability.

## References

1. [Anyhow Documentation](https://docs.rs/anyhow/)
2. [ThisError Documentation](https://docs.rs/thiserror/)
3. [Rust Error Handling Book](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
4. [Error Handling Best Practices](https://blog.burntsushi.net/rust-error-handling/)
5. [User-Friendly Error Messages](https://rust-lang.github.io/rfcs/0236-error-conventions.html)
