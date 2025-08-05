# Ligature Developer Guide

**Last Updated**: January 2025  
**Status**: Production Ready ✅

Welcome to the Ligature Developer Guide! This document provides comprehensive information for developers who want to contribute to Ligature, understand its internals, or integrate it into their projects.

## 🚀 **Quick Start for Developers**

### **Prerequisites**

- **Rust 1.75+**: Latest stable Rust toolchain
- **Just**: Command runner for development workflows (`cargo install just`)
- **VS Code**: Recommended IDE with Ligature extension
- **Git**: Version control system

### **Development Setup**

```bash
# Clone the repository
git clone https://github.com/ligature-lang/ligature.git
cd ligature

# Install dependencies and build
just install

# Run tests to verify setup
just test

# Start development
just dev
```

## 🏗️ **Project Structure**

### **Core Crates**

```
crates/
├── ligature-ast/          # Abstract Syntax Tree definitions
├── ligature-parser/       # Language parser and grammar
├── ligature-types/        # Type system and inference
├── ligature-eval/         # Evaluation engine and optimization
├── ligature-lsp/          # Language Server Protocol implementation
└── ligature-xdg/          # Configuration management
```

### **Applications**

```
apps/
├── reed/                  # Command Line Interface
├── cacophony/            # Configuration orchestration
├── keywork/              # Package manager
└── performance-monitor/  # Performance analysis tool
```

### **Documentation**

```
docs/
├── user-guide/           # User documentation
├── architecture/         # System architecture
├── analysis/            # Technical analysis
└── examples/            # Code examples
```

## 🔧 **Development Workflows**

### **Using Justfile Commands**

The project uses a comprehensive `justfile` for streamlined development:

```bash
# Build all components
just build

# Run all tests
just test

# Run specific test suites
just test-unit
just test-integration
just test-performance

# Run benchmarks
just bench

# Check code quality
just check
just clippy
just fmt

# Development tools
just reed parse --file examples/config.lig
just reed typecheck --file examples/config.lig
just reed eval --file examples/config.lig

# Performance monitoring
just performance-monitor
```

### **IDE Integration**

#### **VS Code Setup**

1. **Install Ligature Extension**:

   ```bash
   cd apps/editor-plugins/vscode-ligature
   npm install
   npm run build
   ```

2. **Configure LSP Server**:

   ```json
   {
     "ligature.server.path": "./target/debug/ligature-lsp",
     "ligature.server.args": ["--log-level=debug"]
   }
   ```

3. **Enable Features**:
   - Syntax highlighting
   - Code completion
   - Error diagnostics
   - Symbol navigation
   - Refactoring tools

#### **LSP Development**

The LSP server provides comprehensive IDE integration:

```rust
// Example: Adding a new LSP feature
pub trait LspProvider {
    async fn provide_completion(&self, params: CompletionParams) -> Result<Vec<CompletionItem>, ServerError>;
    async fn provide_definition(&self, params: DefinitionParams) -> Result<Option<Location>, ServerError>;
    async fn provide_references(&self, params: ReferenceParams) -> Result<Vec<Location>, ServerError>;
}
```

## 🧪 **Testing Strategy**

### **Test Organization**

```
tests/
├── integration/          # End-to-end tests
├── property/            # Property-based tests
├── performance/         # Performance tests
├── registers/           # Register system tests
└── fixtures/            # Test data and examples
```

### **Writing Tests**

#### **Unit Tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_optimization() {
        let input = "let add = \\x y -> x + y; add 5 3";
        let result = evaluate(input).unwrap();
        assert_eq!(result, Value::Integer(8));
    }
}
```

#### **Integration Tests**

```rust
#[test]
fn test_complete_workflow() {
    // Test complete parse -> typecheck -> evaluate workflow
    let source = include_str!("../fixtures/config.lig");
    let ast = parse(source).unwrap();
    let typed = typecheck(ast).unwrap();
    let result = evaluate(typed).unwrap();
    assert!(result.is_valid());
}
```

#### **Property-Based Tests**

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_arithmetic_properties(a: i64, b: i64) {
        let result = evaluate_arithmetic(a, b);
        prop_assert!(result.is_valid());
    }
}
```

### **Performance Testing**

```rust
#[bench]
fn bench_function_calls(b: &mut Bencher) {
    b.iter(|| {
        evaluate_function_calls(test_data())
    });
}
```

## 🔍 **Debugging and Profiling**

### **Debugging Tools**

#### **LSP Debugging**

```bash
# Run LSP server in debug mode
RUST_LOG=debug ligature-lsp --log-level=debug

# Connect VS Code debugger
# Add to launch.json:
{
    "name": "Debug LSP",
    "type": "lldb",
    "request": "launch",
    "program": "${workspaceFolder}/target/debug/ligature-lsp",
    "args": ["--log-level=debug"]
}
```

#### **Performance Profiling**

```bash
# Run performance monitor
just performance-monitor

# Generate performance report
just performance-monitor --report=json

# Monitor specific operations
just performance-monitor --operation=function-calls
```

### **Memory Profiling**

```rust
use sysinfo::{System, SystemExt};

fn profile_memory_usage() {
    let mut sys = System::new_all();
    sys.refresh_all();

    println!("Memory usage: {} MB", sys.used_memory() / 1024 / 1024);
}
```

## 📚 **API Documentation**

### **Core APIs**

#### **Parser API**

```rust
use ligature_parser::{parse, ParseError};

// Parse Ligature source code
let result: Result<Program, ParseError> = parse(source_code);

// Parse with custom options
let options = ParseOptions {
    allow_unknown_operators: false,
    strict_mode: true,
};
let result = parse_with_options(source_code, options);
```

#### **Type System API**

```rust
use ligature_types::{typecheck, TypeEnvironment, TypeError};

// Type check a program
let env = TypeEnvironment::new();
let result: Result<TypedProgram, TypeError> = typecheck(ast, &env);

// Create type environment with imports
let mut env = TypeEnvironment::new();
env.load_module("std.collections")?;
```

#### **Evaluation API**

```rust
use ligature_eval::{evaluate, EvaluationOptions, Value};

// Evaluate a program
let options = EvaluationOptions {
    enable_caching: true,
    enable_optimization: true,
    max_iterations: 1000,
};
let result: Result<Value, EvaluationError> = evaluate(typed_program, options);

// Evaluate with custom environment
let mut env = Environment::new();
env.bind("x", Value::Integer(42));
let result = evaluate_with_environment(program, env);
```

#### **LSP API**

```rust
use ligature_lsp::{LigatureLspServer, DocumentState};

// Create LSP server
let server = LigatureLspServer::new(config)?;

// Handle document changes
let state = DocumentState {
    content: source_code.to_string(),
    ast: Some(parsed_ast),
    version: 1,
};
server.update_document(uri, state)?;
```

### **Configuration API**

```rust
use ligature_xdg::{load_config, ConfigValidator, ConfigSchema};

// Load configuration
let config = load_config("ligature-cli.toml")?;

// Validate configuration
let schema = ConfigSchema::new()
    .field("log_level", FieldType::String)
    .field("cache_size", FieldType::Integer)
    .build();
let validator = ConfigValidator::new(schema);
validator.validate(&config)?;
```

## 🔧 **Contributing Guidelines**

### **Code Style**

- **Rustfmt**: All code must be formatted with `rustfmt`
- **Clippy**: All code must pass `clippy` checks
- **Documentation**: All public APIs must be documented
- **Tests**: All new features must include tests

### **Commit Guidelines**

```
type(scope): description

feat(parser): add support for new operator precedence
fix(eval): resolve memory leak in function caching
docs(lsp): update symbol finding documentation
test(types): add property-based tests for type inference
```

### **Pull Request Process**

1. **Create Feature Branch**: `git checkout -b feature/new-feature`
2. **Implement Changes**: Follow coding standards and add tests
3. **Run Tests**: `just test` and `just bench`
4. **Update Documentation**: Update relevant documentation
5. **Submit PR**: Include description and test results

### **Review Process**

- **Code Review**: All changes require review
- **CI Checks**: Must pass all automated checks
- **Performance**: Must not regress performance
- **Documentation**: Must include appropriate documentation

## 🚀 **Performance Guidelines**

### **Optimization Principles**

1. **Measure First**: Always profile before optimizing
2. **Cache Wisely**: Use expression caching for expensive operations
3. **Avoid Allocations**: Reuse objects and minimize allocations
4. **Parallelize**: Use parallel evaluation where appropriate

### **Performance Testing**

```rust
// Benchmark critical paths
#[bench]
fn bench_critical_operation(b: &mut Bencher) {
    let test_data = generate_test_data();
    b.iter(|| {
        critical_operation(&test_data)
    });
}

// Performance regression tests
#[test]
fn test_performance_regression() {
    let start = Instant::now();
    perform_operation();
    let duration = start.elapsed();
    assert!(duration < Duration::from_millis(100));
}
```

## 🔒 **Security Considerations**

### **Input Validation**

- **Parser Security**: Validate all input before parsing
- **Type Safety**: Ensure type safety throughout evaluation
- **Resource Limits**: Implement resource limits for evaluation

### **Error Handling**

```rust
// Proper error handling
pub fn safe_evaluate(source: &str) -> Result<Value, Box<dyn Error>> {
    // Validate input
    if source.len() > MAX_SOURCE_SIZE {
        return Err("Source too large".into());
    }

    // Parse with error handling
    let ast = parse(source)
        .map_err(|e| format!("Parse error: {}", e))?;

    // Type check with error handling
    let typed = typecheck(ast)
        .map_err(|e| format!("Type error: {}", e))?;

    // Evaluate with resource limits
    let options = EvaluationOptions {
        max_iterations: 1000,
        max_memory: 1024 * 1024, // 1MB
        timeout: Duration::from_secs(30),
    };

    evaluate(typed, options)
        .map_err(|e| format!("Evaluation error: {}", e))
}
```

## 📊 **Monitoring and Observability**

### **Logging**

```rust
use tracing::{info, warn, error, debug};

// Structured logging
info!(
    operation = "evaluation",
    duration_ms = %duration.as_millis(),
    cache_hits = cache_stats.hits,
    "Evaluation completed"
);
```

### **Metrics**

```rust
use metrics::{counter, histogram, gauge};

// Track performance metrics
histogram!("evaluation.duration", duration.as_secs_f64());
counter!("cache.hits", cache_stats.hits);
gauge!("memory.usage", memory_usage);
```

### **Health Checks**

```rust
pub struct HealthCheck {
    pub status: HealthStatus,
    pub details: HashMap<String, String>,
}

pub fn check_health() -> HealthCheck {
    let mut details = HashMap::new();

    // Check parser health
    let parser_health = check_parser_health();
    details.insert("parser".to_string(), parser_health.to_string());

    // Check evaluator health
    let eval_health = check_evaluator_health();
    details.insert("evaluator".to_string(), eval_health.to_string());

    HealthCheck {
        status: if parser_health.is_healthy() && eval_health.is_healthy() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Unhealthy
        },
        details,
    }
}
```

## 🎯 **Production Deployment**

### **Build Configuration**

```toml
# Cargo.toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

### **Docker Deployment**

```dockerfile
FROM rust:1.75-alpine as builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/target/release/ligature-lsp .
CMD ["./ligature-lsp"]
```

### **Configuration Management**

```rust
// Production configuration
let config = ProductionConfig {
    log_level: "info",
    cache_size: 1024 * 1024, // 1MB
    max_evaluation_time: Duration::from_secs(30),
    enable_monitoring: true,
    metrics_endpoint: "http://localhost:9090",
};
```

## 📞 **Getting Help**

### **Resources**

- **Documentation**: [docs/](docs/) - Complete documentation
- **Examples**: [examples/](examples/) - Code examples
- **Tests**: [tests/](tests/) - Test examples
- **Issues**: [GitHub Issues](https://github.com/ligature-lang/ligature/issues)

### **Community**

- **Discussions**: [GitHub Discussions](https://github.com/ligature-lang/ligature/discussions)
- **Contributing**: [CONTRIBUTING.md](../../CONTRIBUTING.md)
- **Code of Conduct**: [CODE_OF_CONDUCT.md](../../CODE_OF_CONDUCT.md)

---

This developer guide provides comprehensive information for contributing to and working with the Ligature project. The system is production-ready with professional-grade tooling, comprehensive testing, and robust error handling.
