# Ligature API Reference

**Last Updated**: January 2025  
**Status**: Production Ready ✅

This document provides comprehensive API documentation for all public interfaces in the Ligature system. All APIs are stable and ready for production use.

## 📚 **Core Language APIs**

### **Parser API (`ligature-parser`)**

#### **Main Parser Functions**

```rust
/// Parse Ligature source code into an AST
pub fn parse(source: &str) -> Result<Program, ParseError>

/// Parse with custom options
pub fn parse_with_options(
    source: &str,
    options: ParseOptions
) -> Result<Program, ParseError>

/// Parse a single expression
pub fn parse_expression(source: &str) -> Result<Expression, ParseError>
```

#### **ParseOptions**

```rust
pub struct ParseOptions {
    /// Allow unknown operators in expressions
    pub allow_unknown_operators: bool,
    /// Enable strict parsing mode
    pub strict_mode: bool,
    /// Maximum source size in bytes
    pub max_source_size: usize,
    /// Enable detailed error reporting
    pub detailed_errors: bool,
}

impl Default for ParseOptions {
    fn default() -> Self {
        Self {
            allow_unknown_operators: false,
            strict_mode: true,
            max_source_size: 1024 * 1024, // 1MB
            detailed_errors: true,
        }
    }
}
```

#### **ParseError**

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    /// Error message
    pub message: String,
    /// Source location where error occurred
    pub span: Span,
    /// Error kind for programmatic handling
    pub kind: ParseErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorKind {
    UnexpectedToken { expected: String, found: String },
    UnterminatedString,
    InvalidNumber,
    UnknownOperator,
    SyntaxError,
}
```

### **Type System API (`ligature-types`)**

#### **Type Checking Functions**

```rust
/// Type check a program
pub fn typecheck(
    program: Program,
    env: &TypeEnvironment
) -> Result<TypedProgram, TypeError>

/// Type check with custom options
pub fn typecheck_with_options(
    program: Program,
    env: &TypeEnvironment,
    options: TypeCheckOptions
) -> Result<TypedProgram, TypeError>

/// Infer types for an expression
pub fn infer_type(
    expr: &Expression,
    env: &TypeEnvironment
) -> Result<Type, TypeError>
```

#### **TypeEnvironment**

```rust
pub struct TypeEnvironment {
    /// Current type bindings
    bindings: HashMap<String, Type>,
    /// Imported modules
    modules: HashMap<String, ModuleInfo>,
    /// Type class instances
    instances: Vec<TypeClassInstance>,
    /// Warnings collected during type checking
    warnings: Vec<TypeWarning>,
}

impl TypeEnvironment {
    /// Create a new type environment
    pub fn new() -> Self

    /// Add a type binding
    pub fn bind(&mut self, name: String, ty: Type)

    /// Load a module
    pub fn load_module(&mut self, path: &str) -> Result<(), TypeError>

    /// Get all warnings
    pub fn warnings(&self) -> &[TypeWarning]

    /// Clear warnings
    pub fn clear_warnings(&mut self)
}
```

#### **TypeCheckOptions**

```rust
pub struct TypeCheckOptions {
    /// Enable type-level computation
    pub enable_type_level_computation: bool,
    /// Allow partial type inference
    pub allow_partial_inference: bool,
    /// Maximum type inference depth
    pub max_inference_depth: usize,
    /// Enable advanced subtyping
    pub enable_advanced_subtyping: bool,
}

impl Default for TypeCheckOptions {
    fn default() -> Self {
        Self {
            enable_type_level_computation: true,
            allow_partial_inference: false,
            max_inference_depth: 100,
            enable_advanced_subtyping: true,
        }
    }
}
```

#### **TypeError**

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    /// Error message
    pub message: String,
    /// Source location
    pub span: Span,
    /// Error kind
    pub kind: TypeErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    TypeMismatch { expected: Type, found: Type },
    UndefinedVariable { name: String },
    UndefinedType { name: String },
    TypeClassError { message: String },
    ImportError { path: String, reason: String },
    CycleError { path: Vec<String> },
}
```

### **Evaluation API (`ligature-eval`)**

#### **Main Evaluation Functions**

```rust
/// Evaluate a typed program
pub fn evaluate(
    program: TypedProgram,
    options: EvaluationOptions
) -> Result<Value, EvaluationError>

/// Evaluate with custom environment
pub fn evaluate_with_environment(
    program: TypedProgram,
    env: Environment,
    options: EvaluationOptions
) -> Result<Value, EvaluationError>

/// Evaluate a single expression
pub fn evaluate_expression(
    expr: &TypedExpression,
    env: &Environment
) -> Result<Value, EvaluationError>
```

#### **EvaluationOptions**

```rust
pub struct EvaluationOptions {
    /// Enable expression caching
    pub enable_caching: bool,
    /// Enable performance optimizations
    pub enable_optimization: bool,
    /// Maximum evaluation iterations
    pub max_iterations: usize,
    /// Maximum memory usage in bytes
    pub max_memory: usize,
    /// Evaluation timeout
    pub timeout: Option<Duration>,
    /// Enable performance monitoring
    pub enable_monitoring: bool,
}

impl Default for EvaluationOptions {
    fn default() -> Self {
        Self {
            enable_caching: true,
            enable_optimization: true,
            max_iterations: 1000,
            max_memory: 1024 * 1024 * 100, // 100MB
            timeout: Some(Duration::from_secs(30)),
            enable_monitoring: false,
        }
    }
}
```

#### **Environment**

```rust
pub struct Environment {
    /// Variable bindings
    bindings: HashMap<String, Value>,
    /// Parent environment for closures
    parent: Option<Arc<Environment>>,
    /// Performance metrics
    metrics: EvaluationMetrics,
}

impl Environment {
    /// Create a new environment
    pub fn new() -> Self

    /// Create environment with parent
    pub fn with_parent(parent: Arc<Environment>) -> Self

    /// Bind a variable
    pub fn bind(&mut self, name: String, value: Value)

    /// Look up a variable
    pub fn lookup(&self, name: &str) -> Option<&Value>

    /// Get evaluation metrics
    pub fn metrics(&self) -> &EvaluationMetrics
}
```

#### **EvaluationError**

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct EvaluationError {
    /// Error message
    pub message: String,
    /// Source location
    pub span: Span,
    /// Error kind
    pub kind: EvaluationErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationErrorKind {
    UndefinedVariable { name: String },
    TypeError { message: String },
    RuntimeError { message: String },
    TimeoutError,
    MemoryError,
    RecursionError { depth: usize },
}
```

## 🔧 **Development Tools APIs**

### **LSP API (`ligature-lsp`)**

#### **LSP Server**

```rust
pub struct LigatureLspServer {
    /// Server configuration
    config: LspConfig,
    /// Document cache
    documents: Arc<RwLock<HashMap<Url, DocumentState>>>,
    /// Type environment
    type_env: Arc<RwLock<TypeEnvironment>>,
    /// Performance metrics
    metrics: Arc<RwLock<LspMetrics>>,
}

impl LigatureLspServer {
    /// Create a new LSP server
    pub fn new(config: LspConfig) -> Result<Self, ServerError>

    /// Update document content
    pub fn update_document(
        &self,
        uri: Url,
        content: String,
        version: i32
    ) -> Result<(), ServerError>

    /// Get document symbols
    pub fn document_symbols(
        &self,
        uri: &Url
    ) -> Result<Vec<SymbolInformation>, ServerError>

    /// Find symbol references
    pub fn find_references(
        &self,
        uri: &Url,
        position: Position
    ) -> Result<Vec<Location>, ServerError>

    /// Get completion items
    pub fn completion(
        &self,
        uri: &Url,
        position: Position
    ) -> Result<Vec<CompletionItem>, ServerError>

    /// Shutdown gracefully
    pub async fn shutdown_gracefully(&self) -> Result<(), ServerError>
}
```

#### **LspConfig**

```rust
pub struct LspConfig {
    /// Server name and version
    pub server_info: ServerInfo,
    /// Document cache settings
    pub cache: CacheConfig,
    /// Performance settings
    pub performance: PerformanceConfig,
    /// Logging settings
    pub logging: LoggingConfig,
}

pub struct ServerInfo {
    pub name: String,
    pub version: String,
}

pub struct CacheConfig {
    pub max_documents: usize,
    pub ttl_seconds: u64,
    pub enable_incremental_parsing: bool,
}

pub struct PerformanceConfig {
    pub max_workspace_files: usize,
    pub enable_symbol_caching: bool,
    pub symbol_cache_size: usize,
}

pub struct LoggingConfig {
    pub level: LogLevel,
    pub enable_structured_logging: bool,
}
```

#### **DocumentState**

```rust
pub struct DocumentState {
    /// Document content
    pub content: String,
    /// Parsed AST (if parsing succeeded)
    pub ast: Option<Program>,
    /// Last known version
    pub version: i32,
    /// Parse errors (if any)
    pub parse_errors: Vec<ParseError>,
    /// Type errors (if any)
    pub type_errors: Vec<TypeError>,
    /// Last modified timestamp
    pub last_modified: SystemTime,
}
```

#### **ServerError**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum ServerError {
    /// Configuration error
    ConfigurationError { message: String },
    /// Document not found
    DocumentNotFound { uri: String },
    /// Parse error
    ParseError { error: ParseError },
    /// Type error
    TypeError { error: TypeError },
    /// Internal server error
    InternalError { message: String },
    /// Invalid request
    InvalidRequest { message: String },
}
```

### **Configuration API (`ligature-xdg`)**

#### **Configuration Loading**

```rust
/// Load configuration from file
pub fn load_config<T: DeserializeOwned>(
    path: &str
) -> Result<T, ConfigError>

/// Load configuration with schema validation
pub fn load_config_with_schema<T: DeserializeOwned>(
    path: &str,
    schema: &ConfigSchema
) -> Result<T, ConfigError>

/// Watch configuration file for changes
pub fn watch_config<T: DeserializeOwned + Clone>(
    path: &str,
    callback: impl Fn(T) + Send + 'static
) -> Result<ConfigWatcher, ConfigError>
```

#### **Configuration Validation**

```rust
pub struct ConfigValidator {
    schema: ConfigSchema,
}

impl ConfigValidator {
    /// Create a new validator
    pub fn new(schema: ConfigSchema) -> Self

    /// Validate configuration
    pub fn validate<T: Serialize>(
        &self,
        config: &T
    ) -> Result<(), ValidationError>

    /// Validate with custom rules
    pub fn validate_with_rules<T: Serialize>(
        &self,
        config: &T,
        rules: Vec<ValidationRule>
    ) -> Result<(), ValidationError>
}

pub struct ConfigSchema {
    fields: HashMap<String, FieldDefinition>,
}

impl ConfigSchema {
    /// Create a new schema
    pub fn new() -> Self

    /// Add a field definition
    pub fn field(
        mut self,
        name: &str,
        field_type: FieldType
    ) -> Self

    /// Build the schema
    pub fn build(self) -> ConfigSchema
}
```

#### **Field Types**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum FieldType {
    String { min_length: Option<usize>, max_length: Option<usize> },
    Integer { min: Option<i64>, max: Option<i64> },
    Float { min: Option<f64>, max: Option<f64> },
    Boolean,
    Object { schema: ConfigSchema },
    Array { element_type: Box<FieldType> },
    File { must_exist: bool },
    Directory { must_exist: bool },
    Url,
    Email,
    IpAddress,
    Port { min: Option<u16>, max: Option<u16> },
    Duration,
    Size { min: Option<u64>, max: Option<u64> },
}
```

## 📊 **Performance Monitoring APIs**

### **Performance Monitor API**

#### **Performance Monitoring**

```rust
/// Start performance monitoring
pub fn start_monitoring(
    config: MonitoringConfig
) -> Result<PerformanceMonitor, MonitorError>

/// Get current performance metrics
pub fn get_metrics() -> Result<PerformanceMetrics, MonitorError>

/// Run performance regression tests
pub fn run_regression_tests(
    baseline: &PerformanceBaseline
) -> Result<RegressionReport, MonitorError>
```

#### **PerformanceMonitor**

```rust
pub struct PerformanceMonitor {
    config: MonitoringConfig,
    metrics: Arc<RwLock<PerformanceMetrics>>,
    baseline: Option<PerformanceBaseline>,
}

impl PerformanceMonitor {
    /// Create a new monitor
    pub fn new(config: MonitoringConfig) -> Self

    /// Start monitoring an operation
    pub fn start_operation(&self, name: &str) -> OperationGuard

    /// Record a metric
    pub fn record_metric(&self, name: &str, value: f64)

    /// Get current metrics
    pub fn metrics(&self) -> PerformanceMetrics

    /// Generate report
    pub fn generate_report(&self) -> PerformanceReport
}
```

#### **PerformanceMetrics**

```rust
pub struct PerformanceMetrics {
    /// Execution time metrics
    pub execution_time: TimeMetrics,
    /// Memory usage metrics
    pub memory_usage: MemoryMetrics,
    /// Cache performance metrics
    pub cache_performance: CacheMetrics,
    /// Operation-specific metrics
    pub operations: HashMap<String, OperationMetrics>,
}

pub struct TimeMetrics {
    pub total_execution_time: Duration,
    pub average_execution_time: Duration,
    pub min_execution_time: Duration,
    pub max_execution_time: Duration,
    pub operation_count: usize,
}

pub struct MemoryMetrics {
    pub peak_memory_usage: usize,
    pub current_memory_usage: usize,
    pub allocation_count: usize,
    pub deallocation_count: usize,
}

pub struct CacheMetrics {
    pub hit_count: usize,
    pub miss_count: usize,
    pub hit_rate: f64,
    pub cache_size: usize,
    pub eviction_count: usize,
}
```

## 🚀 **Application APIs**

### **Reed CLI API**

#### **CLI Commands**

```rust
/// Parse a Ligature file
pub fn parse_file(path: &str) -> Result<Program, CliError>

/// Type check a Ligature file
pub fn typecheck_file(path: &str) -> Result<TypedProgram, CliError>

/// Evaluate a Ligature file
pub fn evaluate_file(path: &str) -> Result<Value, CliError>

/// Run benchmarks
pub fn run_benchmarks(config: BenchmarkConfig) -> Result<BenchmarkReport, CliError>
```

#### **BenchmarkConfig**

```rust
pub struct BenchmarkConfig {
    /// Benchmark iterations
    pub iterations: usize,
    /// Warmup iterations
    pub warmup_iterations: usize,
    /// Benchmark timeout
    pub timeout: Duration,
    /// Enable detailed reporting
    pub detailed_report: bool,
    /// Output format
    pub output_format: OutputFormat,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OutputFormat {
    Json,
    Csv,
    Human,
    Markdown,
}
```

### **Cacophony API**

#### **Configuration Orchestration**

```rust
/// Load and validate configuration
pub fn load_configuration(
    path: &str
) -> Result<Configuration, CacophonyError>

/// Execute configuration
pub fn execute_configuration(
    config: &Configuration,
    environment: &str
) -> Result<ExecutionResult, CacophonyError>

/// Validate configuration
pub fn validate_configuration(
    config: &Configuration
) -> Result<ValidationResult, CacophonyError>
```

#### **Configuration**

```rust
pub struct Configuration {
    /// Configuration name
    pub name: String,
    /// Environment definitions
    pub environments: HashMap<String, Environment>,
    /// Collection definitions
    pub collections: HashMap<String, Collection>,
    /// Plugin configurations
    pub plugins: HashMap<String, PluginConfig>,
}

pub struct Environment {
    pub name: String,
    pub variables: HashMap<String, Value>,
    pub collections: Vec<String>,
}

pub struct Collection {
    pub name: String,
    pub operations: Vec<Operation>,
    pub dependencies: Vec<String>,
}
```

### **Keywork API**

#### **Package Management**

```rust
/// Initialize a new register
pub fn init_register(path: &str) -> Result<(), KeyworkError>

/// Install a package
pub fn install_package(
    package: &str,
    version: Option<&str>
) -> Result<(), KeyworkError>

/// Publish a package
pub fn publish_package(
    path: &str,
    version: &str
) -> Result<(), KeyworkError>

/// List installed packages
pub fn list_packages() -> Result<Vec<PackageInfo>, KeyworkError>
```

#### **PackageInfo**

```rust
pub struct PackageInfo {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub dependencies: Vec<String>,
    pub installed_at: SystemTime,
}
```

## 🔒 **Error Handling**

### **Common Error Types**

All APIs use consistent error handling with the following patterns:

```rust
/// Generic error type for most operations
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

/// Specific error types for different components
pub type ParseResult<T> = Result<T, ParseError>;
pub type TypeResult<T> = Result<T, TypeError>;
pub type EvalResult<T> = Result<T, EvaluationError>;
pub type LspResult<T> = Result<T, ServerError>;
pub type ConfigResult<T> = Result<T, ConfigError>;
```

### **Error Conversion**

All error types implement standard traits:

```rust
impl std::error::Error for ParseError {}
impl std::error::Error for TypeError {}
impl std::error::Error for EvaluationError {}
impl std::error::Error for ServerError {}
impl std::error::Error for ConfigError {}
```

## 📈 **Versioning and Stability**

### **API Stability**

- **Stable APIs**: All documented APIs are stable and will not break in minor releases
- **Experimental APIs**: Marked with `#[unstable]` and may change
- **Deprecated APIs**: Marked with `#[deprecated]` and will be removed in future releases

### **Version Compatibility**

- **Major Version**: Breaking changes
- **Minor Version**: New features, backward compatible
- **Patch Version**: Bug fixes, backward compatible

### **Migration Guide**

When APIs change, migration guides are provided in the release notes and documentation.

---

This API reference provides comprehensive documentation for all public interfaces in the Ligature system. All APIs are production-ready and follow Rust best practices for error handling, performance, and usability.
