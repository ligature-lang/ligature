# Krox - Ligature Client SDKs

###### κρώξιμο (kroximo): This is a direct translation of "squawk" when referring to a bird's cry.

Krox is a companion library to Ligature that provides client SDKs for invoking Ligature programs as side effects from various programming languages and platforms.

## Features

- **Multiple Execution Modes**: Native CLI execution, HTTP-based execution, and in-process execution
- **Language SDKs**: Rust, Python, Node.js, Java, and Go bindings
- **Intelligent Caching**: Content-based and file-based caching with configurable policies
- **Async Support**: Full async/await support for all operations
- **Comprehensive Error Handling**: Detailed error reporting and recovery
- **Configuration Management**: Flexible configuration with environment-specific overrides
- **CLI Interface**: Command-line tool for executing Ligature programs

## Quick Start

### Rust

```rust
use krox::{Client, ExecutionMode};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a client with native execution
    let client = Client::new(ExecutionMode::Native).await?;

    // Execute a Ligature program
    let result = client.execute_file("config.lig").await?;

    println!("Result: {:?}", result.value);
    println!("Execution time: {:?}", result.metadata.duration);

    Ok(())
}
```

### Python

```python
import krox

# Create a client
client = krox.PyKroxClient("native")

# Execute a Ligature program
result = client.execute_file("config.lig")
print(f"Result: {result['value']}")
print(f"Execution time: {result['duration']}s")
```

### Node.js

```javascript
const { NodeKroxClient } = require("krox");

// Create a client
const client = new NodeKroxClient("native");

// Execute a Ligature program
const result = await client.executeFile("config.lig");
console.log("Result:", result.value);
console.log("Execution time:", result.duration, "s");
```

### Command Line

```bash
# Execute a Ligature file
krox execute config.lig

# Execute source code directly
krox eval "let x = 42"

# Show cache statistics
krox cache stats

# Clear the cache
krox cache clear
```

## Installation

### Rust

Add to your `Cargo.toml`:

```toml
[dependencies]
krox = { git = "https://github.com/ligature-lang/ligature", package = "krox" }
```

### Python

```bash
pip install krox
```

### Node.js

```bash
npm install krox
```

## Configuration

Krox supports configuration through files and environment variables. Create a `krox.yaml` file:

```yaml
default_execution_mode: native
cache:
  enabled: true
  directory: ~/.krox/cache
  max_age: 3600 # 1 hour
  max_size: 104857600 # 100 MB
http:
  timeout: 30
  endpoint: http://localhost:8080
  retry:
    max_retries: 3
    base_delay: 1000
    max_delay: 10000
native:
  cli_path: /usr/local/bin/ligature-cli
  timeout: 30
logging:
  level: info
  structured: true
environments:
  development:
    execution_mode: in-process
  production:
    execution_mode: http
    http_endpoint: https://ligature.example.com
```

## Execution Modes

### Native Mode

Executes Ligature programs using the `ligature-cli` binary. This is the default mode and provides the best performance for local development.

```rust
let client = Client::new(ExecutionMode::Native).await?;
```

### HTTP Mode

Executes Ligature programs via HTTP requests to a remote server. Useful for distributed systems and cloud deployments.

```rust
let client = ClientBuilder::new()
    .execution_mode(ExecutionMode::Http)
    .http_endpoint("https://ligature.example.com".to_string())
    .build()
    .await?;
```

### In-Process Mode

Executes Ligature programs directly in the current process. Provides the fastest execution but requires the full Ligature runtime.

```rust
let client = Client::new(ExecutionMode::InProcess).await?;
```

## Caching

Krox provides intelligent caching to improve performance:

- **File-based caching**: Caches results based on file path and modification time
- **Content-based caching**: Caches results based on source code content hash
- **Configurable policies**: Set cache size limits, expiration times, and storage locations

```rust
let client = ClientBuilder::new()
    .enable_cache(true)
    .cache_dir("/tmp/krox-cache".to_string())
    .build()
    .await?;

// Check cache statistics
if let Some(stats) = client.cache_stats().await? {
    println!("Cache hit rate: {:.2}%", stats.hit_rate * 100.0);
}
```

## Error Handling

Krox provides comprehensive error handling with detailed error messages:

```rust
match client.execute_file("config.lig").await {
    Ok(result) => {
        println!("Success: {:?}", result.value);
    }
    Err(Error::Parse(e)) => {
        eprintln!("Parse error: {}", e);
    }
    Err(Error::CliExecution { message, exit_code, stderr }) => {
        eprintln!("CLI execution failed ({}): {}", exit_code.unwrap_or(-1), message);
        eprintln!("Stderr: {}", stderr);
    }
    Err(Error::Http(e)) => {
        eprintln!("HTTP error: {}", e);
    }
    Err(e) => {
        eprintln!("Unexpected error: {}", e);
    }
}
```

## Language SDKs

### Python

```python
import krox

# Create client
client = krox.PyKroxClient("native")

# Execute file
result = client.execute_file("config.lig")

# Execute source
result = client.execute_source("let x = 42")

# Cache operations
stats = client.cache_stats()
client.clear_cache()
```

### Node.js

```javascript
const { NodeKroxClient } = require("krox");

// Create client
const client = new NodeKroxClient("native");

// Execute file
const result = await client.executeFile("config.lig");

// Execute source
const result = await client.executeSource("let x = 42");

// Cache operations
const stats = await client.cacheStats();
await client.clearCache();
```

### Java

```java
import com.krox.KroxClient;

// Create client
KroxClient client = new KroxClient("native");

// Execute file
Map<String, Object> result = client.executeFile("config.lig");

// Execute source
Map<String, Object> result = client.executeSource("let x = 42");
```

### Go

```go
import "github.com/ligature-lang/krox"

// Create client
client := krox.NewClient("native")
defer client.Free()

// Execute file
result := client.ExecuteFile("config.lig")
```

## CLI Usage

### Basic Commands

```bash
# Execute a Ligature file
krox execute config.lig

# Execute source code
krox eval "let x = 42"

# Show cache statistics
krox cache stats

# Clear cache
krox cache clear

# Show configuration
krox config
```

### Advanced Options

```bash
# Use HTTP execution mode
krox --mode http --http-endpoint https://ligature.example.com execute config.lig

# Disable caching
krox --cache false execute config.lig

# Set custom cache directory
krox --cache-dir /tmp/my-cache execute config.lig

# Enable verbose logging
krox --verbose execute config.lig

# Use custom configuration file
krox --config krox.yaml execute config.lig
```

### Output Formats

```bash
# JSON output (default)
krox execute config.lig --format json

# YAML output
krox execute config.lig --format yaml

# Pretty-printed output
krox execute config.lig --format pretty
```

## Development

### Building from Source

```bash
# Clone the repository
git clone https://github.com/ligature-lang/ligature.git
cd ligature

# Build the krox crate
cargo build -p krox

# Run tests
cargo test -p krox

# Build with specific features
cargo build -p krox --features python,node
```

### Running Tests

```bash
# Run all tests
cargo test -p krox

# Run specific test modules
cargo test -p krox client
cargo test -p krox cache
cargo test -p krox executor
```

### Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the Apache License, Version 2.0 - see the [LICENSE-APACHE](LICENSE-APACHE) file or https://www.apache.org/licenses/LICENSE-2.0 for details.

## Documentation

- [API Reference](https://docs.rs/krox)
- [Examples](examples/)
- [Configuration Guide](docs/configuration.md)
- [Language Bindings](docs/bindings.md)
