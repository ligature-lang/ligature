# Reed - Ligature Language CLI

Reed is a command-line interface for the Ligature language, providing tools for parsing, type checking, evaluating, and benchmarking Ligature programs.

## Features

- **Parsing**: Parse and validate Ligature programs with detailed error reporting
- **Type Checking**: Perform static type analysis on Ligature programs
- **Evaluation**: Execute Ligature programs and view results
- **Complete Pipeline**: Run the full parse → type check → evaluate pipeline
- **Benchmarking**: Performance testing and analysis tools
- **XDG Configuration**: User-configurable settings with XDG base directory support
- **Multiple Output Formats**: Support for text, JSON, and YAML output formats

## Installation

Reed is part of the Ligature workspace. To build it:

```bash
# From the workspace root
cargo build --bin reed

# Or from the reed directory
cd apps/reed
cargo build
```

## Usage

### Basic Commands

```bash
# Parse a Ligature program
reed parse --file program.lig

# Type check a program
reed typecheck --file program.lig

# Evaluate a program
reed eval --file program.lig

# Run the complete pipeline
reed run --file program.lig
```

### Benchmarking

Reed includes comprehensive benchmarking capabilities:

```bash
# Quick performance test
reed benchmark --quick

# Comprehensive performance analysis
reed benchmark --comprehensive --output results.csv

# Custom benchmark with memory tracking
reed benchmark --custom --file my_benchmark.lig --memory

# Benchmark with specific iterations and format
reed benchmark --quick --iterations 5000 --format json
```

## Configuration

Reed uses XDG base directories for configuration management. Configuration files are stored in the appropriate XDG directories:

- **Config**: `~/.config/reed/`
- **Data**: `~/.local/share/reed/`
- **Cache**: `~/.cache/reed/`
- **State**: `~/.local/state/reed/`

### Configuration Options

The CLI configuration supports:

- **Logging**: Log levels, file/console output, rotation settings
- **Performance**: Parallel processing, worker threads, caching
- **Defaults**: Output format, verbosity, progress display, timeouts
- **Cache**: Cache size limits, TTL, auto-cleanup

### Example Configuration

```json
{
  "logging": {
    "level": "info",
    "log_to_file": true,
    "log_to_console": false,
    "max_file_size": 10485760,
    "max_files": 5,
    "include_timestamps": true
  },
  "performance": {
    "enable_parallel": true,
    "worker_threads": 4,
    "enable_caching": true,
    "cache_ttl_seconds": 3600
  },
  "defaults": {
    "output_format": "json",
    "verbose": false,
    "show_progress": true,
    "timeout_seconds": 30
  },
  "cache": {
    "enabled": true,
    "max_size": 1073741824,
    "max_age": 86400,
    "auto_clean": true
  }
}
```

## Output Formats

Reed supports multiple output formats:

- **Text**: Human-readable output (default)
- **JSON**: Structured JSON output for programmatic consumption
- **YAML**: YAML format for configuration-friendly output

The output format can be configured globally or specified per command.

## Error Handling

Reed provides comprehensive error reporting with:

- Detailed parsing error messages with line and column information
- Type checking errors with context about type mismatches
- Evaluation errors with stack traces
- Configuration errors with helpful suggestions

## Performance Features

- **Parallel Processing**: Multi-threaded evaluation for large programs
- **Caching**: AST and compiled result caching for improved performance
- **Memory Tracking**: Optional memory usage monitoring during benchmarks
- **Progress Reporting**: Real-time progress indicators for long-running operations

## Development

### Building

```bash
# Debug build
cargo build

# Release build
cargo build --release

# With specific features
cargo build --features "benchmark"
```

### Testing

```bash
# Run tests
cargo test

# Run tests with output
cargo test -- --nocapture
```

### Dependencies

Reed depends on the following Ligature crates:

- `ligature-ast`: Abstract syntax tree representation
- `ligature-parser`: Program parsing and validation
- `ligature-types`: Type system and type checking
- `ligature-eval`: Program evaluation engine
- `ligature-xdg`: XDG configuration management

## Contributing

When contributing to Reed:

1. Follow the existing code style and patterns
2. Add tests for new functionality
3. Update documentation for new features
4. Ensure all commands have proper error handling
5. Consider performance implications of changes

## License

Reed is part of the Ligature project and follows the same licensing terms.
