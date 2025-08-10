# Ligature Evaluator Configuration

The Ligature evaluator supports comprehensive configuration for tuning performance, caching behavior, and debugging features. This configuration system supports multiple formats and hierarchical configuration loading.

## Overview

The configuration system provides:

- **Multiple formats**: TOML, JSON, and YAML support
- **Hierarchical loading**: Global configuration with project-specific overrides
- **Runtime configuration**: Apply configuration changes at runtime
- **Granular control**: Fine-tune caching, performance, and debugging settings

## Configuration File Locations

### Global Configuration

Global configuration files are stored in the XDG configuration directory:

- `~/.config/ligature/eval.toml`
- `~/.config/ligature/eval.json`
- `~/.config/ligature/eval.yaml`

### Project-Specific Configuration

Project-specific configuration files can be placed in your project directory:

- `./eval.toml`
- `./eval.json`
- `./eval.yaml`

Project configuration overrides global configuration settings.

## Configuration Structure

### Cache Configuration

```toml
[cache]
enabled = true
max_size = 1000
max_memory_bytes = 1048576  # 1MB

[cache.warming]
enabled = false
max_expressions = 100
warm_on_module_load = false

[cache.cacheable_expressions]
literals = true
variables = true
binary_ops = true
unary_ops = true
field_access = true
applications = false
let_expressions = false
records = false
unions = false
matches = false
if_expressions = false
```

**Cache Settings:**

- `enabled`: Enable/disable expression caching
- `max_size`: Maximum number of cached expressions
- `max_memory_bytes`: Maximum memory usage for cache

**Cache Warming:**

- `enabled`: Enable cache warming
- `max_expressions`: Maximum expressions to pre-warm
- `warm_on_module_load`: Warm cache when modules are loaded

**Cacheable Expressions:**
Control which expression types are cached:

- `literals`: Cache literal values (recommended: true)
- `variables`: Cache variable lookups (recommended: true)
- `binary_ops`: Cache binary operations (recommended: true)
- `unary_ops`: Cache unary operations (recommended: true)
- `field_access`: Cache field access operations (recommended: true)
- `applications`: Cache function applications (use with caution)
- `let_expressions`: Cache let expressions (use with caution)
- `records`: Cache record expressions (use with caution)
- `unions`: Cache union expressions (use with caution)
- `matches`: Cache match expressions (use with caution)
- `if_expressions`: Cache if expressions (use with caution)

### Performance Configuration

```toml
[performance]
tail_call_optimization = true
stack_based_evaluation = true
value_optimization = true
max_stack_depth = 10000
env_pool_size = 100
value_pool_size = 1000
```

**Performance Settings:**

- `tail_call_optimization`: Enable tail call optimization
- `stack_based_evaluation`: Enable stack-based evaluation for simple functions
- `value_optimization`: Enable value interning optimization
- `max_stack_depth`: Maximum call stack depth
- `env_pool_size`: Environment pool size for reducing allocations
- `value_pool_size`: Value pool size for reducing allocations

### Memory Configuration

```toml
[memory]
monitoring = false
eviction_threshold_percent = 80.0
max_evaluation_memory_bytes = 104857600  # 100MB
gc_frequency = 1000
```

**Memory Settings:**

- `monitoring`: Enable memory usage monitoring
- `eviction_threshold_percent`: Memory threshold for cache eviction
- `max_evaluation_memory_bytes`: Maximum memory per evaluation
- `gc_frequency`: Garbage collection frequency

### Debug Configuration

```toml
[debug]
logging = false
profiling = false
cache_statistics = true
memory_tracking = false
log_level = "info"
```

**Debug Settings:**

- `logging`: Enable detailed logging
- `profiling`: Enable performance profiling
- `cache_statistics`: Enable cache statistics collection
- `memory_tracking`: Enable memory usage tracking
- `log_level`: Log level (error, warn, info, debug, trace)

## Usage Examples

### Creating an Evaluator with Configuration

```rust
use ligature_eval::{Evaluator, config::EvaluatorConfig};

// Create with default configuration
let evaluator = Evaluator::new();

// Create with custom configuration
let mut config = EvaluatorConfig::default();
config.cache.max_size = 5000;
config.cache.max_memory_bytes = 5 * 1024 * 1024; // 5MB
let evaluator = Evaluator::with_config(config);

// Load configuration from files
let evaluator = Evaluator::with_config_from_files(None).await?;
let evaluator = Evaluator::with_config_from_files(Some(PathBuf::from("config.toml"))).await?;
```

### Applying Configuration at Runtime

```rust
use ligature_eval::{Evaluator, config::EvaluatorConfig};

let mut evaluator = Evaluator::new();

// Apply new configuration
let mut config = EvaluatorConfig::default();
config.cache.max_size = 10000;
config.debug.logging = true;
evaluator.apply_config(config);

// Update specific settings
let mut new_config = evaluator.config().clone();
new_config.cache.max_size = 15000;
evaluator.update_config(new_config);
```

### Loading Configuration from Files

```rust
use ligature_eval::config::EvaluatorConfigManager;
use std::path::PathBuf;

let config_manager = EvaluatorConfigManager::new()?;

// Load global configuration
let config = config_manager.load_config().await?;

// Load with project override
let config_manager = config_manager.with_project_config(PathBuf::from("project.toml"));
let config = config_manager.load_config().await?;
```

### Saving Configuration Files

```rust
use ligature_eval::config::{EvaluatorConfigManager, ConfigFormat};

let config_manager = EvaluatorConfigManager::new()?;

// Save default configuration in different formats
let toml_path = config_manager.save_default_config(ConfigFormat::Toml).await?;
let json_path = config_manager.save_default_config(ConfigFormat::Json).await?;
let yaml_path = config_manager.save_default_config(ConfigFormat::Yaml).await?;
```

## Performance Tuning Guidelines

### For Development

```toml
[cache]
enabled = true
max_size = 500
max_memory_bytes = 524288  # 512KB

[debug]
logging = true
cache_statistics = true
log_level = "debug"
```

### For Production

```toml
[cache]
enabled = true
max_size = 5000
max_memory_bytes = 5242880  # 5MB

[performance]
tail_call_optimization = true
stack_based_evaluation = true
value_optimization = true

[debug]
logging = false
profiling = false
cache_statistics = true
```

### For High-Performance Computing

```toml
[cache]
enabled = true
max_size = 10000
max_memory_bytes = 52428800  # 50MB

[performance]
tail_call_optimization = true
stack_based_evaluation = true
value_optimization = true
max_stack_depth = 50000
env_pool_size = 500
value_pool_size = 5000

[memory]
monitoring = true
eviction_threshold_percent = 90.0
max_evaluation_memory_bytes = 1073741824  # 1GB
```

## Troubleshooting

### Common Issues

1. **High Memory Usage**

   - Reduce `cache.max_memory_bytes`
   - Enable `memory.monitoring`
   - Lower `cache.max_size`

2. **Slow Performance**

   - Increase `cache.max_size`
   - Enable `performance.value_optimization`
   - Enable `cache.warming.enabled`

3. **Stack Overflow**

   - Increase `performance.max_stack_depth`
   - Enable `performance.tail_call_optimization`

4. **Cache Inefficiency**
   - Adjust `cache.cacheable_expressions` settings
   - Monitor cache statistics with `debug.cache_statistics = true`

### Debugging Configuration

Enable debugging to troubleshoot configuration issues:

```toml
[debug]
logging = true
cache_statistics = true
memory_tracking = true
log_level = "debug"
```

This will provide detailed information about cache performance, memory usage, and configuration loading.

## Migration from Previous Versions

If you're upgrading from a previous version without configuration support:

1. The evaluator will use sensible defaults
2. Create a configuration file using `EvaluatorConfigManager::save_default_config()`
3. Customize the settings as needed
4. The system is backward compatible

## Best Practices

1. **Start with defaults**: Use default configuration for initial development
2. **Profile first**: Enable profiling to identify bottlenecks
3. **Tune incrementally**: Make small changes and measure impact
4. **Use project configs**: Override global settings for project-specific needs
5. **Monitor memory**: Enable memory monitoring for production deployments
6. **Cache selectively**: Be careful with caching complex expressions
7. **Test thoroughly**: Verify configuration changes don't affect correctness
