# Cacophony CLI

A CLI tool for orchestrating collections of Ligature programs. Cacophony provides a unified interface for managing, deploying, and operating Ligature-based configurations across multiple environments and use cases.

## Features

- **Purpose-Agnostic**: Not tied to any specific domain (infrastructure, etc.) but can orchestrate any Ligature-based configuration
- **Register-Centric**: Built around Ligature's register system for dependency management and code organization
- **Environment-Aware**: Supports multiple environments (dev, staging, prod) with environment-specific configurations
- **Declarative Operations**: All operations are defined declaratively in Ligature, not imperatively in the CLI
- **Type-Safe Orchestration**: Leverages Ligature's type system to ensure configuration correctness across environments
- **Extensible**: Plugin system for custom operations and integrations

## Installation

```bash
# Clone the repository
git clone https://github.com/fugue-ai/ligature.git
cd ligature/apps/cacophony

# Build the CLI tool
cargo build --release

# Install globally (optional)
cargo install --path .
```

## Quick Start

### 1. Initialize a new project

```bash
cacophony init --template terraform --name my-project
```

### 2. Navigate to your project

```bash
cd my-project
```

### 3. List available resources

```bash
cacophony list --collections --environments
```

### 4. Validate your configuration

```bash
cacophony validate --environment dev
```

### 5. Deploy a collection

```bash
cacophony deploy --collection frontend --environment dev
```

## Project Structure

```
my-project/
├── cacophony.lig          # Main configuration file
├── environments/          # Environment-specific configurations
│   ├── dev.lig
│   ├── staging.lig
│   └── prod.lig
├── collections/           # Collection definitions
│   ├── frontend.lig
│   ├── backend.lig
│   └── database.lig
├── scripts/              # Custom operation scripts
│   ├── migrate.sh
│   └── test.sh
└── plugins/              # Custom plugins (optional)
    └── custom/
```

## Configuration

### Main Configuration (`cacophony.lig`)

The main configuration file defines your project structure:

```ocaml
-- cacophony.lig
module Cacophony

let project = {
  name = "my-project",
  version = "1.0.0",
  description = "My project description",
  authors = ["team@example.com"]
}

let environments = {
  dev = {
    name = "development",
    variables = {
      "DATABASE_URL" = "postgresql://localhost:5432/dev",
      "API_BASE_URL" = "http://localhost:8080"
    },
    plugins = ["terraform"]
  }
}

let collections = {
  frontend = {
    name = "frontend",
    dependencies = ["shared-types"],
    operations = ["deploy", "validate"],
    environments = ["dev", "staging", "prod"]
  }
}

export { project, environments, collections }
```

### Environment Configuration

Environment-specific configurations can override default values:

```ocaml
-- environments/dev.lig
module Dev

let overrides = {
  variables = {
    "DEBUG" = true,
    "LOG_LEVEL" = "debug"
  },

  collections = {
    frontend = {
      replicas = 1,
      resources = {
        cpu = "100m",
        memory = "128Mi"
      }
    }
  }
}

export { overrides }
```

### Collection Configuration

Each collection defines its specific configuration:

```ocaml
-- collections/frontend.lig
module Frontend

let config = {
  name = "frontend",
  type = "web",

  deploy = {
    replicas = 2,
    resources = {
      cpu = "500m",
      memory = "512Mi"
    },

    ports = [{
      container = 80,
      service = 8080,
      protocol = "http"
    }]
  },

  environment = {
    "NODE_ENV" = "production",
    "API_URL" = "${API_BASE_URL}"
  }
}

export { config }
```

## Commands

### `init`

Initialize a new cacophony project.

```bash
cacophony init --template terraform --name my-project
```

Options:

- `--template`: Template to use (terraform, microservices)
- `--name`: Project name
- `--force`: Force overwrite of existing directory

### `deploy`

Deploy a collection to an environment.

```bash
cacophony deploy --collection frontend --environment dev
```

Options:

- `--collection`: Collection name
- `--environment`: Environment name
- `--dry-run`: Show what would be deployed without actually deploying
- `--wait`: Wait for deployment to complete

### `validate`

Validate configurations.

```bash
cacophony validate --collection frontend --environment dev
```

Options:

- `--collection`: Collection name (optional)
- `--environment`: Environment name (optional)
- `--strict`: Enable strict validation mode

### `diff`

Show differences between environments.

```bash
cacophony diff --collection frontend --from dev --to prod
```

Options:

- `--collection`: Collection name
- `--from`: Source environment
- `--to`: Target environment
- `--format`: Output format (text, json, yaml)

### `list`

List available resources.

```bash
cacophony list --collections --environments --plugins --operations
```

Options:

- `--collections`: List collections
- `--environments`: List environments
- `--plugins`: List plugins
- `--operations`: List operations

### `run`

Run custom operations.

```bash
cacophony run --operation migrate --collection database --environment prod
```

Options:

- `--operation`: Operation name
- `--collection`: Collection name (optional)
- `--environment`: Environment name (optional)
- `--param`: Custom parameters (key=value format)

### `status`

Show project status.

```bash
cacophony status --environment dev --detailed
```

Options:

- `--environment`: Environment name (optional)
- `--detailed`: Show detailed status

## Plugins

Cacophony includes several built-in plugins:

### Terraform Plugin

Provides Terraform infrastructure management operations:

- `terraform-plan`: Generate Terraform execution plan
- `terraform-apply`: Apply Terraform configuration
- `terraform-destroy`: Destroy Terraform-managed infrastructure

### Custom Plugins

You can create custom plugins by implementing the `Plugin` trait:

```rust
use async_trait::async_trait;
use cacophony::plugin::Plugin;
use cacophony::operation::Operation;

pub struct CustomPlugin {
    name: String,
    version: String,
}

#[async_trait]
impl Plugin for CustomPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        "Custom plugin description"
    }

    fn operations(&self) -> Vec<Box<dyn Operation>> {
        vec![
            Box::new(CustomOperation::new()),
        ]
    }

    fn configure(&mut self, config: &serde_json::Value) -> Result<(), Box<dyn std::error::Error>> {
        // Configure plugin with provided configuration
        Ok(())
    }
}
```

## Examples

See the `examples/` directory for complete examples:

- `examples/terraform/`: Terraform infrastructure example
- `examples/microservices/`: Microservices orchestration example

## Development

### Building

```bash
# Build in debug mode
cargo build

# Build in release mode
cargo build --release

# Run tests
cargo test

# Run with logging
RUST_LOG=debug cargo run -- --help
```

### Project Structure

```
src/
├── main.rs           # CLI entry point
├── cli.rs            # Command-line interface
├── config.rs         # Configuration management
├── environment.rs    # Environment management
├── collection.rs     # Collection management
├── operation.rs      # Operation system
├── plugin.rs         # Plugin system
└── error.rs          # Error handling
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the Apache License, Version 2.0 - see the [LICENSE](../../LICENSE) file for details.

## Roadmap

- [ ] Ligature integration for parsing and evaluation
- [ ] Advanced plugin system with dynamic loading
- [ ] Web UI for configuration management
- [ ] CI/CD integration
- [ ] Monitoring and observability
- [ ] Multi-cloud support
- [ ] Policy enforcement
- [ ] Audit logging
