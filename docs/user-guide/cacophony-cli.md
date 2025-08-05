# Cacophony CLI Guide

Cacophony is a CLI tool for orchestrating collections of Ligature programs. It provides a unified interface for managing, deploying, and operating Ligature-based configurations across multiple environments and use cases.

## Overview

Cacophony is designed to be:

- **Purpose-Agnostic**: Not tied to any specific domain (Kubernetes, infrastructure, etc.) but can orchestrate any Ligature-based configuration
- **Register-Centric**: Built around Ligature's register system for dependency management and code organization
- **Environment-Aware**: Supports multiple environments (dev, staging, prod) with environment-specific configurations
- **Declarative Operations**: All operations are defined declaratively in Ligature, not imperatively in the CLI
- **Type-Safe Orchestration**: Leverages Ligature's type system to ensure configuration correctness across environments
- **Extensible**: Plugin system for custom operations and integrations

## Installation

### From Source

```bash
# Clone the repository
git clone https://github.com/fugue-ai/ligature.git
cd ligature/apps/cacophony

# Build the CLI tool
cargo build --release

# Install globally (optional)
cargo install --path .
```

### Using Cargo

```bash
# Install from crates.io (when available)
cargo install cacophony-cli
```

## Quick Start

### 1. Initialize a new project

```bash
# Create a new project with a template
cacophony init --template kubernetes --name my-project

# Or create an empty project
cacophony init --name my-project
```

### 2. Navigate to your project

```bash
cd my-project
```

### 3. List available resources

```bash
# List all collections and environments
cacophony list --collections --environments

# List specific resources
cacophony list --collections
cacophony list --environments
```

### 4. Validate your configuration

```bash
# Validate all environments
cacophony validate

# Validate specific environment
cacophony validate --environment dev
```

### 5. Deploy a collection

```bash
# Deploy a specific collection to an environment
cacophony deploy --collection frontend --environment dev

# Deploy all collections to an environment
cacophony deploy --environment dev
```

## Project Structure

A typical Cacophony project has the following structure:

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

```ligature
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
      api_url = "http://localhost:8080",
      debug = true
    }
  },
  staging = {
    name = "staging",
    variables = {
      api_url = "https://staging-api.example.com",
      debug = false
    }
  },
  prod = {
    name = "production",
    variables = {
      api_url = "https://api.example.com",
      debug = false
    }
  }
}

let collections = {
  frontend = {
    name = "Frontend Application",
    description = "Web frontend for the application",
    dependencies = ["backend"],
    operations = {
      deploy = "scripts/deploy-frontend.sh",
      test = "scripts/test-frontend.sh"
    }
  },
  backend = {
    name = "Backend API",
    description = "REST API backend",
    dependencies = ["database"],
    operations = {
      deploy = "scripts/deploy-backend.sh",
      test = "scripts/test-backend.sh"
    }
  },
  database = {
    name = "Database",
    description = "Application database",
    dependencies = [],
    operations = {
      deploy = "scripts/deploy-database.sh",
      migrate = "scripts/migrate.sh"
    }
  }
}
```

### Environment Configuration

Each environment has its own configuration file:

```ligature
-- environments/dev.lig
module Dev

let config = {
  api_url = "http://localhost:8080",
  database_url = "postgresql://localhost:5432/dev_db",
  redis_url = "redis://localhost:6379",
  log_level = "debug",
  features = {
    experimental = true,
    analytics = false
  }
}
```

### Collection Configuration

Collections define the components of your system:

```ligature
-- collections/frontend.lig
module Frontend

let config = {
  name = "frontend",
  version = "1.0.0",
  build = {
    framework = "react",
    bundler = "webpack",
    output_dir = "dist"
  },
  deployment = {
    platform = "kubernetes",
    replicas = 2,
    resources = {
      cpu = "100m",
      memory = "128Mi"
    }
  }
}
```

## CLI Commands

### Project Management

```bash
# Initialize a new project
cacophony init [OPTIONS]

# List project resources
cacophony list [OPTIONS]

# Validate project configuration
cacophony validate [OPTIONS]
```

### Deployment

```bash
# Deploy collections
cacophony deploy [OPTIONS]

# Rollback deployment
cacophony rollback [OPTIONS]

# Check deployment status
cacophony status [OPTIONS]
```

### Operations

```bash
# Run custom operations
cacophony run [OPTIONS] <OPERATION>

# Execute scripts
cacophony exec [OPTIONS] <SCRIPT>

# Test collections
cacophony test [OPTIONS]
```

### Configuration

```bash
# Show configuration
cacophony config [OPTIONS]

# Set configuration values
cacophony config set [OPTIONS] <KEY> <VALUE>

# Get configuration values
cacophony config get [OPTIONS] <KEY>
```

## Advanced Features

### Plugin System

Cacophony supports plugins for custom operations:

```ligature
-- plugins/custom/plugin.lig
module CustomPlugin

let operations = {
  custom_deploy = \config -> {
    -- Custom deployment logic
    steps = [
      "validate_config",
      "prepare_environment",
      "deploy_resources",
      "verify_deployment"
    ]
  }
}
```

### Dependency Management

Collections can declare dependencies:

```ligature
let collections = {
  frontend = {
    dependencies = ["backend", "database"],
    -- Frontend configuration
  },
  backend = {
    dependencies = ["database"],
    -- Backend configuration
  },
  database = {
    dependencies = [],
    -- Database configuration
  }
}
```

### Environment Variables

Environment-specific variables are automatically injected:

```ligature
-- Access environment variables in your Ligature code
let api_config = {
  url = env.api_url,
  timeout = env.timeout || 30,
  retries = env.retries || 3
}
```

### Type Safety

Cacophony leverages Ligature's type system for configuration validation:

```ligature
type Environment = {
  name: String,
  variables: Record String String,
  features: Record String Boolean
}

type Collection = {
  name: String,
  dependencies: List String,
  operations: Record String String
}

-- Type checking ensures configuration correctness
let validate_config = \env collection -> {
  -- Validation logic
}
```

## Best Practices

### 1. Environment Separation

Keep environment-specific configurations separate:

```ligature
-- Use environment variables for configuration
let config = {
  api_url = env.api_url,
  database_url = env.database_url,
  log_level = env.log_level
}
```

### 2. Collection Organization

Organize collections by responsibility:

```ligature
let collections = {
  -- Infrastructure
  database = { /* database config */ },
  redis = { /* redis config */ },

  -- Applications
  backend = { /* backend config */ },
  frontend = { /* frontend config */ },

  -- Monitoring
  monitoring = { /* monitoring config */ }
}
```

### 3. Dependency Management

Declare explicit dependencies:

```ligature
let collections = {
  frontend = {
    dependencies = ["backend"],
    -- Frontend depends on backend
  },
  backend = {
    dependencies = ["database", "redis"],
    -- Backend depends on database and redis
  }
}
```

### 4. Operation Scripts

Use scripts for complex operations:

```bash
#!/bin/bash
# scripts/deploy-frontend.sh

echo "Deploying frontend..."
# Deployment logic here
echo "Frontend deployed successfully"
```

### 5. Configuration Validation

Validate configurations before deployment:

```ligature
let validate_environment = \env -> {
  required_vars = ["api_url", "database_url"],
  missing = filter (\var -> !has_key env.variables var) required_vars,

  if length missing > 0 then
    error ("Missing required variables: " ++ join ", " missing)
  else
    success "Environment configuration is valid"
}
```

## Troubleshooting

### Common Issues

1. **Configuration Errors**

   ```bash
   # Validate configuration
   cacophony validate --environment dev
   ```

2. **Dependency Issues**

   ```bash
   # Check dependencies
   cacophony list --dependencies
   ```

3. **Deployment Failures**

   ```bash
   # Check deployment status
   cacophony status --environment dev

   # Rollback if needed
   cacophony rollback --environment dev
   ```

### Debug Mode

Enable debug mode for detailed output:

```bash
cacophony --debug deploy --collection frontend --environment dev
```

### Logging

Configure logging levels:

```bash
# Set log level
export CACOPHONY_LOG_LEVEL=debug

# Run with verbose output
cacophony --verbose deploy --environment dev
```

## Integration Examples

### Kubernetes Integration

```ligature
-- collections/kubernetes.lig
module Kubernetes

let k8s_config = {
  namespace = env.namespace || "default",
  replicas = env.replicas || 1,
  resources = {
    cpu = env.cpu_limit || "100m",
    memory = env.memory_limit || "128Mi"
  }
}
```

### Docker Integration

```ligature
-- collections/docker.lig
module Docker

let docker_config = {
  image = env.image || "myapp:latest",
  ports = env.ports || ["8080:8080"],
  volumes = env.volumes || []
}
```

### AWS Integration

```ligature
-- collections/aws.lig
module AWS

let aws_config = {
  region = env.aws_region || "us-west-2",
  vpc_id = env.vpc_id,
  subnet_ids = env.subnet_ids
}
```

## Getting Help

- Check the **[FAQ](../faq.md)** for common questions
- Look at **[Error Messages](../error-messages.md)** for debugging help
- Explore **[Real-world Examples](../examples.md)** for practical guidance
- Join our [Discussions](https://github.com/ligature-lang/ligature/discussions) for community support
