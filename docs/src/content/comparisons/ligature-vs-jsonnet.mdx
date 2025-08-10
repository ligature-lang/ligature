# Ligature vs Jsonnet: A Comprehensive Comparison

## Overview

This document provides a detailed comparison between Ligature and Jsonnet, two configuration languages that take different approaches to configuration generation and management - Ligature with a focus on formal verification and advanced type systems, and Jsonnet with a focus on JSON templating and code generation.

## Core Philosophy & Design Goals

### Ligature

- **Dependently-typed foundation** based on Lean 4 type theory
- **Configuration-native** design with strong validation focus
- **Correctness over performance** - prioritizes formal verification
- **Accessible to average engineers** - avoids Haskell complexity
- **Verification-ready** - foundation for formal proofs

### Jsonnet

- **JSON templating** with powerful code generation capabilities
- **Data-oriented** design focused on configuration generation
- **Performance-conscious** design for large-scale templating
- **Kubernetes-native** integration and tooling
- **Pragmatic approach** to configuration generation

## Type System Differences

### Ligature's Advanced Type System

Ligature provides a sophisticated functional programming type system:

```ocaml
// Dependent types (Pi and Sigma)
type Vector n = { length: n, elements: List n }

// Type classes with constraints
typeclass Show a where
  show: a -> String

// Higher-kinded types
typeclass Functor f where
  map: (a -> b) -> f a -> f b

// Union types with complex pattern matching
type Result a b = Success a | Error b

// Pattern matching with guards
let classify = \x -> match x {
  n when n > 0 => "positive",
  n when n < 0 => "negative",
  _ => "zero"
}
```

### Jsonnet's Simple Type System

Jsonnet uses a simple, dynamic type system focused on JSON generation:

```jsonnet
// Basic data structures
{
  name: "John",
  age: 25,
  email: "john@example.com",
  roles: ["user", "admin"]
}

// Functions for code generation
local generateUser(name, age, email) = {
  name: name,
  age: age,
  email: email,
  id: std.md5(name + email)
};

// Template-based generation
local userTemplate = {
  name: "",
  age: 0,
  email: "",
  metadata: {
    created: std.now(),
    version: "1.0"
  }
};
```

## Language Features Comparison

| Feature                   | Ligature                   | Jsonnet            |
| ------------------------- | -------------------------- | ------------------ |
| **Dependent Types**       | ✅ Full support (Pi/Sigma) | ❌ Not supported   |
| **Type Classes**          | ✅ Complete implementation | ❌ Not supported   |
| **Higher-Kinded Types**   | ✅ Supported               | ❌ Not supported   |
| **Pattern Matching**      | ✅ Advanced with guards    | ❌ Not supported   |
| **Union Types**           | ✅ Complex with payloads   | ❌ Not supported   |
| **Module System**         | ✅ Imports/exports/aliases | ✅ Import system   |
| **Formal Verification**   | ✅ Lean 4 integration      | ❌ Not supported   |
| **JSON/YAML Integration** | 🔄 Planned                 | ✅ Native support  |
| **Code Generation**       | 🔄 Basic support           | ✅ Advanced system |
| **Templating**            | 🔄 Basic support           | ✅ Primary focus   |

## Configuration Focus

### Ligature's Configuration Features

Ligature is designed for configuration with advanced type-level validation:

```ocaml
// Schema-based validation with constraints
type UserConfig = {
  name: String where length > 0,
  age: Integer where 0 <= age <= 150,
  email: String where isValidEmail
}

// Constraint satisfaction
let config = {
  name = "John",
  age = 25,
  email = "john@example.com"
} : UserConfig

// Configuration merging and inheritance
let baseConfig = { timeout = 30, retries = 3 }
let extendedConfig = { timeout = 60, debug = true }
let finalConfig = merge baseConfig extendedConfig
```

### Jsonnet's Configuration Features

Jsonnet excels at JSON generation and templating:

```jsonnet
// Template-based configuration generation
local k8sDeployment = {
  apiVersion: "apps/v1",
  kind: "Deployment",
  metadata: {
    name: "",
    namespace: "default"
  },
  spec: {
    replicas: 1,
    selector: {
      matchLabels: {
        app: ""
      }
    },
    template: {
      metadata: {
        labels: {
          app: ""
        }
      },
      spec: {
        containers: []
      }
    }
  }
};

// Function to generate deployment
local createDeployment(name, image, replicas) = k8sDeployment {
  metadata+: {
    name: name
  },
  spec+: {
    replicas: replicas,
    selector+: {
      matchLabels+: {
        app: name
      }
    },
    template+: {
      metadata+: {
        labels+: {
          app: name
        }
      },
      spec+: {
        containers: [{
          name: name,
          image: image,
          ports: [{
            containerPort: 8080
          }]
        }]
      }
    }
  }
};

// Generate multiple configurations
{
  webDeployment: createDeployment("web", "nginx:latest", 3),
  apiDeployment: createDeployment("api", "myapp:1.0", 2),
  dbDeployment: createDeployment("db", "postgres:13", 1)
}
```

## Code Generation & Templating

### Ligature's Type-Level Generation

Ligature uses its type system for generation:

```ocaml
// Type-level code generation
type ConfigTemplate = {
  name: String,
  version: String,
  environment: Environment
}

type Environment = Dev | Staging | Prod

// Pattern matching for generation
let generateConfig = \env -> match env {
  Dev => {
    name = "dev-config",
    version = "1.0.0",
    environment = Dev,
    debug = true,
    logLevel = "debug"
  },
  Staging => {
    name = "staging-config",
    version = "1.0.0",
    environment = Staging,
    debug = false,
    logLevel = "info"
  },
  Prod => {
    name = "prod-config",
    version = "1.0.0",
    environment = Prod,
    debug = false,
    logLevel = "error"
  }
}
```

### Jsonnet's Advanced Templating

Jsonnet provides powerful templating capabilities:

```jsonnet
// Advanced templating with inheritance
local baseConfig = {
  api: {
    version: "v1",
    timeout: 30,
    retries: 3
  },
  database: {
    host: "localhost",
    port: 5432
  }
};

// Environment-specific overrides
local devConfig = baseConfig {
  api+: {
    timeout: 60,
    debug: true
  },
  database+: {
    host: "dev-db.local"
  }
};

local prodConfig = baseConfig {
  api+: {
    timeout: 10,
    debug: false
  },
  database+: {
    host: "prod-db.cluster",
    ssl: true
  }
};

// Conditional generation
local generateConfig(environment) =
  if environment == "dev" then devConfig
  else if environment == "prod" then prodConfig
  else baseConfig;

// Multi-environment generation
{
  dev: generateConfig("dev"),
  staging: generateConfig("staging"),
  prod: generateConfig("prod")
}
```

## Syntax & Usability

### Ligature's ML-Family Syntax

Ligature uses functional programming syntax:

```ocaml
// ML-inspired syntax
let add = \x -> \y -> x + y

// Pattern matching with guards
let result = match value {
  Some x when x > 0 => "positive",
  Some x => "non-positive",
  None => "missing"
}

// Type annotations
let processUser: User -> String = \user ->
  match user {
    Admin { name } => "Admin: " ++ name,
    Regular { name, role } => "User: " ++ name ++ " (" ++ role ++ ")"
  }
```

### Jsonnet's JSON-Like Syntax

Jsonnet uses JSON-like syntax with extensions:

```jsonnet
// JSON-like structure with functions
{
  users: [
    {
      name: "Alice",
      role: "admin",
      permissions: ["read", "write", "delete"]
    },
    {
      name: "Bob",
      role: "user",
      permissions: ["read"]
    }
  ],

  // Computed values
  totalUsers: std.length(self.users),
  adminUsers: std.filter(function(u) u.role == "admin", self.users),

  // Conditional fields
  metadata: {
    generated: std.now(),
    version: "1.0",
    if std.length(self.users) > 10: {
      warning: "Large number of users"
    }
  }
}
```

## Integration & Ecosystem

### Ligature

- **Package management** via `keywork` system
- **Client SDKs** via `krox` framework
- **Language server** for IDE support
- **Formal specification** in Lean 4
- **Differential testing** against formal spec
- **Comprehensive test suite** (100+ tests)

### Jsonnet

- **Kubernetes integration** with native tooling
- **JSON/YAML output** with validation
- **CLI tools** for generation and validation
- **Go integration** with official bindings
- **Template libraries** for common patterns
- **IDE support** with syntax highlighting

## Error Handling & Safety

### Ligature

- **Comprehensive error reporting** with source locations
- **Type-level error prevention** via dependent types
- **Formal error semantics** defined in Lean 4
- **Pattern matching exhaustiveness** checking
- **Advanced type inference** with constraint solving

### Jsonnet

- **Runtime error reporting** with stack traces
- **Type safety** through runtime checking
- **Import safety** with file verification
- **Basic error handling** patterns
- **Simple type inference**

## Performance & Scalability

### Ligature

- **Correctness over performance** design
- **Formal verification** overhead
- **Rich type system** complexity
- **Configuration-focused** optimization
- **Early development** stage

### Jsonnet

- **Performance-optimized** for large templates
- **Efficient JSON generation** algorithms
- **Fast template processing**
- **Scalable generation** for complex configurations
- **Production-ready** performance

## Use Cases

### Ligature Best For

- **Critical configuration** requiring formal verification
- **Complex validation** with dependent types
- **Research and academic** applications
- **Safety-critical systems** where correctness is paramount
- **Advanced type-level programming**
- **Configuration with complex constraints**
- **Systems requiring formal proofs**

### Jsonnet Best For

- **Kubernetes configuration** generation
- **Large-scale JSON/YAML** templating
- **Configuration code generation** and automation
- **Multi-environment** configuration management
- **API configuration** generation
- **Infrastructure as Code** (IaC) templating
- **Configuration that needs to be human-readable**

## Development Status

### Ligature

- **Early development** stage
- **Core infrastructure** in place
- **Comprehensive test suite** (100+ tests, 100% pass rate)
- **Formal specification** in Lean 4
- **Active development** with clear roadmap

### Jsonnet

- **Mature and stable** language
- **Production-ready** with extensive usage
- **Well-documented** with tutorials and examples
- **Active community** and ecosystem
- **Google-backed** development

## Learning Curve

### Ligature

- **Steeper learning curve** due to advanced type system
- **Requires understanding** of dependent types
- **Formal verification** concepts may be unfamiliar
- **More powerful** but more complex

### Jsonnet

- **Gentler learning curve** for JSON developers
- **Familiar syntax** for configuration management
- **Practical focus** on templating and generation
- **Good documentation** and examples

## Future Directions

### Ligature

- **Formal verification** integration
- **Advanced type system** features
- **Configuration-specific** optimizations
- **Academic and research** applications
- **Safety-critical** system adoption

### Jsonnet

- **Enhanced Kubernetes** integration
- **Performance improvements** for large templates
- **Extended templating** capabilities
- **Community growth** and adoption
- **Enterprise features** and tooling

## Summary

**Ligature** represents a more **academically rigorous** approach to configuration languages, with dependent types, type classes, and formal verification capabilities. It's designed for scenarios where **correctness is more important than convenience** and where the advanced type system features provide significant value.

**Jsonnet** represents a more **pragmatic approach** focused on **JSON templating and code generation**, particularly in the context of Kubernetes and large-scale configuration management. It's designed for **real-world templating** scenarios where JSON/YAML generation and configuration automation are primary concerns.

### Key Differences

1. **Type System**: Ligature has a much more advanced type system with dependent types and type classes, while Jsonnet focuses on simple, dynamic typing for JSON generation.

2. **Philosophy**: Ligature prioritizes correctness and formal verification, while Jsonnet prioritizes practical templating and code generation.

3. **Syntax**: Ligature uses functional programming syntax, while Jsonnet uses JSON-like syntax with extensions.

4. **Focus**: Ligature targets safety-critical and research applications, while Jsonnet targets configuration generation and templating.

5. **Maturity**: Jsonnet is production-ready with Google backing, while Ligature is in early development with ambitious goals.

The choice between Ligature and Jsonnet depends on your specific needs: if you require advanced type system features and formal verification, Ligature is the better choice. If you need powerful JSON templating, code generation, and Kubernetes configuration management, Jsonnet is the better choice.
