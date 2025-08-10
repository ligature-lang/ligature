# Ligature vs Cuelang: A Comprehensive Comparison

## Overview

This document provides a detailed comparison between Ligature and Cuelang, two configuration languages that approach configuration management from different perspectives - Ligature with a focus on formal verification and advanced type systems, and Cuelang with a focus on data validation and constraint solving.

## Core Philosophy & Design Goals

### Ligature

- **Dependently-typed foundation** based on Lean 4 type theory
- **Configuration-native** design with strong validation focus
- **Correctness over performance** - prioritizes formal verification
- **Accessible to average engineers** - avoids Haskell complexity
- **Verification-ready** - foundation for formal proofs

### Cuelang

- **Constraint-based validation** with powerful data modeling
- **JSON superset** with schema validation capabilities
- **Performance-focused** design for large-scale data
- **Kubernetes-native** integration and tooling
- **Pragmatic approach** to configuration and data validation

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

### Cuelang's Constraint-Based System

Cuelang uses a constraint-based approach focused on data validation:

```cue
// Schema definition with constraints
#User: {
  name: string & !=""
  age: int & >=0 & <=150
  email: string & regexp("^[^@]+@[^@]+\\.[^@]+$")
  role: "admin" | "user" | "guest"
}

// Data validation
user: #User & {
  name: "John"
  age: 25
  email: "john@example.com"
  role: "user"
}

// Constraint inheritance and composition
#AdminUser: #User & {
  role: "admin"
  permissions: [...string]
}
```

## Language Features Comparison

| Feature                   | Ligature                   | Cuelang            |
| ------------------------- | -------------------------- | ------------------ |
| **Dependent Types**       | ✅ Full support (Pi/Sigma) | ❌ Not supported   |
| **Type Classes**          | ✅ Complete implementation | ❌ Not supported   |
| **Higher-Kinded Types**   | ✅ Supported               | ❌ Not supported   |
| **Pattern Matching**      | ✅ Advanced with guards    | ✅ Basic support   |
| **Union Types**           | ✅ Complex with payloads   | ✅ Simple unions   |
| **Module System**         | ✅ Imports/exports/aliases | ✅ Package system  |
| **Formal Verification**   | ✅ Lean 4 integration      | ❌ Not supported   |
| **JSON/YAML Integration** | 🔄 Planned                 | ✅ Native support  |
| **Constraint Solving**    | 🔄 Basic support           | ✅ Advanced system |
| **Data Validation**       | ✅ Type-level              | ✅ Schema-based    |

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

### Cuelang's Configuration Features

Cuelang excels at data validation and constraint-based configuration:

```cue
// Comprehensive schema validation
#ServiceConfig: {
  name: string & !=""
  port: int & >=1024 & <=65535
  replicas: int & >=1 & <=100
  environment: "dev" | "staging" | "prod"
  resources: {
    cpu: string & regexp("^[0-9]+m$")
    memory: string & regexp("^[0-9]+Mi$")
  }
}

// Configuration with defaults and validation
service: #ServiceConfig & {
  name: "web-server"
  port: 8080
  replicas: 3
  environment: "prod"
  resources: {
    cpu: "500m"
    memory: "512Mi"
  }
}

// Template-based configuration generation
#K8sDeployment: {
  apiVersion: "apps/v1"
  kind: "Deployment"
  metadata: {
    name: string
    namespace: string
  }
  spec: {
    replicas: int
    selector: {
      matchLabels: {
        app: string
      }
    }
    template: {
      metadata: {
        labels: {
          app: string
        }
      }
      spec: {
        containers: [{
          name: string
          image: string
          ports: [{
            containerPort: int
          }]
        }]
      }
    }
  }
}
```

## Data Validation & Constraints

### Ligature's Type-Level Validation

Ligature uses its type system for validation:

```ocaml
// Type-level constraints
type ValidEmail = String where isValidEmail
type ValidPort = Integer where 1024 <= port <= 65535
type ValidAge = Integer where 0 <= age <= 150

// Dependent types for validation
type User = {
  name: String where length > 0,
  age: ValidAge,
  email: ValidEmail
}

// Pattern matching for validation
let validateUser = \user -> match user {
  { name, age, email } when length name > 0 && 0 <= age <= 150 =>
    Some user,
  _ => None
}
```

### Cuelang's Constraint-Based Validation

Cuelang provides powerful constraint solving:

```cue
// Advanced constraint definitions
#NetworkConfig: {
  // Port must be in valid range
  port: int & >=1024 & <=65535

  // Hostname must be valid
  hostname: string & regexp("^[a-zA-Z0-9.-]+$")

  // SSL configuration
  ssl: {
    enabled: bool
    certificate: string | *""
    key: string | *""
  } & {
    // If SSL enabled, certificate and key must be provided
    if ssl.enabled {
      certificate: string & !=""
      key: string & !=""
    }
  }
}

// Cross-field validation
#DatabaseConfig: {
  host: string
  port: int
  username: string
  password: string
  ssl: bool
} & {
  // If SSL is enabled, port should be 5432 (PostgreSQL SSL)
  if ssl {
    port: 5432
  }
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

### Cuelang's JSON-Like Syntax

Cuelang uses JSON-like syntax with extensions:

```cue
// JSON-like structure with constraints
config: {
  api: {
    version: "v1"
    timeout: 30
    retries: 3
  }

  database: {
    host: "localhost"
    port: 5432
    name: "myapp"
  }
}

// Conditional fields
environment: "prod" | "dev"
config: {
  if environment == "prod" {
    debug: false
    logLevel: "error"
  }
  if environment == "dev" {
    debug: true
    logLevel: "debug"
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

### Cuelang

- **Kubernetes integration** with native tooling
- **JSON/YAML output** with validation
- **CLI tools** for validation and generation
- **Go integration** with official bindings
- **Schema validation** for multiple formats
- **Template system** for code generation

## Error Handling & Safety

### Ligature

- **Comprehensive error reporting** with source locations
- **Type-level error prevention** via dependent types
- **Formal error semantics** defined in Lean 4
- **Pattern matching exhaustiveness** checking
- **Advanced type inference** with constraint solving

### Cuelang

- **Detailed validation errors** with field paths
- **Constraint violation reporting** with context
- **Schema validation** with clear error messages
- **Type safety** through constraint checking
- **Import safety** with package verification

## Performance & Scalability

### Ligature

- **Correctness over performance** design
- **Formal verification** overhead
- **Rich type system** complexity
- **Configuration-focused** optimization
- **Early development** stage

### Cuelang

- **Performance-optimized** for large data
- **Efficient constraint solving** algorithms
- **Fast JSON/YAML processing**
- **Scalable validation** for complex schemas
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

### Cuelang Best For

- **Kubernetes configuration** management
- **Large-scale data validation** and processing
- **JSON/YAML schema validation**
- **Configuration templating** and generation
- **API schema validation** and documentation
- **Data transformation** and normalization
- **Infrastructure as Code** (IaC) validation

## Development Status

### Ligature

- **Early development** stage
- **Core infrastructure** in place
- **Comprehensive test suite** (100+ tests, 100% pass rate)
- **Formal specification** in Lean 4
- **Active development** with clear roadmap

### Cuelang

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

### Cuelang

- **Gentler learning curve** for JSON/Go developers
- **Familiar syntax** for configuration management
- **Practical focus** on data validation
- **Good documentation** and examples

## Future Directions

### Ligature

- **Formal verification** integration
- **Advanced type system** features
- **Configuration-specific** optimizations
- **Academic and research** applications
- **Safety-critical** system adoption

### Cuelang

- **Enhanced Kubernetes** integration
- **Performance improvements** for large datasets
- **Extended constraint** solving capabilities
- **Community growth** and adoption
- **Enterprise features** and tooling

## Summary

**Ligature** represents a more **academically rigorous** approach to configuration languages, with dependent types, type classes, and formal verification capabilities. It's designed for scenarios where **correctness is more important than convenience** and where the advanced type system features provide significant value.

**Cuelang** represents a more **pragmatic approach** focused on **data validation and constraint solving**, particularly in the context of Kubernetes and large-scale configuration management. It's designed for **real-world data validation** scenarios where JSON/YAML processing and schema validation are primary concerns.

### Key Differences

1. **Type System**: Ligature has a much more advanced type system with dependent types and type classes, while Cuelang focuses on constraint-based validation.

2. **Philosophy**: Ligature prioritizes correctness and formal verification, while Cuelang prioritizes practical data validation and constraint solving.

3. **Syntax**: Ligature uses functional programming syntax, while Cuelang uses JSON-like syntax with constraints.

4. **Focus**: Ligature targets safety-critical and research applications, while Cuelang targets data validation and Kubernetes configuration.

5. **Maturity**: Cuelang is production-ready with Google backing, while Ligature is in early development with ambitious goals.

The choice between Ligature and Cuelang depends on your specific needs: if you require advanced type system features and formal verification, Ligature is the better choice. If you need powerful data validation, constraint solving, and Kubernetes integration, Cuelang is the better choice.
