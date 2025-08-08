# Real-world Examples

This guide provides practical examples of how to use Ligature for real-world configuration and data management tasks.

## Table of Contents

1. [Application Configuration](#application-configuration)
2. [Data Validation](#data-validation)
3. [Constraint-Based Validation](#constraint-based-validation)
4. [Type Classes and Instances](#type-classes-and-instances)
5. [API Configuration](#api-configuration)
6. [Database Configuration](#database-configuration)
7. [Build System Configuration](#build-system-configuration)
8. [Microservices Configuration](#microservices-configuration)
9. [Testing Configuration](#testing-configuration)

## Application Configuration

### Basic App Configuration

```ocaml
// app-config.lig
type Environment = Development | Staging | Production;

type LogLevel = Debug | Info | Warn | Error;

type AppConfig = {
    name: String,
    version: String,
    environment: Environment,
    debug: Boolean,
    log_level: LogLevel,
    port: Integer,
    host: String,
    max_connections: Integer,
    timeout_seconds: Integer
};

let default_config = {
    name = "MyApplication",
    version = "1.0.0",
    environment = Development,
    debug = true,
    log_level = Debug,
    port = 8080,
    host = "localhost",
    max_connections = 100,
    timeout_seconds = 30
};

let production_config = {
    name = "MyApplication",
    version = "1.0.0",
    environment = Production,
    debug = false,
    log_level = Info,
    port = 80,
    host = "0.0.0.0",
    max_connections = 1000,
    timeout_seconds = 60
};
```

### Environment-Specific Configuration

```ocaml
// config/environment.lig
module Environment {
    type Environment = Development | Staging | Production;

    let get_config = \env -> match env of
        Development => {
            debug = true,
            log_level = Debug,
            port = 8080,
            host = "localhost"
        },
        Staging => {
            debug = false,
            log_level = Info,
            port = 8080,
            host = "staging.example.com"
        },
        Production => {
            debug = false,
            log_level = Warn,
            port = 80,
            host = "api.example.com"
        };

    let validate_config = \config -> match config of
        { debug = d, log_level = l, port = p } when
            (d == true && l == Debug) ||
            (d == false && (l == Info || l == Warn || l == Error)) &&
            p > 0 && p <= 65535 => Valid,
        _ => Invalid "Invalid configuration"
}
```

## Data Validation

### Constraint-Based Validation

Ligature's constraint-based validation system allows you to create types with built-in validation rules, ensuring data integrity at the type level.

#### Basic Constraint Types

```ocaml
// constraints/basic.lig
module BasicConstraints {
    // Refinement types with predicates
    type PositiveInt = Integer where x > 0;
    type ValidAge = Integer where x >= 0 && x <= 150;
    type NonZero = Integer where x != 0;

    // Pattern constraints for strings
    type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
    type ValidPhone = String with pattern("\\d{3}-\\d{3}-\\d{4}");
    type NonEmptyString = String with length > 0;

    // Multiple constraints
    type ValidPort = Integer with x > 0 && x <= 65535;
    type AlphaString = String with regexp("^[A-Za-z]+$") with length > 0;
}
```

#### User Data Validation with Constraints

```ocaml
// validation/user_constraints.lig
module UserConstraintValidation {
    // Define constrained types for user data
    type ValidName = String with length > 0 && length <= 50;
    type ValidAge = Integer where x >= 0 && x <= 150;
    type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");
    type ValidUserRole = Admin | User | Guest;

    // Custom validation function for complex user validation
    let isValidUser = \user ->
        length user.name > 0 &&
        user.age >= 0 &&
        user.age <= 150 &&
        contains user.email "@";

    // Refinement type using custom validation function
    type ValidUser = {
        name: ValidName,
        age: ValidAge,
        email: ValidEmail,
        role: ValidUserRole
    } where isValidUser x;

    // Example usage
    let create_user = \name age email role -> {
        name = name,  // Will be validated as ValidName
        age = age,    // Will be validated as ValidAge
        email = email, // Will be validated as ValidEmail
        role = role   // Will be validated as ValidUserRole
    };

    // Valid user creation
    let alice = create_user "Alice" 25 "alice@example.com" User;

    // Invalid user creation (will cause validation errors)
    // let invalid_user = create_user "" -5 "invalid-email" InvalidRole;
}
```

#### Configuration Validation with Constraints

```ocaml
// validation/config_constraints.lig
module ConfigConstraintValidation {
    // Constrained types for configuration
    type ValidPort = Integer where x > 0 && x <= 65535;
    type ValidHost = String with length > 0;
    type ValidTimeout = Integer where x > 0 && x <= 3600;
    type ValidLogLevel = Debug | Info | Warn | Error;

    // Custom validation for configuration
    let isValidConfig = \config ->
        config.port > 0 &&
        config.port <= 65535 &&
        length config.host > 0 &&
        config.timeout > 0 &&
        config.timeout <= 3600;

    // Refinement type for valid configuration
    type ValidConfig = {
        port: ValidPort,
        host: ValidHost,
        timeout: ValidTimeout,
        log_level: ValidLogLevel
    } where isValidConfig x;

    // Environment-specific configurations
    let development_config = {
        port = 8080,           // Valid port
        host = "localhost",    // Valid host
        timeout = 30,          // Valid timeout
        log_level = Debug      // Valid log level
    };

    let production_config = {
        port = 80,             // Valid port
        host = "api.example.com", // Valid host
        timeout = 60,          // Valid timeout
        log_level = Info       // Valid log level
    };
}
```

## Constraint-Based Validation

For comprehensive constraint-based validation examples, see the dedicated [Constraint-Based Validation Guide](constraint-validation.md) and the example file `examples/constraint_validation_examples.lig`.

### Key Features Demonstrated

- **Refinement Types**: `type PositiveInt = Integer where x > 0;`
- **Pattern Constraints**: `type ValidEmail = String with regexp("^[^@]+@[^@]+\\.[^@]+$");`
- **Value Constraints**: `type ValidPort = Integer with x > 0 && x <= 65535;`
- **Multiple Constraints**: `type ValidPassword = String with regexp("^[A-Za-z0-9@#$%^&+=]+$") with length >= 8;`
- **Record Refinement Types**: Complex validation for structured data
- **Custom Validation Functions**: User-defined validation logic

### Traditional Validation Functions

For cases where you need more complex validation logic or want to provide custom error messages, you can still use traditional validation functions:

```ocaml
// validation/user.lig
module UserValidation {
    type ValidationResult = Valid | Invalid String;

    type User = {
        name: String,
        age: Integer,
        email: String,
        role: UserRole
    };

    type UserRole = Admin | User | Guest;

    let validate_name = \name -> match name of
        n when length n == 0 => Invalid "Name cannot be empty",
        n when length n > 50 => Invalid "Name too long",
        _ => Valid;

    let validate_age = \age -> match age of
        a when a < 0 => Invalid "Age cannot be negative",
        a when a > 150 => Invalid "Age seems unrealistic",
        _ => Valid;

    let validate_email = \email -> match email of
        e when contains e "@" && contains e "." => Valid,
        _ => Invalid "Invalid email format";

    let validate_role = \role -> match role of
        Admin | User | Guest => Valid,
        _ => Invalid "Invalid user role";

    let validate_user = \user -> match user of
        { name = n, age = a, email = e, role = r } =>
            case validate_name n of
                Valid => case validate_age a of
                    Valid => case validate_email e of
                        Valid => validate_role r,
                        Invalid msg => Invalid msg,
                    Invalid msg => Invalid msg,
                Invalid msg => Invalid msg;
}
```

### Configuration Validation

```ocaml
// validation/config.lig
module ConfigValidation {
    type ValidationResult = Valid | Invalid String;

    let validate_port = \port -> match port of
        p when p > 0 && p <= 65535 => Valid,
        _ => Invalid "Port must be between 1 and 65535";

    let validate_host = \host -> match host of
        h when length h > 0 => Valid,
        _ => Invalid "Host cannot be empty";

    let validate_timeout = \timeout -> match timeout of
        t when t > 0 && t <= 3600 => Valid,
        _ => Invalid "Timeout must be between 1 and 3600 seconds";

    let validate_config = \config -> match config of
        { port = p, host = h, timeout = t } =>
            case validate_port p of
                Valid => case validate_host h of
                    Valid => validate_timeout t,
                    Invalid msg => Invalid msg,
                Invalid msg => Invalid msg;
}
```

## Type Classes and Instances

### Basic Type Classes

```ocaml
// typeclasses/basic.lig
module BasicTypeClasses {
    // Type class for equality
    typeclass Eq 'a where
        eq : 'a -> 'a -> Bool;

    // Type class for ordering
    typeclass Ord 'a where
        superclass Eq 'a;
        compare : 'a -> 'a -> Ordering;

    // Type class for string representation
    typeclass Show 'a where
        show : 'a -> String;

    // Implement Eq for basic types
    instance Eq Int where
        eq = \x y -> x == y;

    instance Eq Bool where
        eq = \x y -> x == y;

    instance Eq String where
        eq = \x y -> x == y;

    // Implement Ord for basic types
    instance Ord Int where
        compare = \x y -> if x < y then LT else if x == y then EQ else GT;

    instance Ord Bool where
        compare = \x y -> if x == y then EQ else if x then GT else LT;

    // Implement Show for basic types
    instance Show Int where
        show = \x -> toString x;

    instance Show Bool where
        show = \b -> if b then "true" else "false";

    instance Show String where
        show = \s -> s;
}
```

### Custom Type Instances

```ocaml
// typeclasses/custom.lig
module CustomTypeClasses {
    import "./basic" { Eq, Ord, Show };

    // Custom types
    type Point = { x: Integer, y: Integer };
    type Color = Red | Green | Blue;
    type Pair = { first: 'a, second: 'b };

    // Implement Eq for Point
    instance Eq Point where
        eq = \p1 p2 -> eq p1.x p2.x && eq p1.y p2.y;

    // Implement Ord for Point (lexicographic ordering)
    instance Ord Point where
        compare = \p1 p2 ->
            case compare p1.x p2.x of
                EQ => compare p1.y p2.y,
                result => result;

    // Implement Show for Point
    instance Show Point where
        show = \p -> "Point(" ++ show p.x ++ ", " ++ show p.y ++ ")";

    // Implement Eq for Color
    instance Eq Color where
        eq = \c1 c2 -> match (c1, c2) of
            (Red, Red) => true,
            (Green, Green) => true,
            (Blue, Blue) => true,
            _ => false;

    // Implement Show for Color
    instance Show Color where
        show = \c -> match c of
            Red => "Red",
            Green => "Green",
            Blue => "Blue";

    // Constrained instance for Pair
    instance (Eq 'a, Eq 'b) => Eq (Pair 'a 'b) where
        eq = \p1 p2 -> eq p1.first p2.first && eq p1.second p2.second;

    // Constrained instance for Show
    instance (Show 'a, Show 'b) => Show (Pair 'a 'b) where
        show = \p -> "Pair(" ++ show p.first ++ ", " ++ show p.second ++ ")";
}
```

### Advanced Type Classes

```ocaml
// typeclasses/advanced.lig
module AdvancedTypeClasses {
    import "./basic" { Eq, Show };

    // Type class for numeric operations
    typeclass Num 'a where
        add : 'a -> 'a -> 'a;
        multiply : 'a -> 'a -> 'a;
        zero : 'a;
        one : 'a;

    // Type class for collections
    typeclass Collection 'a 'b where
        empty : 'a 'b;
        insert : 'b -> 'a 'b -> 'a 'b;
        contains : 'b -> 'a 'b -> Bool;
        size : 'a 'b -> Integer;

    // Implement Num for Integer
    instance Num Integer where
        add = \x y -> x + y;
        multiply = \x y -> x * y;
        zero = 0;
        one = 1;

    // Implement Num for Float
    instance Num Float where
        add = \x y -> x + y;
        multiply = \x y -> x * y;
        zero = 0.0;
        one = 1.0;

    // Generic functions using type classes
    let sum : Num 'a => List 'a -> 'a = \list ->
        fold add zero list;

    let product : Num 'a => List 'a -> 'a = \list ->
        fold multiply one list;

    let max : Ord 'a => 'a -> 'a -> 'a = \x y ->
        if compare x y == GT then x else y;

    let min : Ord 'a => 'a -> 'a -> 'a = \x y ->
        if compare x y == LT then x else y;
}
```

### Type Class Constraints in Functions

```ocaml
// typeclasses/constraints.lig
module TypeClassConstraints {
    import "./basic" { Eq, Ord, Show };
    import "./advanced" { Num };

    // Functions with type class constraints
    let is_sorted : Ord 'a => List 'a -> Bool = \list ->
        case list of
            [] => true,
            [x] => true,
            Cons x (Cons y rest) =>
                if compare x y == GT then false
                else is_sorted (Cons y rest);

    let remove_duplicates : Eq 'a => List 'a -> List 'a = \list ->
        case list of
            [] => [],
            Cons x rest =>
                if contains x rest then remove_duplicates rest
                else Cons x (remove_duplicates rest);

    let format_list : Show 'a => List 'a -> String = \list ->
        case list of
            [] => "[]",
            Cons x rest => "[" ++ show x ++ format_rest rest
        where
            format_rest = \rest -> case rest of
                [] => "]",
                Cons x rest => ", " ++ show x ++ format_rest rest;

    // Complex constraint example
    let sort_and_show : (Ord 'a, Show 'a) => List 'a -> String = \list ->
        let sorted = sort list;
        format_list sorted;
}
```

## API Configuration

### REST API Configuration

```ocaml
// api/rest.lig
module RestApi {
    type HttpMethod = GET | POST | PUT | DELETE | PATCH;

    type Endpoint = {
        path: String,
        method: HttpMethod,
        handler: String,
        auth_required: Boolean,
        rate_limit: Integer
    };

    type ApiConfig = {
        base_url: String,
        port: Integer,
        endpoints: List Endpoint,
        cors_enabled: Boolean,
        cors_origins: List String
    };

    let validate_endpoint = \endpoint -> match endpoint of
        { path = p, method = m, handler = h, rate_limit = r } when
            length p > 0 &&
            length h > 0 &&
            r >= 0 => Valid,
        _ => Invalid "Invalid endpoint configuration";

    let validate_api_config = \config -> match config of
        { base_url = url, port = p, endpoints = eps } when
            length url > 0 &&
            p > 0 && p <= 65535 =>
                all validate_endpoint eps,
        _ => Invalid "Invalid API configuration";
}
```

### GraphQL Configuration

```ocaml
// api/graphql.lig
module GraphQL {
    type GraphQLType = {
        name: String,
        fields: List GraphQLField,
        description: String
    };

    type GraphQLField = {
        name: String,
        type: String,
        nullable: Boolean,
        description: String
    };

    type GraphQLConfig = {
        schema_path: String,
        introspection_enabled: Boolean,
        playground_enabled: Boolean,
        max_query_depth: Integer,
        max_query_complexity: Integer
    };

    let validate_graphql_config = \config -> match config of
        { max_query_depth = d, max_query_complexity = c } when
            d > 0 && d <= 20 &&
            c > 0 && c <= 1000 => Valid,
        _ => Invalid "Invalid GraphQL configuration";
}
```

## Database Configuration

### PostgreSQL Configuration

```ocaml
// database/postgres.lig
module Postgres {
    type PostgresConfig = {
        host: String,
        port: Integer,
        database: String,
        username: String,
        password: String,
        ssl_mode: SSLMode,
        max_connections: Integer,
        connection_timeout: Integer
    };

    type SSLMode = Disable | Allow | Prefer | Require | VerifyCA | VerifyFull;

    let validate_postgres_config = \config -> match config of
        { host = h, port = p, database = db, username = u, max_connections = mc } when
            length h > 0 &&
            p > 0 && p <= 65535 &&
            length db > 0 &&
            length u > 0 &&
            mc > 0 && mc <= 100 => Valid,
        _ => Invalid "Invalid PostgreSQL configuration";
}
```

### Redis Configuration

```ocaml
// database/redis.lig
module Redis {
    type RedisConfig = {
        host: String,
        port: Integer,
        password: String,
        database: Integer,
        max_connections: Integer,
        timeout: Integer
    };

    let validate_redis_config = \config -> match config of
        { host = h, port = p, database = db, max_connections = mc } when
            length h > 0 &&
            p > 0 && p <= 65535 &&
            db >= 0 && db <= 15 &&
            mc > 0 && mc <= 50 => Valid,
        _ => Invalid "Invalid Redis configuration";
}
```

## Build System Configuration

### Build Configuration

```ocaml
// build/config.lig
module BuildConfig {
    type BuildTarget = Debug | Release | Profile;

    type BuildConfig = {
        target: BuildTarget,
        optimization_level: Integer,
        debug_symbols: Boolean,
        warnings_as_errors: Boolean,
        parallel_builds: Integer
    };

    let get_build_flags = \config -> match config of
        { target = t, optimization_level = opt, debug_symbols = debug } =>
            case t of
                Debug => ["--debug", "--no-optimize"],
                Release => ["--release", "--optimize=" ++ toString opt],
                Profile => ["--profile", "--debug-symbols=" ++ toString debug];
}
```

## Microservices Configuration

### Service Discovery

```ocaml
// microservices/discovery.lig
module ServiceDiscovery {
    type ServiceInfo = {
        name: String,
        version: String,
        host: String,
        port: Integer,
        health_check: String,
        tags: List String
    };

    type DiscoveryConfig = {
        registry_url: String,
        service_name: String,
        service_port: Integer,
        health_check_interval: Integer,
        deregister_after: Integer
    };

    let validate_service_info = \service -> match service of
        { name = n, host = h, port = p, health_check = hc } when
            length n > 0 &&
            length h > 0 &&
            p > 0 && p <= 65535 &&
            length hc > 0 => Valid,
        _ => Invalid "Invalid service information";
}
```

## Testing Configuration

### Test Configuration

```ocaml
// testing/config.lig
module TestConfig {
    type TestFramework = Unit | Integration | E2E;

    type TestConfig = {
        framework: TestFramework,
        timeout: Integer,
        parallel: Boolean,
        coverage_enabled: Boolean,
        coverage_threshold: Float
    };

    let get_test_command = \config -> match config of
        { framework = f, timeout = t, parallel = p } =>
            case f of
                Unit => "cargo test --unit",
                Integration => "cargo test --integration",
                E2E => "cargo test --e2e";
}
```

## Complete Example: Web Application

```ocaml
// app/main.lig
module WebApp {
    import "./config/environment" { Environment, get_config };
    import "./validation/config" { validate_config };
    import "./api/rest" { ApiConfig, validate_api_config };
    import "./database/postgres" { PostgresConfig, validate_postgres_config };

    type AppConfig = {
        environment: Environment,
        api: ApiConfig,
        database: PostgresConfig,
        logging: LogConfig
    };

    type LogConfig = {
        level: LogLevel,
        format: LogFormat,
        output: LogOutput
    };

    type LogLevel = Debug | Info | Warn | Error;
    type LogFormat = JSON | Text;
    type LogOutput = Console | File String;

    let validate_app_config = \config -> match config of
        { api = api_config, database = db_config } =>
            case validate_api_config api_config of
                Valid => validate_postgres_config db_config,
                Invalid msg => Invalid msg;

    let production_config = {
        environment = Production,
        api = {
            base_url = "https://api.example.com",
            port = 443,
            endpoints = [],
            cors_enabled = true,
            cors_origins = ["https://example.com"]
        },
        database = {
            host = "db.example.com",
            port = 5432,
            database = "myapp",
            username = "app_user",
            password = "secret",
            ssl_mode = Require,
            max_connections = 50,
            connection_timeout = 30
        },
        logging = {
            level = Info,
            format = JSON,
            output = File "/var/log/app.log"
        }
    };

    let validate_and_get_config = \env ->
        let config = get_config env;
        case validate_app_config config of
            Valid => Some config,
            Invalid msg => None;
}
```

This comprehensive set of examples demonstrates how to use Ligature for real-world configuration management, data validation, and type system features. The examples show both basic and advanced usage patterns that are commonly needed in production systems.
