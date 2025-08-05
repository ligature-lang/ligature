# Ligature Registers

This directory contains the standard library registers for Ligature. Registers are the library system for Ligature, providing reusable modules, types, and functions.

## Directory Structure

```
registers/
├── stdlib/                    # Standard library
│   ├── core/                 # Core types and functions
│   │   └── mod.lig          # Bool, Unit, Option, Result types
│   ├── collections/          # Collection types and operations
│   │   └── mod.lig          # List, Map, Set operations
│   ├── validation/           # Data validation utilities
│   │   └── mod.lig          # Email, URL, pattern validation
│   └── register.toml        # Register manifest
├── config/                   # Configuration utilities (planned)
├── crypto/                   # Cryptographic utilities (planned)
└── README.md                # This file
```

## Using Registers

### Importing Modules

```ocaml
-- Import entire module
import stdlib.core

-- Import specific items
import { List, map, filter } from stdlib.collections

-- Import with alias
import stdlib.validation as validation

-- Use imported items
let myList : List<Int> = [1, 2, 3]
let doubled = map(fun x -> x * 2, myList)
let isValid = validation.isValidEmail("test@example.com")
```

### Register Manifest

Each register includes a `register.toml` manifest file that defines:

- Register metadata (name, version, description)
- Dependencies on other registers
- Exported modules
- Additional metadata (tags, authors, license)

Example manifest:

```toml
[register]
name = "stdlib"
version = "1.0.0"
description = "Ligature Standard Library"
authors = ["Ligature Team <team@ligature.dev>"]
license = "Apache-2.0"

[dependencies]
# No dependencies for stdlib

[exports]
core = "core/mod.lig"
collections = "collections/mod.lig"
validation = "validation/mod.lig"
```

## Available Modules

### Core (`stdlib.core`)

Core types and functions that are fundamental to Ligature:

- **Types**: `Bool`, `Unit`, `Option<T>`, `Result<T, E>`
- **Functions**: `not`, `and`, `or`, `isSome`, `isNone`, `map`

### Collections (`stdlib.collections`)

Collection types and higher-order functions:

- **Types**: `List<T>`
- **Functions**: `isEmpty`, `length`, `head`, `tail`, `map`, `filter`, `fold`, `append`, `reverse`

### Validation (`stdlib.validation`)

Data validation utilities:

- **Types**: `ValidationError`
- **Functions**: `validateEmail`, `validateUrl`, `validateLength`, `validatePattern`

## Development

### Adding New Registers

1. Create a new directory in `registers/`
2. Add a `register.toml` manifest file
3. Create modules with `.lig` files
4. Use `module` declarations and `export` statements
5. Add dependencies if needed

### Adding New Modules

1. Create a new `.lig` file in the appropriate register directory
2. Declare the module with `module ModuleName`
3. Define types and functions
4. Export items with `export { item1, item2 }`

### Testing Registers

Registers should include comprehensive tests. Test files should be placed in a `tests/` directory within each register:

```
registers/stdlib/
├── core/
│   ├── mod.lig
│   └── tests/
│       └── core_test.lig
```

## Future Plans

- **Config Register**: Environment variable handling, file system operations
- **Crypto Register**: Hashing functions, encoding utilities
- **Network Register**: HTTP client utilities, API helpers
- **Database Register**: Database connection and query utilities

## Contributing

When contributing to registers:

1. Follow the established module structure
2. Include comprehensive type annotations
3. Add tests for all functions
4. Update the register manifest if adding new modules
5. Document all exported items

## License

All registers in this directory are licensed under the Apache License, Version 2.0 unless otherwise specified in their individual `register.toml` files.
