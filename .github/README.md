# GitHub Actions Configuration

This directory contains GitHub Actions workflows and configuration for the Ligature project.

## Shared Crate Configuration

The project uses a centralized configuration system for managing crate lists across different workflows.

### Configuration File

The main configuration is stored in `.github/crates.config.yml`:

```yaml
# All crates that should be built and tested in CI
crates:
  - cacophony
  - ligature-ast
  - ligature-lsp
  - ligature-parser
  - ligature-types
  - ligature-eval
  - keywork
  - krox
  - reed

# Crates that should be published to crates.io
publish_crates:
  - cacophony
  - ligature-ast
  - ligature-lsp
  - ligature-parser
  - ligature-types
  - ligature-eval
  - keywork
  - krox
  - reed

# Crates that should be included in coverage reporting
coverage_crates:
  - cacophony
  - ligature-ast
  - ligature-lsp
  - ligature-parser
  - ligature-types
  - ligature-eval
  - keywork
  - reed
```

### Shared Workflow

The `.github/workflows/shared-crates.yml` workflow provides a reusable way to load this configuration:

```yaml
jobs:
  load-crates:
    name: Load Crate Configuration
    uses: ./.github/workflows/shared-crates.yml
```

This workflow outputs:

- `crates`: List of all crates for CI builds
- `publish-crates`: List of crates to publish to crates.io
- `coverage-crates`: List of crates for coverage reporting

### Using the Configuration

In any workflow that needs the crate list, you can:

1. Call the shared workflow:

```yaml
jobs:
  load-crates:
    uses: ./.github/workflows/shared-crates.yml
```

2. Use the outputs in matrix strategies:

```yaml
jobs:
  build:
    needs: [load-crates]
    strategy:
      matrix:
        crate: ${{ fromJSON(needs.load-crates.outputs.crates) }}
```

### Benefits

- **Single source of truth**: All crate lists are defined in one place
- **Easy maintenance**: Adding/removing crates only requires updating the config file
- **Consistency**: All workflows use the same crate lists
- **Flexibility**: Different workflows can use different crate lists (e.g., coverage excludes problematic crates)

### Testing

You can test the configuration by running the `.github/workflows/test-crates-config.yml` workflow manually. This will validate the YAML syntax and display the parsed configuration.

## Workflows

- `ci.yml`: Continuous integration with build verification
- `release.yml`: Release process including publishing to crates.io
- `coverage.yml`: Test coverage reporting
- `status-badge.yml`: Status badge generation
- `shared-crates.yml`: Shared configuration loader (reusable)
- `test-crates-config.yml`: Configuration testing (manual trigger)
