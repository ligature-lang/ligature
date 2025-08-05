# Test Coverage

This document describes the test coverage system for the Ligature project.

## Overview

The coverage system uses `cargo-llvm-cov` to generate comprehensive coverage reports for all crates in the workspace. Coverage is tracked automatically in CI/CD and can be run locally for development.

## Features

- **Automated Coverage**: Runs on every PR and push to main
- **Multiple Formats**: HTML, LCOV, and text reports
- **Coverage Thresholds**: Enforces minimum coverage requirements
- **Codecov Integration**: Uploads coverage to Codecov for tracking
- **Individual Crate Coverage**: Per-crate coverage analysis
- **Coverage Badges**: Dynamic badges showing current coverage

## Prerequisites

### Local Development

1. **Install cargo-llvm-cov**:
   ```bash
   cargo install cargo-llvm-cov
   ```

2. **Install llvm-tools-preview**:
   ```bash
   rustup component add llvm-tools-preview
   ```

### CI/CD Setup

The coverage workflow requires these secrets:

- `CODECOV_TOKEN`: Token for uploading to Codecov
- `GIST_SECRET`: (Optional) For generating coverage badges

## Usage

### Local Coverage Testing

Use the coverage script for local development:

```bash
# Run coverage for all crates
./.github/scripts/coverage.sh

# Run coverage for specific crate
./.github/scripts/coverage.sh -c ligature-parser

# Set custom threshold
./.github/scripts/coverage.sh -t 90

# Generate HTML report only
./.github/scripts/coverage.sh --format html

# Upload to Codecov (requires CODECOV_TOKEN)
./.github/scripts/coverage.sh --upload
```

### Direct cargo-llvm-cov Usage

```bash
# Generate coverage for all crates
cargo llvm-cov --all-features --workspace --html --output-dir coverage-html
cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info
cargo llvm-cov --all-features --workspace --text

# Generate coverage for specific crate
cargo llvm-cov --all-features --package ligature-parser --html --output-dir coverage-parser
cargo llvm-cov --all-features --package ligature-parser --text

# Clean coverage data
cargo llvm-cov clean
```

## Coverage Workflow

### 1. Main Coverage Job

The main coverage job runs on every PR and push:

- **Generates coverage** for all crates
- **Creates multiple formats**: HTML, LCOV, text
- **Uploads to Codecov** for tracking
- **Stores artifacts** for 30 days

### 2. Individual Crate Coverage

Runs coverage analysis for each crate separately:

- **Parallel execution** for faster results
- **Individual artifacts** per crate
- **Detailed reporting** per crate

### 3. Coverage Thresholds

Enforces minimum coverage requirements:

- **Overall threshold**: 80%
- **Per-crate thresholds**: Configurable
- **Fails CI** if thresholds not met

### 4. Coverage Badges

Generates dynamic coverage badges:

- **Updates automatically** on main branch
- **Color-coded** by coverage level
- **Shows current coverage** percentage

## Configuration

### Coverage Thresholds

Default thresholds are set to 80%:

```yaml
# In .github/workflows/coverage.yml
cargo llvm-cov --all-features --workspace --text | grep "Total" | awk '{if ($2 < 80) exit 1}'
```

### Codecov Configuration

The `codecov.yml` file configures:

- **Coverage thresholds**: 80% overall
- **Status checks**: Project, patch, changes
- **File exclusions**: Tests, docs, config files
- **Coverage flags**: Different test types

### Cargo Configuration

The `.cargo/config.toml` file sets:

- **Coverage instrumentation**: RUSTFLAGS
- **Profile settings**: Optimized for coverage
- **Toolchain components**: llvm-tools-preview

## Coverage Reports

### HTML Reports

Interactive HTML reports are generated in:

- **Overall**: `coverage-html/index.html`
- **Per-crate**: `coverage-html-{crate}/index.html`

Features:
- **Line-by-line coverage** highlighting
- **Branch coverage** information
- **Function coverage** summaries
- **Search and filter** capabilities

### LCOV Reports

Machine-readable LCOV format:

- **Overall**: `lcov.info`
- **Per-crate**: `lcov-{crate}.info`

Used for:
- **Codecov uploads**
- **CI/CD integration**
- **Coverage analysis tools**

### Text Reports

Simple text summaries:

- **Overall**: `coverage.txt`
- **Per-crate**: `coverage-{crate}.txt`

Shows:
- **Total coverage** percentage
- **Line coverage** statistics
- **Function coverage** statistics

## Coverage Metrics

### Line Coverage

Measures which lines of code are executed:

- **Covered**: Lines executed during tests
- **Uncovered**: Lines never executed
- **Partially covered**: Lines with conditional execution

### Branch Coverage

Measures conditional execution paths:

- **True/False branches**: Both paths tested
- **Missing branches**: Untested conditions
- **Complex conditions**: Multiple outcomes

### Function Coverage

Measures function execution:

- **Called functions**: Functions executed during tests
- **Uncalled functions**: Functions never executed
- **Partial calls**: Functions called but not fully tested

## Best Practices

### Writing Testable Code

1. **Avoid complex functions**: Break down large functions
2. **Use dependency injection**: Make testing easier
3. **Separate concerns**: Business logic from I/O
4. **Use interfaces**: Mock dependencies in tests

### Improving Coverage

1. **Add missing tests**: Cover uncovered code paths
2. **Test edge cases**: Boundary conditions and errors
3. **Test error handling**: Exception and error paths
4. **Test integration**: End-to-end scenarios

### Coverage Goals

- **Minimum**: 80% overall coverage
- **Target**: 90% overall coverage
- **Critical paths**: 100% coverage
- **New code**: 90% coverage requirement

## Troubleshooting

### Common Issues

#### 1. Coverage Not Generated

```bash
# Check if cargo-llvm-cov is installed
cargo install cargo-llvm-cov

# Check if llvm-tools-preview is installed
rustup component add llvm-tools-preview
```

#### 2. Low Coverage

```bash
# Identify uncovered code
cargo llvm-cov --all-features --workspace --html --output-dir coverage-html

# Open HTML report to see uncovered lines
open coverage-html/index.html
```

#### 3. Coverage Threshold Failures

```bash
# Check current coverage
cargo llvm-cov --all-features --workspace --text

# Add tests for uncovered code
# Focus on critical paths first
```

#### 4. Codecov Upload Failures

```bash
# Check CODECOV_TOKEN is set
echo $CODECOV_TOKEN

# Test upload manually
codecov -f lcov.info -t $CODECOV_TOKEN
```

### Performance Optimization

1. **Use caching**: Coverage data is cached between runs
2. **Parallel execution**: Individual crates run in parallel
3. **Incremental builds**: Only rebuild changed code
4. **Selective coverage**: Test specific crates when needed

## Integration

### GitHub Actions

Coverage runs automatically on:

- **Pull requests**: Coverage check and reporting
- **Main branch**: Coverage tracking and badges
- **Manual trigger**: On-demand coverage analysis

### Codecov Integration

Features available:

- **Coverage tracking**: Historical coverage trends
- **PR comments**: Coverage changes in PRs
- **Coverage badges**: Dynamic badges
- **Coverage reports**: Detailed analysis

### IDE Integration

Many IDEs support coverage:

- **VS Code**: Coverage highlighting
- **IntelliJ**: Coverage visualization
- **Vim/Emacs**: Coverage plugins

## Monitoring

### Coverage Trends

Monitor coverage over time:

- **Codecov dashboard**: Historical trends
- **Coverage reports**: Detailed analysis
- **Coverage alerts**: Threshold violations

### Quality Gates

Enforce coverage requirements:

- **PR blocking**: Fail CI on low coverage
- **Coverage thresholds**: Minimum requirements
- **Coverage goals**: Target improvements

## Support

For coverage-related issues:

1. **Check documentation**: This file and Codecov docs
2. **Review logs**: GitHub Actions coverage logs
3. **Test locally**: Use coverage script
4. **Open issue**: Report problems in repository 