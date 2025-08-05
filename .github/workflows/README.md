# GitHub Actions Workflows

This directory contains GitHub Actions workflows for the Ligature project.

## Cargo LLVM Coverage Caching Strategy

### Problem

The `cargo-llvm-cov` tool was being installed fresh in each CI job, which significantly slowed down the coverage workflow. This was especially problematic because:

1. `cargo-llvm-cov` installation takes time and bandwidth
2. The tool was being reinstalled even when dependencies hadn't changed
3. Other CI jobs couldn't benefit from the installation cache

### Solution: Isolated Caching

We've implemented an isolated caching strategy for `cargo-llvm-cov` that:

1. **Separates tool installation from build artifacts**: Uses a dedicated cache key for `cargo-llvm-cov` installation
2. **Enables cache sharing**: Multiple jobs can share the same cached installation
3. **Maintains build independence**: Regular Cargo caches remain separate and can be reused by other pipeline steps

### Implementation

#### Cache Key Strategy

```yaml
# Isolated cache for cargo-llvm-cov installation
key: ${{ runner.os }}-cargo-llvm-cov-${{ hashFiles('**/Cargo.lock') }}

# Separate cache for build dependencies
key: ${{ runner.os }}-cargo-coverage-${{ hashFiles('**/Cargo.lock') }}
```

#### Usage Pattern

```yaml
- name: Cache cargo-llvm-cov installation
  id: cache-cargo-llvm-cov
  uses: actions/cache@v3
  with:
    path: ~/.cargo/bin/cargo-llvm-cov
    key: ${{ runner.os }}-cargo-llvm-cov-${{ hashFiles('**/Cargo.lock') }}
    restore-keys: |
      ${{ runner.os }}-cargo-llvm-cov-

- name: Install cargo-llvm-cov
  if: steps.cache-cargo-llvm-cov.outputs.cache-hit != 'true'
  run: cargo install cargo-llvm-cov
```

### Benefits

1. **Faster CI**: `cargo-llvm-cov` installation is cached and reused across jobs
2. **Reduced bandwidth**: Tool is downloaded only when `Cargo.lock` changes
3. **Independent caching**: Build artifacts can be cached separately and reused by other workflows
4. **Maintainable**: Clear separation of concerns between tool installation and build caching

### Files

- `coverage.yml`: Main coverage workflow with isolated caching
- `coverage-optimized.yml`: Alternative workflow demonstrating reusable setup (for reference)
- `cargo-llvm-cov-setup.yml`: Reusable workflow for cargo-llvm-cov setup (for reference)

### Cache Keys Used

| Purpose            | Cache Key Pattern                         | Description                              |
| ------------------ | ----------------------------------------- | ---------------------------------------- |
| Tool Installation  | `{os}-cargo-llvm-cov-{cargo.lock-hash}`   | Isolated cache for cargo-llvm-cov binary |
| Build Dependencies | `{os}-cargo-{job-type}-{cargo.lock-hash}` | Regular Cargo cache for each job type    |
| Registry           | `{os}-cargo-{job-type}-{cargo.lock-hash}` | Cargo registry cache (shared with build) |

### Migration Guide

To add isolated caching to other workflows that use `cargo-llvm-cov`:

1. Add the cache step before the installation step
2. Use a unique cache key suffix for the job type
3. Condition the installation on cache miss
4. Keep the regular Cargo cache separate

Example:

```yaml
- name: Cache cargo-llvm-cov installation
  id: cache-cargo-llvm-cov
  uses: actions/cache@v3
  with:
    path: ~/.cargo/bin/cargo-llvm-cov
    key: ${{ runner.os }}-cargo-llvm-cov-{job-name}-${{ hashFiles('**/Cargo.lock') }}
    restore-keys: |
      ${{ runner.os }}-cargo-llvm-cov-{job-name}-
      ${{ runner.os }}-cargo-llvm-cov-

- name: Install cargo-llvm-cov
  if: steps.cache-cargo-llvm-cov.outputs.cache-hit != 'true'
  run: cargo install cargo-llvm-cov
```
