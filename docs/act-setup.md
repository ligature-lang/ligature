# Local GitHub Actions Testing with Act

This document explains how to use [nektos/act](https://github.com/nektos/act) to test GitHub Actions workflows locally in the Ligature project.

## Prerequisites

1. **Docker**: Make sure Docker Desktop is installed and running
2. **Act**: Install act using Homebrew: `brew install act`

## Quick Start

### 1. Test the CI workflow

```bash
# Test all CI jobs
./scripts/test-workflows.sh ci

# Test a specific job (e.g., code quality checks)
./scripts/test-workflows.sh ci code-quality
```

### 2. Test other workflows

```bash
# Test coverage workflow
./scripts/test-workflows.sh coverage

# Test release workflow
./scripts/test-workflows.sh release
```

## Configuration

The project includes an `.actrc` file with optimized settings for local testing:

- **Platform**: Uses `linux/amd64` for M1/M2 Mac compatibility
- **Images**: Uses `catthehacker/ubuntu:act-latest` for better performance
- **Bind mounts**: Enabled for better performance on macOS
- **Artifacts**: Configured for local artifact handling
- **Container reuse**: Enabled for faster subsequent runs

## Available Workflows

| Workflow               | Description                | Jobs                                                                                                 |
| ---------------------- | -------------------------- | ---------------------------------------------------------------------------------------------------- |
| `ci`                   | Main CI pipeline           | code-quality, unit-tests, integration-tests, build-verification, examples, lsp-tests, docs, security |
| `coverage`             | Code coverage reporting    | coverage-analysis, coverage-report                                                                   |
| `release`              | Release automation         | build-release, publish-crates, create-release                                                        |
| `status-badge`         | Status badge updates       | update-badge                                                                                         |
| `shared-crates`        | Shared crate configuration | load-crates                                                                                          |
| `test-crates-config`   | Test crate configuration   | test-config                                                                                          |
| `cargo-llvm-cov-setup` | LLVM coverage setup        | setup-coverage                                                                                       |

## Manual Act Usage

### Basic Commands

```bash
# List all workflows
act -l

# Run a specific workflow
act workflow_dispatch -W .github/workflows/ci.yml

# Run a specific job
act workflow_dispatch -W .github/workflows/ci.yml -j code-quality

# Run with specific event
act push -W .github/workflows/ci.yml

# Run with pull request event
act pull_request -W .github/workflows/ci.yml
```

### Environment Variables

You can set environment variables for testing:

```bash
# Set GitHub token for authenticated actions
export ACTIONS_STEP_DEBUG=true
export GITHUB_TOKEN=your_token_here

# Run with environment variables
act workflow_dispatch -W .github/workflows/ci.yml --env-file .env
```

## Troubleshooting

### Common Issues

1. **Docker not running**

   ```bash
   open -a Docker
   ```

2. **Permission issues on macOS**

   - Make sure Docker has access to the project directory
   - Check Docker Desktop settings

3. **Slow performance**

   - The `.actrc` file includes optimizations for macOS
   - Consider using `--reuse` flag for faster subsequent runs

4. **Action compatibility**
   - Some GitHub Actions may not work exactly the same locally
   - Check the [act compatibility list](https://github.com/nektos/act#actions)

### Debug Mode

Enable debug output for troubleshooting:

```bash
# Run with verbose output
act -v workflow_dispatch -W .github/workflows/ci.yml

# Run with debug logging
ACTIONS_STEP_DEBUG=true act workflow_dispatch -W .github/workflows/ci.yml
```

## Best Practices

1. **Test individual jobs first**: Start with smaller jobs like `code-quality` before running full workflows
2. **Use the helper script**: The `scripts/test-workflows.sh` script provides a convenient interface
3. **Check Docker resources**: Ensure Docker has enough memory and CPU allocated
4. **Clean up containers**: Use `docker system prune` to clean up unused containers and images

## Integration with Development Workflow

### Pre-commit Testing

Add act testing to your development workflow:

```bash
# Test CI workflow before committing
./scripts/test-workflows.sh ci code-quality

# Test specific jobs that are relevant to your changes
./scripts/test-workflows.sh ci unit-tests
```

### Continuous Testing

Consider setting up a local testing loop:

```bash
# Watch for changes and test automatically
fswatch -o . | xargs -n1 -I{} ./scripts/test-workflows.sh ci code-quality
```

## Advanced Configuration

### Custom Act Configuration

You can override the `.actrc` settings for specific runs:

```bash
# Use a different image
act -P ubuntu-latest=node:18 workflow_dispatch -W .github/workflows/ci.yml

# Disable container reuse
act --no-reuse workflow_dispatch -W .github/workflows/ci.yml

# Use a different platform
act --platform linux/arm64 workflow_dispatch -W .github/workflows/ci.yml
```

### Workflow-specific Testing

Create workflow-specific test scripts:

```bash
# Test only Rust-related jobs
act workflow_dispatch -W .github/workflows/ci.yml -j unit-tests -j integration-tests

# Test only documentation jobs
act workflow_dispatch -W .github/workflows/ci.yml -j docs
```

## Resources

- [Act Documentation](https://nektosact.com/)
- [Act GitHub Repository](https://github.com/nektos/act)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Docker Documentation](https://docs.docker.com/)
