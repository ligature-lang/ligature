# Release Process

This document describes the automated release process for the Ligature project.

## Overview

The release process is fully automated using GitHub Actions. When a version tag is pushed, the workflow will:

1. **Validate** the release (version format, tests, etc.)
2. **Publish** all crates to crates.io
3. **Create** a GitHub release with changelog
4. **Notify** completion

## Prerequisites

### 1. Cargo Registry Token

You need a crates.io API token to publish packages:

1. Go to [crates.io/settings/tokens](https://crates.io/settings/tokens)
2. Create a new token with publish permissions
3. Add it to your GitHub repository secrets as `CARGO_REGISTRY_TOKEN`

### 2. GitHub Token

The workflow uses `GITHUB_TOKEN` (automatically provided) for creating releases.

## Release Workflow

### Step 1: Prepare the Release

Use the release preparation script:

```bash
# Bump patch version (0.1.0 -> 0.1.1)
./.github/scripts/prepare-release.sh --patch

# Bump minor version (0.1.0 -> 0.2.0)
./.github/scripts/prepare-release.sh --minor

# Bump major version (0.1.0 -> 1.0.0)
./.github/scripts/prepare-release.sh --major

# Set specific version
./.github/scripts/prepare-release.sh 0.2.0

# Dry run to see what would happen
./.github/scripts/prepare-release.sh --dry-run --patch
```

The script will:
- Validate the working directory is clean
- Calculate the new version
- Update `Cargo.toml`
- Create a git commit and tag
- Optionally push to remote

### Step 2: Trigger the Release

Push the tag to trigger the automated release:

```bash
git push origin v0.1.0
```

### Step 3: Monitor the Release

Monitor the release workflow at:
https://github.com/ligature-lang/ligature/actions

## Workflow Jobs

### 1. Pre-release Checks
- **Code formatting** with `rustfmt`
- **Linting** with `clippy`
- **All tests** (unit, integration, property, differential)
- **Build verification** (debug and release)
- **Documentation** checks

### 2. Version Validation
- **Format validation** (semantic versioning)
- **Cargo.toml consistency** check
- **Tag uniqueness** verification

### 3. Changelog Generation
- **Automatic changelog** from git commits
- **Filtered commits** (excludes merge commits)
- **Formatted output** for GitHub release

### 4. Crate Publishing
Publishes all crates in parallel:
- `ligature-ast`
- `ligature-parser`
- `ligature-types`
- `ligature-eval`
- `ligature-cli`
- `ligature-lsp`
- `krox`
- `keywork`

### 5. GitHub Release
- **Creates release** with generated changelog
- **Includes installation** instructions
- **Links to documentation**

## Version Management

### Semantic Versioning

The project follows [Semantic Versioning](https://semver.org/):

- **MAJOR** version for incompatible API changes
- **MINOR** version for backwards-compatible functionality
- **PATCH** version for backwards-compatible bug fixes

### Version Format

Versions must follow the format: `vX.Y.Z[-prerelease][+build]`

Examples:
- `v0.1.0` - Standard release
- `v0.1.0-alpha.1` - Prerelease
- `v0.1.0+20231219` - Build metadata

### Workspace Version

All crates in the workspace share the same version defined in the root `Cargo.toml`:

```toml
[workspace.package]
version = "0.1.0"
```

## Release Checklist

Before creating a release, ensure:

- [ ] All tests pass locally
- [ ] Code is formatted (`cargo fmt`)
- [ ] No clippy warnings (`cargo clippy`)
- [ ] Documentation is up to date
- [ ] Changelog is meaningful
- [ ] Version is appropriate (semantic versioning)
- [ ] Working directory is clean

## Troubleshooting

### Common Issues

#### 1. Version Already Exists
```
Error: Version v0.1.0 already exists as a tag
```
**Solution**: Use a different version or delete the existing tag.

#### 2. Working Directory Not Clean
```
Error: Working directory is not clean
```
**Solution**: Commit or stash your changes, or use `--force`.

#### 3. Cargo Registry Token Missing
```
Error: 401 Unauthorized
```
**Solution**: Add `CARGO_REGISTRY_TOKEN` to GitHub secrets.

#### 4. Crate Already Published
```
Error: crate already exists
```
**Solution**: Bump the version before publishing.

### Manual Release

If the automated workflow fails, you can manually publish:

```bash
# Login to crates.io
cargo login

# Publish each crate
cargo publish --package ligature-ast
cargo publish --package ligature-parser
# ... repeat for all crates
```

## Post-Release Tasks

After a successful release:

1. **Update documentation** if needed
2. **Announce the release** to the community
3. **Monitor for issues** in the new version
4. **Plan the next release** cycle

## Security Considerations

- **Token security**: Never commit API tokens to the repository
- **Access control**: Limit who can create tags and push to main
- **Audit trail**: All releases are logged in GitHub Actions
- **Rollback plan**: Keep previous versions available

## Best Practices

1. **Test thoroughly** before releasing
2. **Use semantic versioning** consistently
3. **Write meaningful commit messages** for better changelogs
4. **Review the generated changelog** before publishing
5. **Monitor the release** for any issues
6. **Communicate breaking changes** clearly

## Support

For issues with the release process:

1. Check the [GitHub Actions logs](https://github.com/ligature-lang/ligature/actions)
2. Review this documentation
3. Open an issue in the repository
4. Contact the maintainers 