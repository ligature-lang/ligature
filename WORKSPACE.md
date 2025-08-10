# Ligature Workspace

This is a PNPM workspace that contains multiple packages for the Ligature language project.

## Structure

- `docs/` - Documentation site built with Next.js and Nextra
- `apps/` - Application packages
- `crates/` - Rust crates
- `engines/` - Language engines
- `krox/` - Additional tools
- `examples/` - Example projects

## Getting Started

### Prerequisites

- Node.js (v18 or higher)
- PNPM (v10.14.0 or higher)

### Installation

```bash
# Install PNPM globally if not already installed
npm install -g pnpm

# Install all workspace dependencies
pnpm install
```

## Available Scripts

### Workspace Commands

- `pnpm install:all` - Install dependencies for all packages
- `pnpm build` - Build all packages
- `pnpm dev` - Start development servers for all packages
- `pnpm lint` - Lint all packages
- `pnpm test` - Run tests for all packages
- `pnpm clean` - Clean build artifacts for all packages

### Documentation Commands

- `pnpm docs:dev` - Start the documentation development server
- `pnpm docs:build` - Build the documentation site
- `pnpm docs:start` - Start the production documentation server
- `pnpm docs:lint` - Lint the documentation code
- `pnpm docs:type-check` - Run TypeScript type checking
- `pnpm docs:format` - Format the documentation code
- `pnpm docs:test` - Run documentation tests

## Development

### Working with Documentation

The documentation site is located in the `docs/` directory and uses:
- Next.js 15.4.6
- Nextra 4.3.0 for documentation
- MDX for content
- TypeScript for type safety

To start developing the documentation:

```bash
pnpm docs:dev
```

The site will be available at `http://localhost:3000`.

### Adding New Packages

To add a new package to the workspace:

1. Create a new directory in the appropriate location (e.g., `apps/`, `crates/`, etc.)
2. Add a `package.json` file to the new directory
3. Update `pnpm-workspace.yaml` if needed to include the new package
4. Run `pnpm install` to install dependencies

### Package Management

- Use `pnpm add <package>` in a specific package directory to add dependencies
- Use `pnpm add -w <package>` to add workspace-level dependencies
- Use `pnpm add --filter <package-name> <dependency>` to add dependencies to a specific package

## Migration from MD to MDX

All documentation files have been migrated from `.md` to `.mdx` format to enable:
- React components in documentation
- Enhanced interactivity
- Better integration with Next.js

The migration was completed using the `docs/migrate-to-mdx.sh` script.

## Troubleshooting

### Multiple Lockfiles Warning

If you see warnings about multiple lockfiles, ensure you're using PNPM consistently:
- Remove any `package-lock.json` files
- Use only `pnpm-lock.yaml` for dependency locking

### Build Issues

If you encounter build issues:
1. Clean all build artifacts: `pnpm clean`
2. Reinstall dependencies: `pnpm install`
3. Try building individual packages: `pnpm --filter <package-name> build`
