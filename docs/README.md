# Ligature Documentation

This directory contains the Ligature documentation site built with Next.js and Nextra.

## Nx Targets

This project is integrated with Nx and provides the following targets:

### Development
- `nx run docs:dev` - Start development server
- `nx run docs:start` - Start production server (requires build first)
- `nx run docs:preview` - Preview production build

### Building
- `nx run docs:build` - Build for production ✅ **WORKING**
- `nx run docs:build:static` - Build static export
- `nx run docs:export` - Export static files
- `nx run docs:analyze` - Analyze bundle size

### Code Quality
- `nx run docs:lint` - Run ESLint ✅ **WORKING**
- `nx run docs:lint:fix` - Fix ESLint issues
- `nx run docs:format` - Format code with Prettier
- `nx run docs:format:check` - Check code formatting
- `nx run docs:type-check` - Run TypeScript type checking ✅ **WORKING**

### Testing
- `nx run docs:test` - Run tests
- `nx run docs:test:watch` - Run tests in watch mode
- `nx run docs:test:coverage` - Run tests with coverage

### Validation & Checks
- `nx run docs:validate` - Run lint, type-check, and format check
- `nx run docs:check` - Run all checks including tests

### Maintenance
- `nx run docs:install` - Install dependencies
- `nx run docs:clean` - Clean build artifacts
- `nx run docs:clean:all` - Clean all artifacts including node_modules

## Quick Start

1. Install dependencies:
   ```bash
   nx run docs:install
   ```

2. Start development server:
   ```bash
   nx run docs:dev
   ```

3. Build for production:
   ```bash
   nx run docs:build
   ```

## File Structure

- `content/` - Documentation content (MDX files)
- `src/` - Source code and components
- `pages/` - Next.js pages directory (Nextra 3.x)
- `public/` - Static assets

## Configuration Files

- `next.config.mjs` - Next.js and Nextra configuration ✅ **WORKING**
- `theme.config.jsx` - Nextra theme configuration
- `tsconfig.json` - TypeScript configuration
- `.eslintrc.json` - ESLint configuration
- `.prettierrc` - Prettier configuration
- `jest.config.js` - Jest configuration
- `project.json` - Nx project configuration

## Dependencies

This project uses:
- Next.js 15.4.6
- Nextra 3.3.1 (stable version)
- React 19.1.1
- TypeScript 5.9.2
- ESLint 8.57.1
- Prettier 3.6.2
- Jest 29.7.0

## Recent Fixes

- ✅ Fixed Nextra configuration issues by downgrading to stable 3.x version
- ✅ Resolved App Router vs Pages Router compatibility
- ✅ Fixed MDX components integration
- ✅ Successfully configured Nx targets for all operations
- ✅ All core targets (build, lint, type-check) are working 