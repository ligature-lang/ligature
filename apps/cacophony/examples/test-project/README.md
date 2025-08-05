# test-project

A Cacophony-managed project for orchestrating Ligature programs.

## Quick Start

1. List available resources:
   ```bash
   cacophony list
   ```

2. Validate your configuration:
   ```bash
   cacophony validate
   ```

3. Deploy a collection:
   ```bash
   cacophony deploy --collection app --environment dev
   ```

## Project Structure

- `cacophony.lig` - Main configuration file
- `environments/` - Environment-specific configurations
- `collections/` - Collection definitions
- `scripts/` - Custom operation scripts
- `plugins/` - Custom plugins (optional)

## Configuration

Edit `cacophony.lig` to configure your project's:
- Project metadata
- Environments and variables
- Collections and dependencies
- Custom operations

## Documentation

For more information, see the [Cacophony documentation](https://github.com/fugue-ai/ligature).
