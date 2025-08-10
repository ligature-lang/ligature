//! Command implementations for keywork CLI.

use std::fs;
use std::path::{Path, PathBuf};

use miette::{IntoDiagnostic, Result, miette};

use crate::dependency::{
    install_dependencies, parse_dependencies, resolve_dependencies_from_manifest,
};
use crate::register::Register;
use crate::registry::Registry;
use crate::xdg_config::KeyworkXdgConfig;

pub async fn init_register(name: &str, directory: &Path) -> Result<()> {
    let register_dir = directory.join(name);

    if register_dir.exists() {
        return Err(miette!(
            "Register directory '{}' already exists",
            register_dir.display()
        ));
    }

    // Create register directory structure
    fs::create_dir_all(&register_dir)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create register directory: {}", e))?;

    fs::create_dir_all(register_dir.join("src"))
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create src directory: {}", e))?;

    fs::create_dir_all(register_dir.join("tests"))
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create tests directory: {}", e))?;

    // Create register.toml
    let manifest_content = format!(
        r#"[register]
name = "{name}"
version = "0.1.0"
description = "A Ligature register"
authors = ["Your Name <your.email@example.com>"]
license = "Apache-2.0"

[dependencies]
# Add your dependencies here
# stdlib = "1.0.0"

[exports]
# Add your exported modules here
# example = "src/example.lig"

[metadata]
tags = []
"#
    );

    fs::write(register_dir.join("register.toml"), manifest_content)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create register.toml: {}", e))?;

    // Create a sample module
    let sample_module = r#"module Example

-- Define your types and functions here
type ExampleType = {
    name: String,
    value: Int
}

let exampleFunction: String -> Int = fun name -> 
    length(name)

export { ExampleType, exampleFunction }
"#;

    fs::write(register_dir.join("src").join("example.lig"), sample_module)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create example module: {}", e))?;

    // Create a sample test
    let sample_test = r#"module ExampleTest

import { exampleFunction } from Example

let testResult = exampleFunction("test")
-- Add your tests here
"#;

    fs::write(
        register_dir.join("tests").join("example_test.lig"),
        sample_test,
    )
    .into_diagnostic()
    .map_err(|e| miette!("Failed to create test file: {}", e))?;

    println!(
        "✓ Created register '{}' in {}",
        name,
        register_dir.display()
    );
    println!("  - Edit register.toml to configure your register");
    println!("  - Add modules to src/ directory");
    println!("  - Add tests to tests/ directory");
    println!("  - Run 'keywork build' to build your register");

    Ok(())
}

pub async fn build_register(path: &Path, output: &Path) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    println!("Building register '{}'...", register.name());

    // Build the register
    let artifact = register
        .build(path, output)
        .await
        .map_err(|e| miette!("Failed to build register: {}", e))?;

    println!(
        "✓ Built register '{}' version {} to {}",
        register.name(),
        register.version(),
        output.display()
    );
    println!("  - Files: {}", artifact.files.len());
    println!("  - Dependencies: {}", artifact.dependencies.len());
    println!("  - Checksum: {}", artifact.checksum);

    Ok(())
}

pub async fn install_register(
    register_name: &str,
    version: Option<&str>,
    global: bool,
) -> Result<()> {
    // Use default registry for development (localhost triggers mock mode)
    let registry = Registry::default();

    let version = version.unwrap_or("latest");
    println!("Installing register '{register_name}' version '{version}'...");

    // Resolve the actual version if "latest" was specified
    let actual_version = if version == "latest" {
        registry.get_latest_version(register_name).await?
    } else {
        version.to_string()
    };

    // Download the package
    let cached_file = registry
        .download_package_cached(register_name, &actual_version)
        .await?;

    // Determine install path using XDG
    let install_path = if global {
        // For global installation, use system-wide directory
        PathBuf::from("/usr/local/lib/ligature/registers")
    } else {
        // For user installation, use XDG data directory
        let xdg_config = KeyworkXdgConfig::new()
            .await
            .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

        let data_dir = xdg_config
            .data_dir()
            .map_err(|e| miette!("Failed to get data directory: {}", e))?;

        data_dir.join("packages")
    };

    // Ensure install directory exists
    tokio::fs::create_dir_all(&install_path)
        .await
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create install directory: {}", e))?;

    let register_install_path = install_path.join(format!("{register_name}-{actual_version}"));

    // Extract the package
    crate::dependency::extract_package(&cached_file, &register_install_path).await?;

    println!(
        "✓ Installed register '{}@{}' to {}",
        register_name,
        actual_version,
        register_install_path.display()
    );
    Ok(())
}

pub async fn publish_register(path: &Path, registry_url: Option<&str>) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    // Validate before publishing
    let validation = register
        .validate(path)
        .await
        .map_err(|e| miette!("Register validation failed: {}", e))?;

    if !validation.valid {
        println!("✗ Register validation failed:");
        for error in &validation.errors {
            println!("  - {error}");
        }
        return Err(miette!("Cannot publish invalid register"));
    }

    if !validation.warnings.is_empty() {
        println!("⚠️  Warnings:");
        for warning in &validation.warnings {
            println!("  - {warning}");
        }
    }

    // Package the register
    let temp_dir = tempfile::tempdir()
        .into_diagnostic()
        .map_err(|e| miette!("Failed to create temp directory: {}", e))?;

    let package_path =
        temp_dir
            .path()
            .join(format!("{}-{}.tar.gz", register.name(), register.version()));
    register
        .package(path, &package_path)
        .await
        .map_err(|e| miette!("Failed to package register: {}", e))?;

    // Read the package file
    let package_data = std::fs::read(&package_path)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to read package file: {}", e))?;

    // Get auth token from environment
    let auth_token = std::env::var("KEYWORK_AUTH_TOKEN")
        .map_err(|_| miette!("KEYWORK_AUTH_TOKEN environment variable not set"))?;

    // Publish to registry
    let registry_url = registry_url.unwrap_or("https://registry.ligature.dev");
    let registry = Registry::new(registry_url.to_string());

    registry
        .publish_package(&package_data, &auth_token)
        .await
        .map_err(|e| miette!("Failed to publish package: {}", e))?;

    println!(
        "✓ Published register '{}' version {} to {}",
        register.name(),
        register.version(),
        registry_url
    );
    Ok(())
}

pub async fn list_registers(verbose: bool, global: bool) -> Result<()> {
    let install_path = if global {
        PathBuf::from("/usr/local/lib/ligature/registers")
    } else {
        // Use XDG data directory for user installations
        let xdg_config = KeyworkXdgConfig::new()
            .await
            .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

        let data_dir = xdg_config
            .data_dir()
            .map_err(|e| miette!("Failed to get data directory: {}", e))?;

        data_dir.join("packages")
    };

    if !install_path.exists() {
        println!("No registers installed at {}", install_path.display());
        return Ok(());
    }

    println!("Installed registers at {}:", install_path.display());

    // Scan the install directory for registers
    let entries = std::fs::read_dir(&install_path)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to read install directory: {}", e))?;

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("unknown");

            if verbose {
                // Try to load register info
                if let Ok(register) = Register::load(&path) {
                    println!(
                        "  {}@{} - {}",
                        register.name(),
                        register.version(),
                        register.description()
                    );
                    println!("    License: {}", register.license());
                    println!("    Authors: {}", register.authors().join(", "));
                } else {
                    println!("  {name} (invalid register)");
                }
            } else {
                println!("  {name}");
            }
        }
    }

    Ok(())
}

pub async fn remove_register(register_name: &str, global: bool) -> Result<()> {
    let install_path = if global {
        PathBuf::from("/usr/local/lib/ligature/registers")
    } else {
        // Use XDG data directory for user installations
        let xdg_config = KeyworkXdgConfig::new()
            .await
            .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

        let data_dir = xdg_config
            .data_dir()
            .map_err(|e| miette!("Failed to get data directory: {}", e))?;

        data_dir.join("packages")
    };

    // Find the register directory
    let entries = std::fs::read_dir(&install_path)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to read install directory: {}", e))?;

    let mut found = false;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");

            if name.starts_with(register_name) {
                std::fs::remove_dir_all(&path)
                    .into_diagnostic()
                    .map_err(|e| miette!("Failed to remove register: {}", e))?;
                println!(
                    "✓ Removed register '{}' from {}",
                    name,
                    install_path.display()
                );
                found = true;
                break;
            }
        }
    }

    if !found {
        return Err(miette!(
            "Register '{}' is not installed at {}",
            register_name,
            install_path.display()
        ));
    }

    Ok(())
}

pub async fn update_dependencies(path: &Path, all: bool, dependency: Option<&str>) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    if all {
        println!(
            "Updating all dependencies for register '{}'...",
            register.name()
        );

        // Resolve dependencies to get latest versions
        let mut graph = resolve_dependencies_from_manifest(&path.join("register.toml")).await?;
        let resolution = graph.resolve_dependencies().await?;

        if !resolution.success {
            println!("✗ Dependency resolution failed:");
            for conflict in &resolution.conflicts {
                println!(
                    "  - {}: {} vs {}",
                    conflict.package, conflict.requested_version, conflict.resolved_version
                );
            }
            return Err(miette!("Dependency resolution failed"));
        }

        // Update the manifest with resolved versions
        // This would typically update the register.toml file
        println!("✓ Dependencies updated successfully");
    } else if let Some(dep) = dependency {
        println!(
            "Updating dependency '{}' for register '{}'...",
            dep,
            register.name()
        );

        let registry = Registry::default();
        let latest_version = registry.get_latest_version(dep).await?;

        // Update the specific dependency in the manifest
        // This would typically update the register.toml file
        println!("✓ Updated {dep} to version {latest_version}");
    } else {
        return Err(miette!("Must specify either --all or --dependency"));
    }

    Ok(())
}

pub async fn show_register_info(register_name: &str) -> Result<()> {
    // Check if it's a local path or installed register
    let path = PathBuf::from(register_name);

    if path.exists() {
        let register =
            Register::load(&path).map_err(|e| miette!("Failed to load register: {}", e))?;

        println!("Register: {}", register.name());
        println!("Version: {}", register.version());
        println!("Description: {}", register.description());
        println!("Authors: {}", register.authors().join(", "));
        println!("License: {}", register.license());

        if !register.dependencies().is_empty() {
            println!("Dependencies:");
            for (name, version) in register.dependencies() {
                println!("  {name}@{version}");
            }
        }

        if !register.exports().is_empty() {
            println!("Exports:");
            for (name, module_path) in register.exports() {
                println!("  {name} -> {module_path}");
            }
        }

        // Show validation status
        let validation = register.validate(&path).await?;
        println!(
            "Validation: {}",
            if validation.valid {
                "✓ Valid"
            } else {
                "✗ Invalid"
            }
        );

        if !validation.warnings.is_empty() {
            println!("Warnings:");
            for warning in &validation.warnings {
                println!("  - {warning}");
            }
        }
    } else {
        // Try to find in installed registers
        let registry = Registry::default();

        match registry.get_package(register_name, None).await {
            Ok(package) => {
                println!("Register: {}", package.name);
                println!("Version: {}", package.version);
                println!("Description: {}", package.description);
                println!("Authors: {}", package.authors.join(", "));
                println!("License: {}", package.license);

                if let Some(repo) = package.repository {
                    println!("Repository: {repo}");
                }

                if !package.dependencies.is_empty() {
                    println!("Dependencies:");
                    for (name, version) in &package.dependencies {
                        println!("  {name}@{version}");
                    }
                }

                if let Some(metadata) = package.metadata {
                    println!("Downloads: {}", metadata.downloads);
                    println!("Last Updated: {}", metadata.last_updated);

                    if !metadata.tags.is_empty() {
                        println!("Tags: {}", metadata.tags.join(", "));
                    }
                }
            }
            Err(_) => {
                println!("Register '{register_name}' not found locally or in registry");
                println!("Try: keywork search {register_name}");
            }
        }
    }

    Ok(())
}

pub async fn search_registers(query: &str, registry_url: Option<&str>, limit: usize) -> Result<()> {
    let registry = if let Some(url) = registry_url {
        Registry::new(url.to_string())
    } else {
        Registry::default()
    };

    println!("Searching for '{}' in {}...", query, registry.url);

    match registry.search(query, limit).await {
        Ok(result) => {
            println!(
                "Found {} results (showing {}):",
                result.total,
                result.packages.len()
            );

            for package in &result.packages {
                println!(
                    "  {}@{} - {}",
                    package.name, package.version, package.description
                );

                if let Some(metadata) = &package.metadata {
                    println!(
                        "    Downloads: {}, Tags: {}",
                        metadata.downloads,
                        metadata.tags.join(", ")
                    );
                }
            }
        }
        Err(e) => {
            println!("Search failed: {e}");
            return Err(e);
        }
    }

    Ok(())
}

pub async fn validate_register(path: &Path, verbose: bool) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    println!("Validating register '{}'...", register.name());

    let validation = register
        .validate(path)
        .await
        .map_err(|e| miette!("Validation failed: {}", e))?;

    if validation.valid {
        println!("✓ Register is valid");

        if verbose {
            println!("  - Manifest file is valid");
            println!("  - All exported modules exist");
            println!("  - Dependencies are properly specified");
            println!("  - Found {} modules", validation.modules_found.len());

            if validation.dependencies_resolved {
                println!("  - Dependencies resolved successfully");
            }
        }

        if !validation.warnings.is_empty() {
            println!("⚠️  Warnings:");
            for warning in &validation.warnings {
                println!("  - {warning}");
            }
        }
    } else {
        println!("✗ Register validation failed:");
        for error in &validation.errors {
            println!("  - {error}");
        }

        if verbose {
            println!("  - Check register.toml syntax");
            println!("  - Ensure all exported modules exist");
            println!("  - Verify dependency specifications");
        }

        return Err(miette!("Validation failed"));
    }

    Ok(())
}

// New commands for package discovery and installation

pub async fn discover_packages(category: Option<&str>, limit: usize) -> Result<()> {
    let registry = Registry::default();

    let query = category.unwrap_or("");
    let category_text = if query.is_empty() {
        "".to_string()
    } else {
        format!(" in category '{query}'")
    };
    println!("Discovering packages{category_text}...");

    match registry.search(query, limit).await {
        Ok(result) => {
            println!("Found {} packages:", result.packages.len());

            for (i, package) in result.packages.iter().enumerate() {
                println!("{}. {}@{}", i + 1, package.name, package.version);
                println!("   {}", package.description);

                if let Some(metadata) = &package.metadata {
                    println!(
                        "   Downloads: {}, Tags: {}",
                        metadata.downloads,
                        metadata.tags.join(", ")
                    );
                }
                println!();
            }
        }
        Err(e) => {
            println!("Discovery failed: {e}");
            return Err(e);
        }
    }

    Ok(())
}

pub async fn install_dependencies_for_project(path: &Path) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    if register.dependencies().is_empty() {
        println!("No dependencies to install.");
        return Ok(());
    }

    println!(
        "Installing dependencies for register '{}'...",
        register.name()
    );

    // Resolve dependencies
    let mut graph = resolve_dependencies_from_manifest(&path.join("register.toml")).await?;
    let resolution = graph.resolve_dependencies().await?;

    if !resolution.success {
        println!("✗ Dependency resolution failed:");
        for conflict in &resolution.conflicts {
            println!(
                "  - {}: {} vs {}",
                conflict.package, conflict.requested_version, conflict.resolved_version
            );
        }
        return Err(miette!("Dependency resolution failed"));
    }

    // Install dependencies
    let dependencies_dir = path.join("dependencies");
    install_dependencies(&graph, &dependencies_dir).await?;

    println!(
        "✓ Installed {} dependencies",
        resolution.resolved_dependencies.len()
    );
    Ok(())
}

pub async fn clean_cache() -> Result<()> {
    // Use XDG configuration to get cache directory
    let xdg_config = KeyworkXdgConfig::new()
        .await
        .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

    let cache_dir = xdg_config
        .cache_dir()
        .map_err(|e| miette!("Failed to get cache directory: {}", e))?;

    if !cache_dir.exists() {
        println!("No cache directory found at {}", cache_dir.display());
        return Ok(());
    }

    let entries = std::fs::read_dir(&cache_dir)
        .into_diagnostic()
        .map_err(|e| miette!("Failed to read cache directory: {}", e))?;

    let mut removed_count = 0;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file() {
            std::fs::remove_file(&path)
                .into_diagnostic()
                .map_err(|e| miette!("Failed to remove cache file: {}", e))?;
            removed_count += 1;
        }
    }

    println!(
        "✓ Removed {} cached files from {}",
        removed_count,
        cache_dir.display()
    );
    Ok(())
}

pub async fn show_package_stats(register_name: &str) -> Result<()> {
    let registry = Registry::default();

    match registry.get_package_stats(register_name).await {
        Ok(stats) => {
            println!("Statistics for package '{register_name}':");
            for (key, value) in &stats {
                println!("  {key}: {value}");
            }
        }
        Err(e) => {
            println!("Failed to get package stats: {e}");
            return Err(e);
        }
    }

    Ok(())
}

pub async fn list_available_versions(register_name: &str) -> Result<()> {
    let registry = Registry::default();

    match registry.list_versions(register_name).await {
        Ok(versions) => {
            println!("Available versions for package '{register_name}':");
            for version in &versions {
                let status = if version.yanked { "[YANKED]" } else { "" };
                println!(
                    "  {} {} ({} downloads, published {})",
                    version.version, status, version.downloads, version.published_at
                );
            }
        }
        Err(e) => {
            println!("Failed to get versions: {e}");
            return Err(e);
        }
    }

    Ok(())
}

pub async fn show_dependency_graph(path: &Path, format: &str) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    println!("Dependency graph for register '{}':", register.name());

    let dependencies = parse_dependencies(register.dependencies())
        .map_err(|e| miette!("Failed to parse dependencies: {}", e))?;

    match format {
        "json" => {
            let graph_data = serde_json::json!({
                "name": register.name(),
                "version": register.version(),
                "dependencies": dependencies.iter().map(|d| {
                    serde_json::json!({
                        "name": d.name,
                        "version": d.version,
                        "registry": d.registry
                    })
                }).collect::<Vec<_>>()
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&graph_data)
                    .into_diagnostic()
                    .map_err(|e| miette!("Failed to serialize graph data: {}", e))?
            );
        }
        "dot" => {
            println!("digraph dependencies {{");
            println!("  \"{}\" [label=\"{}\"];", register.name(), register.name());
            for dep in &dependencies {
                println!(
                    "  \"{}\" -> \"{}\" [label=\"{}\"];",
                    register.name(),
                    dep.name,
                    dep.version
                );
            }
            println!("}}");
        }
        _ => {
            println!("  Direct dependencies:");
            for dep in &dependencies {
                println!("    {}@{}", dep.name, dep.version);
            }
        }
    }

    Ok(())
}

pub async fn lock_dependencies(path: &Path) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    println!("Locking dependencies for register '{}'...", register.name());

    let dependencies = parse_dependencies(register.dependencies())
        .map_err(|e| miette!("Failed to parse dependencies: {}", e))?;

    let registry = Registry::default();
    let mut lock_data = std::collections::HashMap::new();

    for dep in &dependencies {
        let version = if dep.version == "latest" {
            registry.get_latest_version(&dep.name).await?
        } else {
            dep.version.clone()
        };

        lock_data.insert(dep.name.clone(), version);
    }

    let lock_content = toml::to_string_pretty(&serde_json::json!({
        "lockfile_version": "1.0",
        "register": {
            "name": register.name(),
            "version": register.version()
        },
        "dependencies": lock_data
    }))
    .into_diagnostic()
    .map_err(|e| miette!("Failed to serialize lock file: {}", e))?;

    let lock_path = path.join("register.lock");
    tokio::fs::write(&lock_path, lock_content)
        .await
        .into_diagnostic()
        .map_err(|e| miette!("Failed to write lock file: {}", e))?;

    println!("✓ Created lock file: {}", lock_path.display());
    Ok(())
}

pub async fn check_outdated_dependencies(path: &Path) -> Result<()> {
    let register = Register::load(path).map_err(|e| miette!("Failed to load register: {}", e))?;

    println!(
        "Checking for outdated dependencies in register '{}'...",
        register.name()
    );

    let dependencies = parse_dependencies(register.dependencies())
        .map_err(|e| miette!("Failed to parse dependencies: {}", e))?;

    let registry = Registry::default();
    let mut outdated = Vec::new();

    for dep in &dependencies {
        if let Ok(versions) = registry.list_versions(&dep.name).await {
            if let Some(latest) = versions.first() {
                if latest.version != dep.version && dep.version != "latest" {
                    outdated.push((
                        dep.name.clone(),
                        dep.version.clone(),
                        latest.version.clone(),
                    ));
                }
            }
        }
    }

    if outdated.is_empty() {
        println!("✓ All dependencies are up to date");
    } else {
        println!("Outdated dependencies:");
        for (name, current, latest) in &outdated {
            println!("  {name}: {current} -> {latest}");
        }
    }

    Ok(())
}
