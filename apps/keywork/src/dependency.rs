//! Dependency resolution and management.

use crate::registry::Registry;
use miette::{Result, miette};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dependency {
    pub name: String,
    pub version: String,
    pub registry: Option<String>,
}

#[derive(Debug, Clone)]
pub struct DependencyGraph {
    pub nodes: HashMap<String, DependencyNode>,
    pub edges: HashMap<String, Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct DependencyNode {
    pub dependency: Dependency,
    pub resolved: bool,
    #[allow(dead_code)]
    pub conflicts: Vec<DependencyConflict>,
    pub resolved_version: Option<String>,
    pub registry: Option<Registry>,
}

#[derive(Debug, Clone)]
pub struct DependencyConflict {
    pub package: String,
    pub requested_version: String,
    pub resolved_version: String,
    #[allow(dead_code)]
    pub conflict_type: ConflictType,
}

#[derive(Debug, Clone)]
pub enum ConflictType {
    #[allow(dead_code)]
    VersionMismatch,
    CircularDependency,
    MissingDependency,
    #[allow(dead_code)]
    IncompatibleVersion,
}

#[derive(Debug, Clone)]
pub struct ResolutionResult {
    pub resolved_dependencies: HashMap<String, String>,
    pub conflicts: Vec<DependencyConflict>,
    #[allow(dead_code)]
    pub resolution_order: Vec<String>,
    pub success: bool,
}

/// Semantic version comparison utilities
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Semver {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub pre_release: Option<String>,
    pub build: Option<String>,
}

impl Semver {
    #[allow(dead_code)]
    pub fn parse(version: &str) -> Result<Self> {
        // Remove leading 'v' if present
        let version = version.trim_start_matches('v');

        // Split on '+' for build metadata first
        let parts: Vec<&str> = version.split('+').collect();
        let version_without_build = parts[0];
        let build = if parts.len() > 1 {
            Some(parts[1].to_string())
        } else {
            None
        };

        // Split on '-' for pre-release
        let parts: Vec<&str> = version_without_build.split('-').collect();
        let version_part = parts[0];
        let pre_release = if parts.len() > 1 {
            Some(parts[1].to_string())
        } else {
            None
        };

        // Split version numbers
        let numbers: Vec<&str> = version_part.split('.').collect();
        if numbers.len() != 3 {
            return Err(miette!("Invalid semver format: {}", version));
        }

        let major = numbers[0]
            .parse::<u64>()
            .map_err(|_| miette!("Invalid major version: {}", numbers[0]))?;
        let minor = numbers[1]
            .parse::<u64>()
            .map_err(|_| miette!("Invalid minor version: {}", numbers[1]))?;
        let patch = numbers[2]
            .parse::<u64>()
            .map_err(|_| miette!("Invalid patch version: {}", numbers[2]))?;

        Ok(Semver {
            major,
            minor,
            patch,
            pre_release,
            build,
        })
    }

    #[allow(dead_code)]
    pub fn satisfies_constraint(&self, constraint: &str) -> bool {
        if constraint == "latest" {
            return true;
        }

        if constraint == "*" || constraint == "x" || constraint == "X" {
            return true;
        }

        // Handle exact version
        if !constraint.starts_with(['>', '<', '=', '~', '^']) {
            return self
                == &Semver::parse(constraint).unwrap_or(Semver {
                    major: 0,
                    minor: 0,
                    patch: 0,
                    pre_release: None,
                    build: None,
                });
        }

        // Handle version ranges
        if let Some(version) = constraint.strip_prefix('>') {
            if let Some(version) = constraint.strip_prefix(">=") {
                if let Ok(req_version) = Semver::parse(version) {
                    return self >= &req_version;
                }
            } else if let Ok(req_version) = Semver::parse(version) {
                return self > &req_version;
            }
        } else if let Some(version) = constraint.strip_prefix('<') {
            if let Some(version) = constraint.strip_prefix("<=") {
                if let Ok(req_version) = Semver::parse(version) {
                    return self <= &req_version;
                }
            } else if let Ok(req_version) = Semver::parse(version) {
                return self < &req_version;
            }
        } else if let Some(version) = constraint.strip_prefix('=') {
            if let Ok(req_version) = Semver::parse(version) {
                return self == &req_version;
            }
        } else if let Some(version) = constraint.strip_prefix('~') {
            // Tilde range: ~1.2.3 means >=1.2.3 and <1.3.0
            if let Ok(req_version) = Semver::parse(version) {
                let min_version = req_version.clone();
                let max_version = Semver {
                    major: req_version.major,
                    minor: req_version.minor + 1,
                    patch: 0,
                    pre_release: None,
                    build: None,
                };
                return self >= &min_version && self < &max_version;
            }
        } else if let Some(version) = constraint.strip_prefix('^') {
            // Caret range: ^1.2.3 means >=1.2.3 and <2.0.0
            if let Ok(req_version) = Semver::parse(version) {
                let min_version = req_version.clone();
                let max_version = Semver {
                    major: req_version.major + 1,
                    minor: 0,
                    patch: 0,
                    pre_release: None,
                    build: None,
                };
                return self >= &min_version && self < &max_version;
            }
        }

        false
    }
}

impl Dependency {
    pub fn new(name: String, version: String) -> Self {
        Self {
            name,
            version,
            registry: None,
        }
    }

    #[allow(dead_code)]
    pub fn with_registry(mut self, registry: String) -> Self {
        self.registry = Some(registry);
        self
    }

    #[allow(dead_code)]
    pub fn parse(spec: &str) -> Result<Self> {
        // Parse dependency specification like "package@version" or "package"
        let parts: Vec<&str> = spec.split('@').collect();

        match parts.as_slice() {
            [name] => Ok(Dependency::new(name.to_string(), "latest".to_string())),
            [name, version] => Ok(Dependency::new(name.to_string(), version.to_string())),
            _ => Err(miette!("Invalid dependency specification: {}", spec)),
        }
    }

    // Remove the inherent to_string method as it shadows Display
}

impl std::fmt::Display for Dependency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(registry) = &self.registry {
            write!(f, "{}@{} from {}", self.name, self.version, registry)
        } else {
            write!(f, "{}@{}", self.name, self.version)
        }
    }
}

impl Dependency {
    #[allow(dead_code)]
    pub fn satisfies_version(&self, version: &str) -> bool {
        // Use proper semver comparison
        if self.version == "latest" {
            return true;
        }

        if let Ok(req_semver) = Semver::parse(&self.version) {
            if let Ok(_actual_semver) = Semver::parse(version) {
                return req_semver.satisfies_constraint(&self.version);
            }
        }

        // Fallback to exact string matching
        self.version == version
    }
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
        }
    }
}

impl Default for DependencyGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl DependencyGraph {
    pub fn add_dependency(&mut self, dependency: Dependency) {
        let node_name = dependency.name.clone();
        let node = DependencyNode {
            dependency,
            resolved: false,
            conflicts: Vec::new(),
            resolved_version: None,
            registry: None,
        };

        self.nodes.insert(node_name.clone(), node);
        self.edges.insert(node_name, Vec::new());
    }

    #[allow(dead_code)]
    pub fn add_dependency_edge(&mut self, from: &str, to: &str) {
        if let Some(edges) = self.edges.get_mut(from) {
            if !edges.contains(&to.to_string()) {
                edges.push(to.to_string());
            }
        }
    }

    pub async fn resolve_dependencies(&mut self) -> Result<ResolutionResult> {
        let mut resolved_dependencies = HashMap::new();
        let mut conflicts = Vec::new();
        let mut resolution_order = Vec::new();
        let mut success = true;

        // First pass: resolve direct dependencies
        let node_names: Vec<String> = self.nodes.keys().cloned().collect();
        for node_name in node_names {
            // Get a mutable reference to the node
            if let Some(node) = self.nodes.get_mut(&node_name) {
                // Create a registry instance for resolution
                let registry = Registry::default();

                // Try to resolve the version
                let version_to_resolve = if node.dependency.version == "latest" {
                    match registry.get_latest_version(&node.dependency.name).await {
                        Ok(version) => version,
                        Err(_) => "0.1.0".to_string(), // Fallback version
                    }
                } else {
                    node.dependency.version.clone()
                };

                // Validate that the package exists
                if (registry
                    .validate_package(&node.dependency.name, &version_to_resolve)
                    .await)
                    .is_err()
                {
                    success = false;
                    conflicts.push(DependencyConflict {
                        package: node_name.clone(),
                        requested_version: node.dependency.version.clone(),
                        resolved_version: "unknown".to_string(),
                        conflict_type: ConflictType::MissingDependency,
                    });
                } else {
                    node.resolved = true;
                    node.resolved_version = Some(version_to_resolve.clone());
                    node.registry = Some(registry);
                    resolved_dependencies.insert(node_name.clone(), version_to_resolve);
                    resolution_order.push(node_name.clone());
                }
            }
        }

        // Second pass: detect circular dependencies
        let mut visited = HashSet::new();
        let mut visiting = HashSet::new();

        let node_names: Vec<String> = self.nodes.keys().cloned().collect();
        for node_name in node_names {
            if !visited.contains(&node_name)
                && self
                    .visit_node(&node_name, &mut visited, &mut visiting)
                    .is_err()
            {
                success = false;
                conflicts.push(DependencyConflict {
                    package: node_name.clone(),
                    requested_version: "circular".to_string(),
                    resolved_version: "circular".to_string(),
                    conflict_type: ConflictType::CircularDependency,
                });
            }
        }

        Ok(ResolutionResult {
            resolved_dependencies,
            conflicts,
            resolution_order,
            success,
        })
    }

    #[allow(dead_code)]
    async fn resolve_single_dependency_simple(
        &self,
        _node_name: &str,
        node: &mut DependencyNode,
    ) -> Result<()> {
        // Simple resolution: just mark as resolved with the requested version
        node.resolved = true;
        node.resolved_version = Some(node.dependency.version.clone());
        Ok(())
    }

    #[allow(dead_code)]
    async fn resolve_single_dependency(
        &self,
        _node_name: &str,
        node: &mut DependencyNode,
    ) -> Result<()> {
        // For now, use simple resolution
        // In a full implementation, this would:
        // 1. Query the registry for available versions
        // 2. Check version constraints
        // 3. Resolve conflicts
        // 4. Download package metadata

        let registry = Registry::default();

        // Try to get the latest version if "latest" is specified
        let version_to_resolve = if node.dependency.version == "latest" {
            match registry.get_latest_version(&node.dependency.name).await {
                Ok(version) => version,
                Err(_) => "0.1.0".to_string(), // Fallback version
            }
        } else {
            node.dependency.version.clone()
        };

        // Validate that the package exists
        if (registry
            .validate_package(&node.dependency.name, &version_to_resolve)
            .await)
            .is_err()
        {
            return Err(miette!(
                "Package {}@{} not found in registry",
                node.dependency.name,
                version_to_resolve
            ));
        }

        node.resolved = true;
        node.resolved_version = Some(version_to_resolve);
        node.registry = Some(registry);

        Ok(())
    }

    fn visit_node(
        &self,
        node_name: &str,
        resolved: &mut HashSet<String>,
        visiting: &mut HashSet<String>,
    ) -> Result<()> {
        if visiting.contains(node_name) {
            return Err(miette!("Circular dependency detected"));
        }

        if resolved.contains(node_name) {
            return Ok(());
        }

        visiting.insert(node_name.to_string());

        if let Some(edges) = self.edges.get(node_name) {
            for dependency in edges {
                self.visit_node(dependency, resolved, visiting)?;
            }
        }

        visiting.remove(node_name);
        resolved.insert(node_name.to_string());
        Ok(())
    }

    #[allow(dead_code)]
    pub fn detect_conflicts(&self) -> Vec<DependencyConflict> {
        let mut conflicts = Vec::new();

        // Check for version conflicts
        let mut version_map: HashMap<String, Vec<String>> = HashMap::new();

        for (node_name, node) in &self.nodes {
            if let Some(version) = &node.resolved_version {
                version_map
                    .entry(node_name.clone())
                    .or_default()
                    .push(version.clone());
            }
        }

        for (package, versions) in version_map {
            if versions.len() > 1 {
                // Multiple versions requested for the same package
                let unique_versions: Vec<String> = versions
                    .into_iter()
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                if unique_versions.len() > 1 {
                    conflicts.push(DependencyConflict {
                        package,
                        requested_version: unique_versions[0].clone(),
                        resolved_version: unique_versions[1].clone(),
                        conflict_type: ConflictType::VersionMismatch,
                    });
                }
            }
        }

        conflicts
    }

    #[allow(dead_code)]
    pub fn get_resolution_order(&self) -> Vec<String> {
        let mut order = Vec::new();
        let mut visited = HashSet::new();

        for node_name in self.nodes.keys() {
            if !visited.contains(node_name) {
                self.topological_sort(node_name, &mut visited, &mut order);
            }
        }

        order.reverse();
        order
    }

    #[allow(dead_code)]
    fn topological_sort(
        &self,
        node_name: &str,
        visited: &mut HashSet<String>,
        order: &mut Vec<String>,
    ) {
        if visited.contains(node_name) {
            return;
        }

        visited.insert(node_name.to_string());

        if let Some(edges) = self.edges.get(node_name) {
            for dependency in edges {
                self.topological_sort(dependency, visited, order);
            }
        }

        order.push(node_name.to_string());
    }

    #[allow(dead_code)]
    pub fn validate(&self) -> Result<()> {
        // Check for circular dependencies
        let mut visited = HashSet::new();
        let mut visiting = HashSet::new();

        for node_name in self.nodes.keys() {
            if !visited.contains(node_name) {
                self.visit_node(node_name, &mut visited, &mut visiting)?;
            }
        }

        // Check for unresolved dependencies
        for (node_name, node) in &self.nodes {
            if !node.resolved {
                return Err(miette!("Unresolved dependency: {}", node_name));
            }
        }

        Ok(())
    }

    #[allow(dead_code)]
    pub fn add_transitive_dependencies(&mut self, _registry: &Registry) -> Result<()> {
        // This would add dependencies of dependencies
        // For now, just return Ok() as this is a placeholder
        Ok(())
    }
}

#[allow(dead_code)]
pub fn parse_dependencies(dependencies: &HashMap<String, String>) -> Result<Vec<Dependency>> {
    let mut result = Vec::new();

    for (name, version) in dependencies {
        let dependency = Dependency::new(name.clone(), version.clone());
        result.push(dependency);
    }

    Ok(result)
}

pub async fn resolve_dependencies_from_manifest(manifest_path: &Path) -> Result<DependencyGraph> {
    let content = std::fs::read_to_string(manifest_path)
        .map_err(|e| miette!("Failed to read manifest: {}", e))?;

    let manifest: toml::Value =
        toml::from_str(&content).map_err(|e| miette!("Failed to parse manifest: {}", e))?;

    let mut graph = DependencyGraph::new();

    if let Some(dependencies) = manifest.get("dependencies") {
        if let Some(deps_table) = dependencies.as_table() {
            for (name, version) in deps_table {
                let version_str = version.as_str().unwrap_or("latest");
                let dependency = Dependency::new(name.clone(), version_str.to_string());
                graph.add_dependency(dependency);
            }
        }
    }

    Ok(graph)
}

pub async fn install_dependencies(graph: &DependencyGraph, install_path: &Path) -> Result<()> {
    // Ensure install directory exists
    std::fs::create_dir_all(install_path)
        .map_err(|e| miette!("Failed to create install directory: {}", e))?;

    let registry = Registry::default();

    for (node_name, node) in &graph.nodes {
        if let Some(version) = &node.resolved_version {
            println!("Installing {node_name}@{version}...");

            // Download the package
            let cached_file = registry.download_package_cached(node_name, version).await?;

            // Extract to install path
            let package_install_path = install_path.join(format!("{node_name}-{version}"));
            extract_package(&cached_file, &package_install_path).await?;

            println!("✓ Installed {node_name}@{version}");
        }
    }

    Ok(())
}

pub async fn extract_package(archive_path: &Path, extract_path: &Path) -> Result<()> {
    // Ensure extract directory exists
    std::fs::create_dir_all(extract_path)
        .map_err(|e| miette!("Failed to create extract directory: {}", e))?;

    // For now, just copy the file
    // In a real implementation, you'd extract a tar.gz or zip file
    if archive_path.is_file() {
        std::fs::copy(
            archive_path,
            extract_path.join(archive_path.file_name().unwrap()),
        )
        .map_err(|e| miette!("Failed to copy package: {}", e))?;
    }

    Ok(())
}
