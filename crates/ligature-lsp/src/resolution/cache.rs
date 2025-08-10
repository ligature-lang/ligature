//! Module caching functionality for the LSP server.
//!
//! This module provides structures and utilities for caching loaded modules
//! and tracking module metadata.

use std::path::PathBuf;

use ligature_ast::Program;

/// A module cache entry containing the loaded module and its metadata.
#[derive(Debug, Clone)]
pub struct ModuleCacheEntry {
    /// The loaded module.
    pub module: Program,
    /// The file path where this module was loaded from.
    pub file_path: PathBuf,
    /// The URI of the module file.
    pub uri: String,
    /// Whether this module has been fully resolved (all imports processed).
    pub fully_resolved: bool,
    /// Timestamp of when this module was last loaded.
    pub last_loaded: std::time::SystemTime,
}

/// Statistics about the module cache and dependencies.
#[derive(Debug, Clone, Default)]
pub struct ModuleStats {
    /// Total number of loaded modules.
    pub total_modules: usize,
    /// Total number of dependencies.
    pub total_dependencies: usize,
    /// Total number of reverse dependencies.
    pub total_reverse_dependencies: usize,
}

impl ModuleCacheEntry {
    /// Create a new module cache entry.
    pub fn new(module: Program, file_path: PathBuf, uri: String) -> Self {
        Self {
            module,
            file_path,
            uri,
            fully_resolved: false,
            last_loaded: std::time::SystemTime::now(),
        }
    }

    /// Check if the module file has been modified since it was last loaded.
    pub fn is_stale(&self) -> bool {
        if let Ok(metadata) = std::fs::metadata(&self.file_path) {
            if let Ok(modified) = metadata.modified() {
                return modified > self.last_loaded;
            }
        }
        true // Consider stale if we can't determine modification time
    }

    /// Mark the module as fully resolved.
    pub fn mark_resolved(&mut self) {
        self.fully_resolved = true;
    }

    /// Update the last loaded timestamp.
    pub fn update_timestamp(&mut self) {
        self.last_loaded = std::time::SystemTime::now();
    }
}

impl ModuleStats {
    /// Create new module statistics.
    pub fn new(
        total_modules: usize,
        total_dependencies: usize,
        total_reverse_dependencies: usize,
    ) -> Self {
        Self {
            total_modules,
            total_dependencies,
            total_reverse_dependencies,
        }
    }

    /// Get the total number of loaded modules.
    pub fn total_modules(&self) -> usize {
        self.total_modules
    }

    /// Get the total number of dependencies.
    pub fn total_dependencies(&self) -> usize {
        self.total_dependencies
    }

    /// Get the total number of reverse dependencies.
    pub fn total_reverse_dependencies(&self) -> usize {
        self.total_reverse_dependencies
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::Program;

    use super::*;

    #[test]
    fn test_module_cache_entry_creation() {
        let program = Program {
            declarations: vec![],
        };
        let file_path = PathBuf::from("/test/path/module.lig");
        let uri = "file:///test/path/module.lig".to_string();

        let entry = ModuleCacheEntry::new(program.clone(), file_path.clone(), uri.clone());

        assert_eq!(entry.module.declarations.len(), 0);
        assert_eq!(entry.file_path, file_path);
        assert_eq!(entry.uri, uri);
        assert!(!entry.fully_resolved);
    }

    #[test]
    fn test_module_cache_entry_mark_resolved() {
        let program = Program {
            declarations: vec![],
        };
        let mut entry = ModuleCacheEntry::new(
            program,
            PathBuf::from("/test/path/module.lig"),
            "file:///test/path/module.lig".to_string(),
        );

        assert!(!entry.fully_resolved);
        entry.mark_resolved();
        assert!(entry.fully_resolved);
    }

    #[test]
    fn test_module_stats_creation() {
        let stats = ModuleStats::new(10, 25, 15);

        assert_eq!(stats.total_modules(), 10);
        assert_eq!(stats.total_dependencies(), 25);
        assert_eq!(stats.total_reverse_dependencies(), 15);
    }

    #[test]
    fn test_module_stats_default() {
        let stats = ModuleStats::default();

        assert_eq!(stats.total_modules(), 0);
        assert_eq!(stats.total_dependencies(), 0);
        assert_eq!(stats.total_reverse_dependencies(), 0);
    }
}
