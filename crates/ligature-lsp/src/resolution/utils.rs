//! Utility functions for URI and path handling.
//!
//! This module provides utilities for converting between URIs and file paths,
//! and other common operations needed by the import resolution system.

use std::path::{Path, PathBuf};

use ligature_ast::{AstError, AstResult};
use tower_lsp::lsp_types::Url;

/// URI utilities for path/URI conversion.
pub struct UriUtils;

impl UriUtils {
    /// Create a new URI utilities instance.
    pub fn new() -> Self {
        Self
    }

    /// Convert a URI to a file path.
    pub fn uri_to_path(&self, uri: &str) -> AstResult<PathBuf> {
        let url = Url::parse(uri).map_err(|e| AstError::Parse {
            code: ligature_ast::ErrorCode::M4001,
            message: format!("Invalid URI: {e}"),
            span: ligature_ast::Span::default(),
            suggestions: vec!["Check that the URI is properly formatted".to_string()],
        })?;

        Ok(url.to_file_path().map_err(|_| AstError::Parse {
            code: ligature_ast::ErrorCode::M4001,
            message: format!("Cannot convert URI to file path: {uri}"),
            span: ligature_ast::Span::default(),
            suggestions: vec!["Ensure the URI points to a valid file path".to_string()],
        })?)
    }

    /// Convert a file path to a URI.
    pub fn path_to_uri(&self, path: &Path) -> AstResult<String> {
        let url = Url::from_file_path(path).map_err(|_| AstError::Parse {
            code: ligature_ast::ErrorCode::M4001,
            message: format!("Cannot convert path to URI: {path:?}"),
            span: ligature_ast::Span::default(),
            suggestions: vec!["Ensure the path is absolute and valid".to_string()],
        })?;

        Ok(url.to_string())
    }

    /// Normalize a path by resolving any `.` and `..` components.
    pub fn normalize_path(&self, path: &Path) -> PathBuf {
        let mut components = Vec::new();

        for component in path.components() {
            match component {
                std::path::Component::CurDir => {
                    // Skip current directory
                }
                std::path::Component::ParentDir => {
                    // Go up one level
                    components.pop();
                }
                _ => {
                    components.push(component);
                }
            }
        }

        components.into_iter().collect()
    }

    /// Check if a path is within a given directory.
    pub fn is_path_within_directory(&self, path: &Path, directory: &Path) -> bool {
        let normalized_path = self.normalize_path(path);
        let normalized_dir = self.normalize_path(directory);

        normalized_path.starts_with(&normalized_dir)
    }

    /// Get the relative path from a base directory to a target path.
    pub fn get_relative_path(&self, base: &Path, target: &Path) -> AstResult<PathBuf> {
        let normalized_base = self.normalize_path(base);
        let normalized_target = self.normalize_path(target);

        if !self.is_path_within_directory(&normalized_target, &normalized_base) {
            return Err(AstError::Parse {
                code: ligature_ast::ErrorCode::M4001,
                message: "Target path is not within base directory".to_string(),
                span: ligature_ast::Span::default(),
                suggestions: vec![
                    "Ensure the target path is within the base directory".to_string(),
                ],
            }
            .into());
        }

        let mut relative_components = Vec::new();
        let mut target_components = normalized_target.components();
        let mut base_components = normalized_base.components();

        // Skip common prefix
        loop {
            match (base_components.next(), target_components.next()) {
                (Some(base_comp), Some(target_comp)) => {
                    if base_comp != target_comp {
                        return Err(AstError::Parse {
                            code: ligature_ast::ErrorCode::M4001,
                            message: "Paths do not share a common prefix".to_string(),
                            span: ligature_ast::Span::default(),
                            suggestions: vec!["Ensure the paths share a common base".to_string()],
                        }
                        .into());
                    }
                }
                (None, Some(target_comp)) => {
                    // Base is exhausted, remaining target components form the relative path
                    relative_components.push(target_comp);
                    relative_components.extend(target_components);
                    break;
                }
                (Some(_), None) => {
                    // Target is exhausted, this shouldn't happen if target is within base
                    return Err(AstError::Parse {
                        code: ligature_ast::ErrorCode::M4001,
                        message: "Target path is shorter than base path".to_string(),
                        span: ligature_ast::Span::default(),
                        suggestions: vec![
                            "Ensure the target path is within the base directory".to_string(),
                        ],
                    }
                    .into());
                }
                (None, None) => {
                    // Both exhausted, paths are identical
                    break;
                }
            }
        }

        Ok(relative_components.into_iter().collect())
    }

    /// Check if a URI is a file URI.
    pub fn is_file_uri(&self, uri: &str) -> bool {
        uri.starts_with("file://")
    }

    /// Check if a URI is a valid file URI.
    pub fn is_valid_file_uri(&self, uri: &str) -> bool {
        if !self.is_file_uri(uri) {
            return false;
        }

        self.uri_to_path(uri).is_ok()
    }

    /// Get the file extension from a URI.
    pub fn get_file_extension(&self, uri: &str) -> Option<String> {
        if let Ok(path) = self.uri_to_path(uri) {
            path.extension()
                .and_then(|ext| ext.to_str())
                .map(|s| s.to_string())
        } else {
            None
        }
    }

    /// Check if a URI has a specific file extension.
    pub fn has_file_extension(&self, uri: &str, extension: &str) -> bool {
        self.get_file_extension(uri)
            .map(|ext| ext == extension)
            .unwrap_or(false)
    }

    /// Get the file name from a URI.
    pub fn get_file_name(&self, uri: &str) -> Option<String> {
        if let Ok(path) = self.uri_to_path(uri) {
            path.file_name()
                .and_then(|name| name.to_str())
                .map(|s| s.to_string())
        } else {
            None
        }
    }

    /// Get the directory name from a URI.
    pub fn get_directory_name(&self, uri: &str) -> Option<String> {
        if let Ok(path) = self.uri_to_path(uri) {
            path.parent()
                .and_then(|parent| parent.file_name())
                .and_then(|name| name.to_str())
                .map(|s| s.to_string())
        } else {
            None
        }
    }

    /// Join a base URI with a relative path.
    pub fn join_uri_path(&self, base_uri: &str, relative_path: &str) -> AstResult<String> {
        let base_path = self.uri_to_path(base_uri)?;
        let joined_path = base_path.join(relative_path);
        self.path_to_uri(&joined_path)
    }

    /// Resolve a relative URI against a base URI.
    pub fn resolve_relative_uri(&self, base_uri: &str, relative_uri: &str) -> AstResult<String> {
        if self.is_file_uri(relative_uri) {
            // Already an absolute URI
            Ok(relative_uri.to_string())
        } else {
            // Relative URI, resolve against base
            self.join_uri_path(base_uri, relative_uri)
        }
    }
}

impl Default for UriUtils {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_uri_utils_creation() {
        let _utils = UriUtils::new();
        // Just test that it can be created
    }

    #[test]
    fn test_uri_to_path() {
        let utils = UriUtils::new();

        // Test valid file URI
        let uri = "file:///test/path/file.lig";
        let result = utils.uri_to_path(uri);
        assert!(result.is_ok());

        let path = result.unwrap();
        assert_eq!(path, PathBuf::from("/test/path/file.lig"));
    }

    #[test]
    fn test_uri_to_path_invalid() {
        let utils = UriUtils::new();

        // Test invalid URI
        let uri = "invalid://uri";
        let result = utils.uri_to_path(uri);
        assert!(result.is_err());
    }

    #[test]
    fn test_path_to_uri() {
        let utils = UriUtils::new();

        // Test valid path
        let path = PathBuf::from("/test/path/file.lig");
        let result = utils.path_to_uri(&path);
        assert!(result.is_ok());

        let uri = result.unwrap();
        assert!(uri.starts_with("file://"));
        assert!(uri.contains("/test/path/file.lig"));
    }

    #[test]
    fn test_normalize_path() {
        let utils = UriUtils::new();

        // Test path with . and ..
        let path = PathBuf::from("/test/./path/../file.lig");
        let normalized = utils.normalize_path(&path);
        assert_eq!(normalized, PathBuf::from("/test/file.lig"));
    }

    #[test]
    fn test_is_path_within_directory() {
        let utils = UriUtils::new();

        let base = PathBuf::from("/test");
        let within = PathBuf::from("/test/path/file.lig");
        let outside = PathBuf::from("/other/path/file.lig");

        assert!(utils.is_path_within_directory(&within, &base));
        assert!(!utils.is_path_within_directory(&outside, &base));
    }

    #[test]
    fn test_get_relative_path() {
        let utils = UriUtils::new();

        let base = PathBuf::from("/test");
        let target = PathBuf::from("/test/path/file.lig");

        let result = utils.get_relative_path(&base, &target);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PathBuf::from("path/file.lig"));
    }

    #[test]
    fn test_is_file_uri() {
        let utils = UriUtils::new();

        assert!(utils.is_file_uri("file:///test/path"));
        assert!(!utils.is_file_uri("http://example.com"));
        assert!(!utils.is_file_uri("invalid"));
    }

    #[test]
    fn test_get_file_extension() {
        let utils = UriUtils::new();

        let uri = "file:///test/path/file.lig";
        let extension = utils.get_file_extension(uri);
        assert_eq!(extension, Some("lig".to_string()));
    }

    #[test]
    fn test_has_file_extension() {
        let utils = UriUtils::new();

        let uri = "file:///test/path/file.lig";
        assert!(utils.has_file_extension(uri, "lig"));
        assert!(!utils.has_file_extension(uri, "rs"));
    }

    #[test]
    fn test_get_file_name() {
        let utils = UriUtils::new();

        let uri = "file:///test/path/file.lig";
        let file_name = utils.get_file_name(uri);
        assert_eq!(file_name, Some("file.lig".to_string()));
    }

    #[test]
    fn test_join_uri_path() {
        let utils = UriUtils::new();

        let base_uri = "file:///test/path";
        let relative_path = "subdir/file.lig";

        let result = utils.join_uri_path(base_uri, relative_path);
        assert!(result.is_ok());

        let joined_uri = result.unwrap();
        assert!(joined_uri.contains("/test/path/subdir/file.lig"));
    }

    #[test]
    fn test_resolve_relative_uri() {
        let utils = UriUtils::new();

        let base_uri = "file:///test/path";
        let relative_uri = "file.lig";

        let result = utils.resolve_relative_uri(base_uri, relative_uri);
        assert!(result.is_ok());

        let resolved_uri = result.unwrap();
        assert!(resolved_uri.contains("/test/path/file.lig"));
    }
}
