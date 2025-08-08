//! Registry operations for remote package management.

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::{Duration, SystemTime};

use miette::{IntoDiagnostic, Result, miette};
use serde::{Deserialize, Serialize};
use tokio::fs;

use crate::xdg_config::KeyworkXdgConfig;

#[derive(Debug, Clone)]
pub struct Registry {
    pub url: String,
    pub client: reqwest::Client,
    pub cache_dir: PathBuf,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryPackage {
    pub name: String,
    pub version: String,
    pub description: String,
    pub authors: Vec<String>,
    pub license: String,
    pub repository: Option<String>,
    pub dependencies: HashMap<String, String>,
    pub exports: HashMap<String, String>,
    pub metadata: Option<PackageMetadata>,
    pub download_url: Option<String>,
    pub checksum: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageMetadata {
    pub tags: Vec<String>,
    pub downloads: u64,
    pub last_updated: String,
    pub size: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub packages: Vec<RegistryPackage>,
    pub total: u64,
    pub page: u64,
    pub per_page: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageVersion {
    pub version: String,
    pub published_at: String,
    pub downloads: u64,
    pub yanked: bool,
}

impl Default for Registry {
    fn default() -> Self {
        // Use a fallback cache directory if XDG is not available
        let cache_dir = dirs::cache_dir()
            .unwrap_or_else(|| PathBuf::from("/tmp"))
            .join("keywork");

        Self {
            url: "http://localhost:8080".to_string(), /* Use localhost for development to trigger mock mode */
            client: reqwest::Client::builder()
                .timeout(Duration::from_secs(30))
                .user_agent("keywork/1.0.0")
                .build()
                .unwrap_or_default(),
            cache_dir,
        }
    }
}

impl Registry {
    /// Create a new registry with the given URL.
    pub fn new(url: String) -> Self {
        // Use a fallback cache directory if XDG is not available
        let cache_dir = dirs::cache_dir()
            .unwrap_or_else(|| PathBuf::from("/tmp"))
            .join("keywork");

        Self {
            url,
            client: reqwest::Client::builder()
                .timeout(Duration::from_secs(30))
                .user_agent("keywork/1.0.0")
                .build()
                .unwrap_or_default(),
            cache_dir,
        }
    }

    /// Create a new registry with XDG configuration.
    pub async fn with_xdg_config() -> Result<Self> {
        let xdg_config = KeyworkXdgConfig::new()
            .await
            .map_err(|e| miette!("Failed to load XDG configuration: {}", e))?;

        let cache_dir = xdg_config
            .cache_dir()
            .map_err(|e| miette!("Failed to get cache directory: {}", e))?;

        let timeout = Duration::from_secs(xdg_config.registry_timeout());

        let mut client_builder = reqwest::Client::builder()
            .timeout(timeout)
            .user_agent("keywork/1.0.0");

        // Add auth token if available
        if let Some(token) = xdg_config.auth_token(xdg_config.registry_url()) {
            client_builder = client_builder.default_headers({
                let mut headers = reqwest::header::HeaderMap::new();
                headers.insert("Authorization", format!("Bearer {token}").parse().unwrap());
                headers
            });
        }

        let client = client_builder
            .build()
            .map_err(|e| miette!("Failed to create HTTP client: {}", e))?;

        Ok(Self {
            url: xdg_config.registry_url().to_string(),
            client,
            cache_dir,
        })
    }

    pub async fn ensure_cache_dir(&self) -> Result<()> {
        fs::create_dir_all(&self.cache_dir)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create cache directory: {}", e))?;
        Ok(())
    }

    pub async fn search(&self, query: &str, limit: usize) -> Result<SearchResult> {
        // For development, return mock data if registry is not available
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return self.mock_search(query, limit);
        }

        let url = format!("{}/api/v1/search?q={}&limit={}", self.url, query, limit);

        let response = self
            .client
            .get(&url)
            .send()
            .await
            .map_err(|e| miette!("Failed to search registry: {}", e))?;

        if !response.status().is_success() {
            return Err(miette!(
                "Registry search failed with status: {}",
                response.status()
            ));
        }

        let result: SearchResult = response
            .json()
            .await
            .map_err(|e| miette!("Failed to parse search response: {}", e))?;

        Ok(result)
    }

    fn mock_search(&self, query: &str, _limit: usize) -> Result<SearchResult> {
        // Return mock search results for development
        let mock_packages = vec![
            RegistryPackage {
                name: "stdlib".to_string(),
                version: "1.0.0".to_string(),
                description: "Standard library for Ligature".to_string(),
                authors: vec!["Ligature Team".to_string()],
                license: "Apache-2.0".to_string(),
                repository: Some("https://github.com/ligature-lang/stdlib".to_string()),
                dependencies: HashMap::new(),
                exports: HashMap::new(),
                metadata: Some(PackageMetadata {
                    tags: vec!["standard-library".to_string(), "core".to_string()],
                    downloads: 1000,
                    last_updated: "2024-01-01T00:00:00Z".to_string(),
                    size: Some(1024),
                }),
                download_url: None,
                checksum: None,
            },
            RegistryPackage {
                name: "validation".to_string(),
                version: "0.5.0".to_string(),
                description: "Data validation utilities".to_string(),
                authors: vec!["Community Contributor".to_string()],
                license: "Apache-2.0".to_string(),
                repository: Some("https://github.com/ligature-lang/validation".to_string()),
                dependencies: HashMap::new(),
                exports: HashMap::new(),
                metadata: Some(PackageMetadata {
                    tags: vec!["validation".to_string(), "utilities".to_string()],
                    downloads: 500,
                    last_updated: "2024-01-15T00:00:00Z".to_string(),
                    size: Some(512),
                }),
                download_url: None,
                checksum: None,
            },
        ];

        let filtered_packages: Vec<RegistryPackage> = mock_packages
            .into_iter()
            .filter(|pkg| {
                pkg.name.contains(query)
                    || pkg
                        .description
                        .to_lowercase()
                        .contains(&query.to_lowercase())
            })
            .collect();

        let total = filtered_packages.len() as u64;

        Ok(SearchResult {
            packages: filtered_packages,
            total,
            page: 1,
            per_page: 10,
        })
    }

    pub async fn get_package(&self, name: &str, version: Option<&str>) -> Result<RegistryPackage> {
        let version = version.unwrap_or("latest");

        // For development, return mock data
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return self.mock_get_package(name, version);
        }

        let url = format!("{}/api/v1/packages/{}/{}", self.url, name, version);

        let response = self
            .client
            .get(&url)
            .send()
            .await
            .map_err(|e| miette!("Failed to get package: {}", e))?;

        if !response.status().is_success() {
            return Err(miette!("Package not found: {}@{}", name, version));
        }

        let package: RegistryPackage = response
            .json()
            .await
            .map_err(|e| miette!("Failed to parse package response: {}", e))?;

        Ok(package)
    }

    fn mock_get_package(&self, name: &str, version: &str) -> Result<RegistryPackage> {
        match name {
            "stdlib" => Ok(RegistryPackage {
                name: "stdlib".to_string(),
                version: version.to_string(),
                description: "Standard library for Ligature".to_string(),
                authors: vec!["Ligature Team".to_string()],
                license: "Apache-2.0".to_string(),
                repository: Some("https://github.com/ligature-lang/stdlib".to_string()),
                dependencies: HashMap::new(),
                exports: HashMap::from([
                    ("core".to_string(), "src/core.lig".to_string()),
                    ("collections".to_string(), "src/collections.lig".to_string()),
                ]),
                metadata: Some(PackageMetadata {
                    tags: vec!["standard-library".to_string(), "core".to_string()],
                    downloads: 1000,
                    last_updated: "2024-01-01T00:00:00Z".to_string(),
                    size: Some(1024),
                }),
                download_url: Some(
                    "https://registry.ligature.dev/downloads/stdlib-1.0.0.tar.gz".to_string(),
                ),
                checksum: Some("sha256:abc123...".to_string()),
            }),
            "validation" => Ok(RegistryPackage {
                name: "validation".to_string(),
                version: version.to_string(),
                description: "Data validation utilities".to_string(),
                authors: vec!["Community Contributor".to_string()],
                license: "Apache-2.0".to_string(),
                repository: Some("https://github.com/ligature-lang/validation".to_string()),
                dependencies: HashMap::from([("stdlib".to_string(), ">=1.0.0".to_string())]),
                exports: HashMap::from([
                    ("validators".to_string(), "src/validators.lig".to_string()),
                    ("schemas".to_string(), "src/schemas.lig".to_string()),
                ]),
                metadata: Some(PackageMetadata {
                    tags: vec!["validation".to_string(), "utilities".to_string()],
                    downloads: 500,
                    last_updated: "2024-01-15T00:00:00Z".to_string(),
                    size: Some(512),
                }),
                download_url: Some(
                    "https://registry.ligature.dev/downloads/validation-0.5.0.tar.gz".to_string(),
                ),
                checksum: Some("sha256:def456...".to_string()),
            }),
            _ => Err(miette!("Package not found: {}@{}", name, version)),
        }
    }

    pub async fn download_package(
        &self,
        name: &str,
        version: &str,
        output_path: &std::path::Path,
    ) -> Result<()> {
        // For development, create a mock package file
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return self.mock_download_package(name, version, output_path).await;
        }

        let package = self.get_package(name, Some(version)).await?;

        let download_url = package
            .download_url
            .ok_or_else(|| miette!("No download URL available for {}@{}", name, version))?;

        let response = self
            .client
            .get(&download_url)
            .send()
            .await
            .map_err(|e| miette!("Failed to download package: {}", e))?;

        if !response.status().is_success() {
            return Err(miette!("Failed to download package: {}", response.status()));
        }

        let bytes = response
            .bytes()
            .await
            .map_err(|e| miette!("Failed to read package data: {}", e))?;

        fs::write(output_path, &bytes)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to write package file: {}", e))?;

        Ok(())
    }

    async fn mock_download_package(
        &self,
        name: &str,
        version: &str,
        output_path: &std::path::Path,
    ) -> Result<()> {
        // Create a mock package file for development
        let mock_content =
            format!("# Mock package: {name}@{version}\n# This is a development mock file\n");

        fs::write(output_path, mock_content)
            .await
            .into_diagnostic()
            .map_err(|e| miette!("Failed to create mock package: {}", e))?;

        Ok(())
    }

    pub async fn download_package_cached(&self, name: &str, version: &str) -> Result<PathBuf> {
        self.ensure_cache_dir().await?;

        let cache_key = format!("{name}-{version}.tar.gz");
        let cache_path = self.cache_dir.join(&cache_key);

        // Check if already cached
        if cache_path.exists() {
            // Check if cache is fresh (less than 1 hour old)
            if let Ok(metadata) = fs::metadata(&cache_path).await {
                if let Ok(modified) = metadata.modified() {
                    if let Ok(now) = SystemTime::now().duration_since(modified) {
                        if now.as_secs() < 3600 {
                            // 1 hour
                            return Ok(cache_path);
                        }
                    }
                }
            }
        }

        // Download and cache
        self.download_package(name, version, &cache_path).await?;

        Ok(cache_path)
    }

    pub async fn publish_package(&self, package_data: &[u8], auth_token: &str) -> Result<()> {
        // For development, just log the publish attempt
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            println!(
                "[MOCK] Publishing package ({} bytes) to {}",
                package_data.len(),
                self.url
            );
            return Ok(());
        }

        let url = format!("{}/api/v1/publish", self.url);

        let response = self
            .client
            .post(&url)
            .header("Authorization", format!("Bearer {auth_token}"))
            .header("Content-Type", "application/octet-stream")
            .body(package_data.to_vec())
            .send()
            .await
            .map_err(|e| miette!("Failed to publish package: {}", e))?;

        if !response.status().is_success() {
            let status = response.status();
            let error_text = response
                .text()
                .await
                .unwrap_or_else(|_| "Unknown error".to_string());
            return Err(miette!(
                "Failed to publish package: {} - {}",
                status,
                error_text
            ));
        }

        Ok(())
    }

    pub async fn list_versions(&self, name: &str) -> Result<Vec<PackageVersion>> {
        // For development, return mock versions
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return self.mock_list_versions(name);
        }

        let url = format!("{}/api/v1/packages/{}/versions", self.url, name);

        let response = self
            .client
            .get(&url)
            .send()
            .await
            .map_err(|e| miette!("Failed to list versions: {}", e))?;

        if !response.status().is_success() {
            return Err(miette!("Failed to list versions: {}", response.status()));
        }

        let versions: Vec<PackageVersion> = response
            .json()
            .await
            .map_err(|e| miette!("Failed to parse versions response: {}", e))?;

        Ok(versions)
    }

    fn mock_list_versions(&self, name: &str) -> Result<Vec<PackageVersion>> {
        match name {
            "stdlib" => Ok(vec![
                PackageVersion {
                    version: "1.0.0".to_string(),
                    published_at: "2024-01-01T00:00:00Z".to_string(),
                    downloads: 1000,
                    yanked: false,
                },
                PackageVersion {
                    version: "0.9.0".to_string(),
                    published_at: "2023-12-01T00:00:00Z".to_string(),
                    downloads: 500,
                    yanked: false,
                },
            ]),
            "validation" => Ok(vec![
                PackageVersion {
                    version: "0.5.0".to_string(),
                    published_at: "2024-01-15T00:00:00Z".to_string(),
                    downloads: 300,
                    yanked: false,
                },
                PackageVersion {
                    version: "0.4.0".to_string(),
                    published_at: "2023-12-15T00:00:00Z".to_string(),
                    downloads: 200,
                    yanked: false,
                },
            ]),
            _ => Ok(vec![]),
        }
    }

    pub async fn get_latest_version(&self, name: &str) -> Result<String> {
        let versions = self.list_versions(name).await?;

        if versions.is_empty() {
            return Err(miette!("No versions found for package: {}", name));
        }

        // Find the latest non-yanked version
        let latest = versions
            .iter()
            .filter(|v| !v.yanked)
            .max_by_key(|v| &v.version)
            .ok_or_else(|| miette!("No valid versions found for package: {}", name))?;

        Ok(latest.version.clone())
    }

    pub async fn validate_package(&self, name: &str, version: &str) -> Result<bool> {
        // For development, always return true for known packages
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return Ok(matches!(name, "stdlib" | "validation"));
        }

        match self.get_package(name, Some(version)).await {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    pub async fn get_package_stats(&self, name: &str) -> Result<HashMap<String, u64>> {
        // For development, return mock stats
        if self.url.contains("localhost") || self.url.contains("127.0.0.1") {
            return self.mock_get_package_stats(name);
        }

        let url = format!("{}/api/v1/packages/{}/stats", self.url, name);

        let response = self
            .client
            .get(&url)
            .send()
            .await
            .map_err(|e| miette!("Failed to get package stats: {}", e))?;

        if !response.status().is_success() {
            return Err(miette!(
                "Failed to get package stats: {}",
                response.status()
            ));
        }

        let stats: HashMap<String, u64> = response
            .json()
            .await
            .map_err(|e| miette!("Failed to parse stats response: {}", e))?;

        Ok(stats)
    }

    fn mock_get_package_stats(&self, name: &str) -> Result<HashMap<String, u64>> {
        let mut stats = HashMap::new();

        match name {
            "stdlib" => {
                stats.insert("downloads".to_string(), 1000);
                stats.insert("versions".to_string(), 2);
                stats.insert("dependencies".to_string(), 0);
            }
            "validation" => {
                stats.insert("downloads".to_string(), 500);
                stats.insert("versions".to_string(), 2);
                stats.insert("dependencies".to_string(), 1);
            }
            _ => {
                stats.insert("downloads".to_string(), 0);
                stats.insert("versions".to_string(), 0);
                stats.insert("dependencies".to_string(), 0);
            }
        }

        Ok(stats)
    }
}
