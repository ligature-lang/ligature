//! Caching system for Ligature program results.

use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ligature_eval::Value;
use serde::{Deserialize, Serialize};
use tokio::fs;
use tracing::{debug, info, warn};

use crate::error::{Error, Result};

/// Cache statistics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    /// Total number of cache entries.
    pub total_entries: usize,
    /// Number of cache hits.
    pub hits: usize,
    /// Number of cache misses.
    pub misses: usize,
    /// Cache hit rate (0.0 to 1.0).
    pub hit_rate: f64,
    /// Total cache size in bytes.
    pub total_size: u64,
    /// Cache directory path.
    pub cache_dir: String,
}

/// Cache entry metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CacheEntry {
    /// The cached value as JSON string (since Value doesn't implement Serialize).
    value_json: String,
    /// When this entry was created.
    created_at: u64,
    /// When this entry was last accessed.
    last_accessed: u64,
    /// Number of times this entry was accessed.
    access_count: u64,
    /// File hash for content-based caching.
    content_hash: Option<String>,
}

/// A cache for Ligature program results.
pub struct Cache {
    cache_dir: PathBuf,
    stats: CacheStats,
    max_age: Duration,
    max_size: u64,
}

impl Cache {
    /// Create a new cache with the specified directory.
    pub async fn new(cache_dir: &str) -> Result<Self> {
        let cache_dir = PathBuf::from(cache_dir);

        // Create cache directory if it doesn't exist
        if !cache_dir.exists() {
            fs::create_dir_all(&cache_dir).await.map_err(|e| {
                Error::file_system(
                    format!("Failed to create cache directory: {e}"),
                    Some(cache_dir.to_string_lossy().to_string()),
                )
            })?;
        }

        let stats = CacheStats {
            total_entries: 0,
            hits: 0,
            misses: 0,
            hit_rate: 0.0,
            total_size: 0,
            cache_dir: cache_dir.to_string_lossy().to_string(),
        };

        Ok(Self {
            cache_dir,
            stats,
            max_age: Duration::from_secs(3600), // 1 hour default
            max_size: 100 * 1024 * 1024,        // 100 MB default
        })
    }

    /// Get a cached result for a file path.
    pub async fn get<P: AsRef<Path>>(&mut self, path: P) -> Result<Option<Value>> {
        let path = path.as_ref();
        let cache_key = self.path_to_cache_key(path);
        let cache_file = self.cache_dir.join(&cache_key);

        if !cache_file.exists() {
            self.stats.misses += 1;
            self.update_hit_rate();
            return Ok(None);
        }

        // Check if cache entry is too old
        if let Ok(metadata) = fs::metadata(&cache_file).await {
            if let Ok(modified) = metadata.modified() {
                if let Ok(age) = SystemTime::now().duration_since(modified) {
                    if age > self.max_age {
                        debug!("Cache entry expired for {:?}", path);
                        let _ = fs::remove_file(&cache_file).await;
                        self.stats.misses += 1;
                        self.update_hit_rate();
                        return Ok(None);
                    }
                }
            }
        }

        // Read and deserialize cache entry
        match fs::read_to_string(&cache_file).await {
            Ok(content) => {
                match serde_json::from_str::<CacheEntry>(&content) {
                    Ok(mut entry) => {
                        // Update access statistics
                        entry.last_accessed = SystemTime::now()
                            .duration_since(UNIX_EPOCH)
                            .unwrap()
                            .as_secs();
                        entry.access_count += 1;

                        // Write updated entry back
                        if let Ok(updated_content) = serde_json::to_string(&entry) {
                            let _ = fs::write(&cache_file, updated_content).await;
                        }

                        self.stats.hits += 1;
                        self.update_hit_rate();
                        debug!("Cache hit for {:?}", path);
                        // Deserialize the Value from JSON
                        match serde_json::from_str::<Value>(&entry.value_json) {
                            Ok(value) => Ok(Some(value)),
                            Err(e) => {
                                warn!("Failed to deserialize cached value: {}", e);
                                Ok(None)
                            }
                        }
                    }
                    Err(e) => {
                        warn!("Failed to deserialize cache entry: {}", e);
                        let _ = fs::remove_file(&cache_file).await;
                        self.stats.misses += 1;
                        self.update_hit_rate();
                        Ok(None)
                    }
                }
            }
            Err(e) => {
                warn!("Failed to read cache file: {}", e);
                self.stats.misses += 1;
                self.update_hit_rate();
                Ok(None)
            }
        }
    }

    /// Get a cached result for source content.
    pub async fn get_by_content(&mut self, content: &str) -> Result<Option<Value>> {
        let content_hash = self.hash_content(content);
        let cache_key = format!("content_{content_hash}");
        let cache_file = self.cache_dir.join(&cache_key);

        if !cache_file.exists() {
            self.stats.misses += 1;
            self.update_hit_rate();
            return Ok(None);
        }

        // Read and deserialize cache entry
        match fs::read_to_string(&cache_file).await {
            Ok(content) => {
                match serde_json::from_str::<CacheEntry>(&content) {
                    Ok(mut entry) => {
                        // Update access statistics
                        entry.last_accessed = SystemTime::now()
                            .duration_since(UNIX_EPOCH)
                            .unwrap()
                            .as_secs();
                        entry.access_count += 1;

                        // Write updated entry back
                        if let Ok(updated_content) = serde_json::to_string(&entry) {
                            let _ = fs::write(&cache_file, updated_content).await;
                        }

                        self.stats.hits += 1;
                        self.update_hit_rate();
                        debug!("Cache hit for content");
                        // Deserialize the Value from JSON
                        match serde_json::from_str::<Value>(&entry.value_json) {
                            Ok(value) => Ok(Some(value)),
                            Err(e) => {
                                warn!("Failed to deserialize cached value: {}", e);
                                Ok(None)
                            }
                        }
                    }
                    Err(e) => {
                        warn!("Failed to deserialize cache entry: {}", e);
                        let _ = fs::remove_file(&cache_file).await;
                        self.stats.misses += 1;
                        self.update_hit_rate();
                        Ok(None)
                    }
                }
            }
            Err(e) => {
                warn!("Failed to read cache file: {}", e);
                self.stats.misses += 1;
                self.update_hit_rate();
                Ok(None)
            }
        }
    }

    /// Set a cached result for a file path.
    pub async fn set<P: AsRef<Path>>(&mut self, path: P, value: &Value) -> Result<()> {
        let path = path.as_ref();
        let cache_key = self.path_to_cache_key(path);
        let cache_file = self.cache_dir.join(&cache_key);

        let entry = CacheEntry {
            value_json: serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}")), /* Use proper JSON serialization */
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            last_accessed: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            access_count: 1,
            content_hash: None,
        };

        let content = serde_json::to_string(&entry).map_err(Error::JsonSerialization)?;

        let content_len = content.len();
        fs::write(&cache_file, content).await.map_err(|e| {
            Error::file_system(
                format!("Failed to write cache file: {e}"),
                Some(cache_file.to_string_lossy().to_string()),
            )
        })?;

        self.stats.total_entries += 1;
        self.stats.total_size += content_len as u64;

        debug!("Cached result for {:?}", path);
        Ok(())
    }

    /// Set a cached result for source content.
    pub async fn set_by_content(&mut self, content: &str, value: &Value) -> Result<()> {
        let content_hash = self.hash_content(content);
        let cache_key = format!("content_{content_hash}");
        let cache_file = self.cache_dir.join(&cache_key);

        let entry = CacheEntry {
            value_json: serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}")), /* Use proper JSON serialization */
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            last_accessed: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            access_count: 1,
            content_hash: Some(content_hash),
        };

        let content = serde_json::to_string(&entry).map_err(Error::JsonSerialization)?;

        let content_len = content.len();
        fs::write(&cache_file, content).await.map_err(|e| {
            Error::file_system(
                format!("Failed to write cache file: {e}"),
                Some(cache_file.to_string_lossy().to_string()),
            )
        })?;

        self.stats.total_entries += 1;
        self.stats.total_size += content_len as u64;

        debug!("Cached result for content");
        Ok(())
    }

    /// Clear all cache entries.
    pub async fn clear(&mut self) -> Result<()> {
        let mut entries = fs::read_dir(&self.cache_dir).await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })?;

        while let Some(entry) = entries.next_entry().await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory entry: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })? {
            let _ = fs::remove_file(entry.path()).await;
        }

        self.stats.total_entries = 0;
        self.stats.total_size = 0;
        self.stats.hits = 0;
        self.stats.misses = 0;
        self.stats.hit_rate = 0.0;

        info!("Cache cleared");
        Ok(())
    }

    /// Get cache statistics.
    pub async fn stats(&self) -> Result<CacheStats> {
        Ok(self.stats.clone())
    }

    /// Set the maximum age for cache entries.
    pub fn set_max_age(&mut self, max_age: Duration) {
        self.max_age = max_age;
    }

    /// Set the maximum size for the cache.
    pub fn set_max_size(&mut self, max_size: u64) {
        self.max_size = max_size;
    }

    /// Convert a file path to a cache key.
    fn path_to_cache_key(&self, path: &Path) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        path.hash(&mut hasher);
        format!("file_{:x}", hasher.finish())
    }

    /// Hash content for content-based caching.
    fn hash_content(&self, content: &str) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        content.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    /// Update the hit rate statistic.
    fn update_hit_rate(&mut self) {
        let total = self.stats.hits + self.stats.misses;
        if total > 0 {
            self.stats.hit_rate = self.stats.hits as f64 / total as f64;
        }
    }
}

#[cfg(test)]
mod tests {
    use ligature_eval::Value;
    use tempfile::tempdir;

    use super::*;

    #[tokio::test]
    async fn test_cache_creation() {
        let temp_dir = tempdir().unwrap();
        let cache = Cache::new(temp_dir.path().to_string_lossy().as_ref()).await;
        assert!(cache.is_ok());
    }

    #[tokio::test]
    async fn test_cache_set_get() {
        let temp_dir = tempdir().unwrap();
        let mut cache = Cache::new(temp_dir.path().to_string_lossy().as_ref())
            .await
            .unwrap();

        let value = Value::integer(42, ligature_ast::Span::default());

        // Test file-based caching
        cache.set("test.lig", &value).await.unwrap();
        let cached = cache.get("test.lig").await.unwrap();
        assert!(cached.is_some());
        assert_eq!(cached.unwrap(), value);

        // Test content-based caching
        cache.set_by_content("let x = 42", &value).await.unwrap();
        let cached = cache.get_by_content("let x = 42").await.unwrap();
        assert!(cached.is_some());
        assert_eq!(cached.unwrap(), value);
    }

    #[tokio::test]
    async fn test_cache_clear() {
        let temp_dir = tempdir().unwrap();
        let mut cache = Cache::new(temp_dir.path().to_string_lossy().as_ref())
            .await
            .unwrap();

        let value = Value::integer(42, ligature_ast::Span::default());
        cache.set("test.lig", &value).await.unwrap();

        cache.clear().await.unwrap();

        let cached = cache.get("test.lig").await.unwrap();
        assert!(cached.is_none());
    }
}
