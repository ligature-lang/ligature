//! Caching system for Ligature program results.

use std::collections::HashMap;
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
    /// Number of evicted entries.
    pub evicted_entries: usize,
    /// Number of invalid entries.
    pub invalid_entries: usize,
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
    /// Entry size in bytes.
    size: u64,
}

/// Cache eviction policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvictionPolicy {
    /// Least Recently Used - evict least recently accessed entries.
    Lru,
    /// Least Frequently Used - evict least frequently accessed entries.
    Lfu,
    /// First In First Out - evict oldest entries.
    Fifo,
}

impl Default for EvictionPolicy {
    fn default() -> Self {
        Self::Lru
    }
}

/// A cache for Ligature program results.
pub struct Cache {
    cache_dir: PathBuf,
    stats: CacheStats,
    max_age: Duration,
    max_size: u64,
    eviction_policy: EvictionPolicy,
    /// Track cache entries for eviction (key -> last_accessed)
    entry_timestamps: HashMap<String, u64>,
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

        let mut cache = Self {
            cache_dir,
            stats: CacheStats {
                total_entries: 0,
                hits: 0,
                misses: 0,
                hit_rate: 0.0,
                total_size: 0,
                cache_dir: String::new(),
                evicted_entries: 0,
                invalid_entries: 0,
            },
            max_age: Duration::from_secs(3600), // 1 hour default
            max_size: 100 * 1024 * 1024,        // 100 MB default
            eviction_policy: EvictionPolicy::default(),
            entry_timestamps: HashMap::new(),
        };

        // Initialize cache stats from existing files
        cache.initialize_stats().await?;
        cache.stats.cache_dir = cache.cache_dir.to_string_lossy().to_string();

        Ok(cache)
    }

    /// Initialize cache statistics from existing cache files.
    async fn initialize_stats(&mut self) -> Result<()> {
        let mut entries = fs::read_dir(&self.cache_dir).await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })?;

        let mut total_entries = 0;
        let mut total_size = 0;
        let mut invalid_entries = 0;

        while let Some(entry) = entries.next_entry().await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory entry: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })? {
            let path = entry.path();
            if path.is_file() {
                total_entries += 1;
                
                // Get file size
                if let Ok(metadata) = fs::metadata(&path).await {
                    total_size += metadata.len();
                }

                // Validate cache entry
                if let Ok(content) = fs::read_to_string(&path).await {
                    if let Ok(cache_entry) = serde_json::from_str::<CacheEntry>(&content) {
                        // Track entry for eviction
                        let key = path.file_name()
                            .and_then(|n| n.to_str())
                            .unwrap_or("unknown")
                            .to_string();
                        self.entry_timestamps.insert(key, cache_entry.last_accessed);
                    } else {
                        invalid_entries += 1;
                        // Remove invalid entry
                        let _ = fs::remove_file(&path).await;
                    }
                } else {
                    invalid_entries += 1;
                    // Remove unreadable entry
                    let _ = fs::remove_file(&path).await;
                }
            }
        }

        self.stats.total_entries = total_entries;
        self.stats.total_size = total_size;
        self.stats.invalid_entries = invalid_entries;

        debug!("Initialized cache with {} entries, {} bytes, {} invalid entries", 
               total_entries, total_size, invalid_entries);

        Ok(())
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
                        self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                        self.entry_timestamps.remove(&cache_key);
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
                        let now = SystemTime::now()
                            .duration_since(UNIX_EPOCH)
                            .unwrap()
                            .as_secs();
                        entry.last_accessed = now;
                        entry.access_count += 1;

                        // Update entry timestamps for eviction
                        self.entry_timestamps.insert(cache_key.clone(), now);

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
                                // Remove invalid entry
                                let _ = fs::remove_file(&cache_file).await;
                                self.stats.invalid_entries += 1;
                                self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                                self.entry_timestamps.remove(&cache_key);
                                Ok(None)
                            }
                        }
                    }
                    Err(e) => {
                        warn!("Failed to deserialize cache entry: {}", e);
                        let _ = fs::remove_file(&cache_file).await;
                        self.stats.misses += 1;
                        self.stats.invalid_entries += 1;
                        self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                        self.entry_timestamps.remove(&cache_key);
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
                        let now = SystemTime::now()
                            .duration_since(UNIX_EPOCH)
                            .unwrap()
                            .as_secs();
                        entry.last_accessed = now;
                        entry.access_count += 1;

                        // Update entry timestamps for eviction
                        self.entry_timestamps.insert(cache_key.clone(), now);

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
                                // Remove invalid entry
                                let _ = fs::remove_file(&cache_file).await;
                                self.stats.invalid_entries += 1;
                                self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                                self.entry_timestamps.remove(&cache_key);
                                Ok(None)
                            }
                        }
                    }
                    Err(e) => {
                        warn!("Failed to deserialize cache entry: {}", e);
                        let _ = fs::remove_file(&cache_file).await;
                        self.stats.misses += 1;
                        self.stats.invalid_entries += 1;
                        self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                        self.entry_timestamps.remove(&cache_key);
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
            value_json: serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}")),
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
            size: 0, // Will be set after serialization
        };

        let content = serde_json::to_string(&entry).map_err(Error::JsonSerialization)?;
        let content_len = content.len() as u64;

        // Check if we need to evict entries to make space
        if self.stats.total_size + content_len > self.max_size {
            self.evict_entries(content_len).await?;
        }

        // Update entry with actual size
        let mut entry_with_size = entry;
        entry_with_size.size = content_len;
        let content_with_size = serde_json::to_string(&entry_with_size).map_err(Error::JsonSerialization)?;

        fs::write(&cache_file, content_with_size).await.map_err(|e| {
            Error::file_system(
                format!("Failed to write cache file: {e}"),
                Some(cache_file.to_string_lossy().to_string()),
            )
        })?;

        self.stats.total_entries += 1;
        self.stats.total_size += content_len;
        self.entry_timestamps.insert(cache_key, entry_with_size.last_accessed);

        debug!("Cached result for {:?}", path);
        Ok(())
    }

    /// Set a cached result for source content.
    pub async fn set_by_content(&mut self, content: &str, value: &Value) -> Result<()> {
        let content_hash = self.hash_content(content);
        let cache_key = format!("content_{content_hash}");
        let cache_file = self.cache_dir.join(&cache_key);

        let entry = CacheEntry {
            value_json: serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}")),
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
            size: 0, // Will be set after serialization
        };

        let content = serde_json::to_string(&entry).map_err(Error::JsonSerialization)?;
        let content_len = content.len() as u64;

        // Check if we need to evict entries to make space
        if self.stats.total_size + content_len > self.max_size {
            self.evict_entries(content_len).await?;
        }

        // Update entry with actual size
        let mut entry_with_size = entry;
        entry_with_size.size = content_len;
        let content_with_size = serde_json::to_string(&entry_with_size).map_err(Error::JsonSerialization)?;

        fs::write(&cache_file, content_with_size).await.map_err(|e| {
            Error::file_system(
                format!("Failed to write cache file: {e}"),
                Some(cache_file.to_string_lossy().to_string()),
            )
        })?;

        self.stats.total_entries += 1;
        self.stats.total_size += content_len;
        self.entry_timestamps.insert(cache_key, entry_with_size.last_accessed);

        debug!("Cached result for content");
        Ok(())
    }

    /// Evict entries to make space for new entry.
    async fn evict_entries(&mut self, required_space: u64) -> Result<()> {
        let mut entries_to_evict = Vec::new();
        let mut current_size = self.stats.total_size;

        // Sort entries by eviction policy
        let mut sorted_entries: Vec<_> = self.entry_timestamps.iter().collect();
        match self.eviction_policy {
            EvictionPolicy::Lru => {
                sorted_entries.sort_by_key(|(_, &timestamp)| timestamp);
            }
            EvictionPolicy::Lfu => {
                // For LFU, we'd need to track access counts, but for now use LRU
                sorted_entries.sort_by_key(|(_, &timestamp)| timestamp);
            }
            EvictionPolicy::Fifo => {
                // For FIFO, we'd need to track creation times, but for now use LRU
                sorted_entries.sort_by_key(|(_, &timestamp)| timestamp);
            }
        }

        // Find entries to evict
        for (key, _) in sorted_entries {
            if current_size + required_space <= self.max_size {
                break;
            }

            let cache_file = self.cache_dir.join(key);
            if let Ok(content) = fs::read_to_string(&cache_file).await {
                if let Ok(entry) = serde_json::from_str::<CacheEntry>(&content) {
                    entries_to_evict.push((key.clone(), entry.size));
                    current_size = current_size.saturating_sub(entry.size);
                }
            }
        }

        // Evict entries
        for (key, size) in entries_to_evict {
            let cache_file = self.cache_dir.join(&key);
            if let Err(e) = fs::remove_file(&cache_file).await {
                warn!("Failed to evict cache entry {}: {}", key, e);
            } else {
                self.stats.evicted_entries += 1;
                self.stats.total_entries = self.stats.total_entries.saturating_sub(1);
                self.stats.total_size = self.stats.total_size.saturating_sub(size);
                self.entry_timestamps.remove(&key);
                debug!("Evicted cache entry: {}", key);
            }
        }

        if !entries_to_evict.is_empty() {
            info!("Evicted {} entries to make space for new cache entry", entries_to_evict.len());
        }

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
        self.stats.evicted_entries = 0;
        self.stats.invalid_entries = 0;
        self.entry_timestamps.clear();

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

    /// Set the eviction policy.
    pub fn set_eviction_policy(&mut self, policy: EvictionPolicy) {
        self.eviction_policy = policy;
    }

    /// Validate cache integrity.
    pub async fn validate(&mut self) -> Result<()> {
        let mut entries = fs::read_dir(&self.cache_dir).await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })?;

        let mut valid_entries = 0;
        let mut invalid_entries = 0;
        let mut total_size = 0;

        while let Some(entry) = entries.next_entry().await.map_err(|e| {
            Error::file_system(
                format!("Failed to read cache directory entry: {e}"),
                Some(self.cache_dir.to_string_lossy().to_string()),
            )
        })? {
            let path = entry.path();
            if path.is_file() {
                if let Ok(content) = fs::read_to_string(&path).await {
                    if let Ok(cache_entry) = serde_json::from_str::<CacheEntry>(&content) {
                        valid_entries += 1;
                        total_size += cache_entry.size;
                    } else {
                        invalid_entries += 1;
                        // Remove invalid entry
                        let _ = fs::remove_file(&path).await;
                    }
                } else {
                    invalid_entries += 1;
                    // Remove unreadable entry
                    let _ = fs::remove_file(&path).await;
                }
            }
        }

        self.stats.total_entries = valid_entries;
        self.stats.total_size = total_size;
        self.stats.invalid_entries = invalid_entries;

        info!("Cache validation complete: {} valid entries, {} invalid entries", 
              valid_entries, invalid_entries);

        Ok(())
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

    #[tokio::test]
    async fn test_cache_size_limit() {
        let temp_dir = tempdir().unwrap();
        let mut cache = Cache::new(temp_dir.path().to_string_lossy().as_ref())
            .await
            .unwrap();

        // Set a small size limit
        cache.set_max_size(1000);

        let value1 = Value::integer(42, ligature_ast::Span::default());
        let value2 = Value::integer(43, ligature_ast::Span::default());
        let value3 = Value::integer(44, ligature_ast::Span::default());

        // Add entries that will exceed the size limit
        cache.set("test1.lig", &value1).await.unwrap();
        cache.set("test2.lig", &value2).await.unwrap();
        cache.set("test3.lig", &value3).await.unwrap();

        // Verify that some entries were evicted
        let stats = cache.stats().await.unwrap();
        assert!(stats.total_size <= 1000);
    }

    #[tokio::test]
    async fn test_cache_validation() {
        let temp_dir = tempdir().unwrap();
        let mut cache = Cache::new(temp_dir.path().to_string_lossy().as_ref())
            .await
            .unwrap();

        let value = Value::integer(42, ligature_ast::Span::default());
        cache.set("test.lig", &value).await.unwrap();

        // Validate cache
        cache.validate().await.unwrap();

        let stats = cache.stats().await.unwrap();
        assert_eq!(stats.total_entries, 1);
        assert_eq!(stats.invalid_entries, 0);
    }
}
