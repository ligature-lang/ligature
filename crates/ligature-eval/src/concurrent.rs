//! Concurrent data structures for the Ligature evaluation engine.
//!
//! This module provides thread-safe data structures optimized for
//! concurrent access patterns in the evaluation engine.

use std::collections::HashMap;
use std::sync::Arc;

use dashmap::DashMap;
use ligature_ast::{Expr, Type};

use crate::environment::EvaluationEnvironment;
use crate::value::Value;

/// Cache key for expression evaluation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CacheKey {
    /// Expression hash
    pub expression_hash: u64,
    /// Environment hash
    pub environment_hash: u64,
    /// Evaluation depth
    pub depth: usize,
}

impl CacheKey {
    /// Create a new cache key
    pub fn new(expression: &Expr, environment: &EvaluationEnvironment, depth: usize) -> Self {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let mut hasher = DefaultHasher::new();
        // For now, use a simple hash based on expression span
        hasher.write_u64(expression.span.start as u64);
        hasher.write_u64(expression.span.end as u64);
        let expression_hash = hasher.finish();

        let mut hasher = DefaultHasher::new();
        // For now, use a simple hash based on environment bindings count
        hasher.write_usize(environment.current_bindings().len());
        let environment_hash = hasher.finish();

        Self {
            expression_hash,
            environment_hash,
            depth,
        }
    }
}

/// Thread-safe expression cache
#[derive(Debug)]
pub struct ConcurrentExpressionCache {
    /// Cache storage
    cache: DashMap<CacheKey, Value>,
    /// Maximum cache size
    max_size: usize,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ConcurrentExpressionCache {
    /// Create a new expression cache
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: DashMap::new(),
            max_size,
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Get a value from the cache
    pub fn get(&self, key: &CacheKey) -> Option<Value> {
        if let Some(value) = self.cache.get(key) {
            self.stats
                .entry("hits".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            Some(value.clone())
        } else {
            self.stats
                .entry("misses".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            None
        }
    }

    /// Put a value in the cache
    pub fn put(&self, key: CacheKey, value: Value) {
        // Check if we need to evict entries
        if self.cache.len() >= self.max_size {
            self.evict_entries();
        }

        self.cache.insert(key, value);
        self.stats
            .entry("insertions".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }

    /// Evict entries from the cache
    fn evict_entries(&self) {
        // Simple LRU eviction (in a real implementation, this would be more sophisticated)
        let to_remove: Vec<_> = self.cache
            .iter()
            .take(self.cache.len() / 4) // Remove 25% of entries
            .map(|entry| entry.key().clone())
            .collect();

        for key in to_remove {
            self.cache.remove(&key);
        }

        self.stats
            .entry("evictions".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }

    /// Get cache statistics
    pub fn stats(&self) -> HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }

    /// Clear the cache
    pub fn clear(&self) {
        self.cache.clear();
        self.stats.clear();
    }
}

/// Thread-safe type environment
#[derive(Debug)]
pub struct ConcurrentTypeEnvironment {
    /// Bindings storage
    bindings: DashMap<String, Type>,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ConcurrentTypeEnvironment {
    /// Create a new type environment
    pub fn new() -> Self {
        Self {
            bindings: DashMap::new(),
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Bind a name to a type
    pub fn bind(&self, name: String, type_: Type) {
        self.bindings.insert(name.clone(), type_);
        self.stats
            .entry("bindings".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }

    /// Look up a type by name
    pub fn lookup(&self, name: &str) -> Option<Type> {
        if let Some(type_) = self.bindings.get(name) {
            self.stats
                .entry("lookups".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            Some(type_.clone())
        } else {
            self.stats
                .entry("misses".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            None
        }
    }

    /// Check if a name is bound
    pub fn is_bound(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    /// Remove a binding
    pub fn remove(&self, name: &str) -> Option<Type> {
        if let Some((_, type_)) = self.bindings.remove(name) {
            self.stats
                .entry("removals".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            Some(type_)
        } else {
            None
        }
    }

    /// Get the number of bindings
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the environment is empty
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Get environment statistics
    pub fn stats(&self) -> HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }
}

impl Default for ConcurrentTypeEnvironment {
    fn default() -> Self {
        Self::new()
    }
}

/// Thread-safe value cache
#[derive(Debug)]
pub struct ConcurrentValueCache {
    /// Cache storage
    cache: DashMap<String, Value>,
    /// Maximum cache size
    max_size: usize,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ConcurrentValueCache {
    /// Create a new value cache
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: DashMap::new(),
            max_size,
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Get a value from the cache
    pub fn get(&self, key: &str) -> Option<Value> {
        if let Some(value) = self.cache.get(key) {
            self.stats
                .entry("hits".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            Some(value.clone())
        } else {
            self.stats
                .entry("misses".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            None
        }
    }

    /// Put a value in the cache
    pub fn put(&self, key: String, value: Value) {
        // Check if we need to evict entries
        if self.cache.len() >= self.max_size {
            self.evict_entries();
        }

        self.cache.insert(key, value);
        self.stats
            .entry("insertions".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }

    /// Evict entries from the cache
    fn evict_entries(&self) {
        // Simple LRU eviction
        let to_remove: Vec<_> = self
            .cache
            .iter()
            .take(self.cache.len() / 4)
            .map(|entry| entry.key().clone())
            .collect();

        for key in to_remove {
            self.cache.remove(&key);
        }

        self.stats
            .entry("evictions".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }

    /// Get cache statistics
    pub fn stats(&self) -> HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }

    /// Clear the cache
    pub fn clear(&self) {
        self.cache.clear();
        self.stats.clear();
    }
}

/// Thread-safe pattern matcher
#[derive(Debug)]
pub struct ConcurrentPatternMatcher {
    /// Pattern cache
    pattern_cache: DashMap<String, bool>,
    /// Statistics
    stats: Arc<DashMap<String, usize>>,
}

impl ConcurrentPatternMatcher {
    /// Create a new pattern matcher
    pub fn new() -> Self {
        Self {
            pattern_cache: DashMap::new(),
            stats: Arc::new(DashMap::new()),
        }
    }

    /// Match a value against a pattern
    pub fn match_pattern(&self, value: &Value, pattern: &ligature_ast::Pattern) -> bool {
        let cache_key = self.create_cache_key(value, pattern);

        if let Some(result) = self.pattern_cache.get(&cache_key) {
            self.stats
                .entry("cache_hits".to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            return *result;
        }

        let result = self.do_match(value, pattern);

        self.pattern_cache.insert(cache_key, result);
        self.stats
            .entry("cache_misses".to_string())
            .and_modify(|count| *count += 1)
            .or_insert(1);

        result
    }

    /// Create a cache key for pattern matching
    fn create_cache_key(&self, value: &Value, pattern: &ligature_ast::Pattern) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let mut hasher = DefaultHasher::new();
        // Hash the value content
        match &value.kind {
            crate::value::ValueKind::Integer(i) => {
                hasher.write_u8(0);
                hasher.write_i64(**i);
            }
            crate::value::ValueKind::Float(f) => {
                hasher.write_u8(1);
                hasher.write_u64(f.to_bits());
            }
            crate::value::ValueKind::String(s) => {
                hasher.write_u8(2);
                hasher.write(s.as_bytes());
            }
            crate::value::ValueKind::Boolean(b) => {
                hasher.write_u8(3);
                hasher.write_u8(if **b { 1 } else { 0 });
            }
            crate::value::ValueKind::Unit => {
                hasher.write_u8(4);
            }
            _ => {
                // For other types, use span as fallback
                hasher.write_u64(value.span.start as u64);
                hasher.write_u64(value.span.end as u64);
            }
        }

        // Hash the pattern content
        match pattern {
            ligature_ast::Pattern::Wildcard => {
                hasher.write_u8(0);
            }
            ligature_ast::Pattern::Variable(name) => {
                hasher.write_u8(1);
                hasher.write(name.as_bytes());
            }
            ligature_ast::Pattern::Literal(literal) => {
                hasher.write_u8(2);
                match literal {
                    ligature_ast::Literal::Integer(i) => {
                        hasher.write_u8(0);
                        hasher.write_i64(*i);
                    }
                    ligature_ast::Literal::Float(f) => {
                        hasher.write_u8(1);
                        hasher.write_u64(f.to_bits());
                    }
                    ligature_ast::Literal::String(s) => {
                        hasher.write_u8(2);
                        hasher.write(s.as_bytes());
                    }
                    ligature_ast::Literal::Boolean(b) => {
                        hasher.write_u8(3);
                        hasher.write_u8(if *b { 1 } else { 0 });
                    }
                    ligature_ast::Literal::Unit => {
                        hasher.write_u8(4);
                    }
                    ligature_ast::Literal::List(_) => {
                        hasher.write_u8(5);
                    }
                }
            }
            ligature_ast::Pattern::Record { fields } => {
                hasher.write_u8(3);
                for field in fields {
                    hasher.write(field.name.as_bytes());
                }
            }
            ligature_ast::Pattern::Union { variant, value } => {
                hasher.write_u8(4);
                hasher.write(variant.as_bytes());
                if let Some(val) = value {
                    // Hash the nested pattern content
                    match &**val {
                        ligature_ast::Pattern::Literal(literal) => match literal {
                            ligature_ast::Literal::Integer(i) => {
                                hasher.write_u8(0);
                                hasher.write_i64(*i);
                            }
                            ligature_ast::Literal::Float(f) => {
                                hasher.write_u8(1);
                                hasher.write_u64(f.to_bits());
                            }
                            ligature_ast::Literal::String(s) => {
                                hasher.write_u8(2);
                                hasher.write(s.as_bytes());
                            }
                            ligature_ast::Literal::Boolean(b) => {
                                hasher.write_u8(3);
                                hasher.write_u8(if *b { 1 } else { 0 });
                            }
                            ligature_ast::Literal::Unit => {
                                hasher.write_u8(4);
                            }
                            ligature_ast::Literal::List(_) => {
                                hasher.write_u8(5);
                            }
                        },
                        _ => {
                            // For complex patterns, use a simple hash
                            hasher.write_u8(99);
                        }
                    }
                }
            }
            ligature_ast::Pattern::List { elements } => {
                hasher.write_u8(5);
                for element in elements {
                    // Hash the element pattern content
                    match element {
                        ligature_ast::Pattern::Wildcard => hasher.write_u8(0),
                        ligature_ast::Pattern::Variable(name) => {
                            hasher.write_u8(1);
                            hasher.write(name.as_bytes());
                        }
                        ligature_ast::Pattern::Literal(literal) => {
                            hasher.write_u8(2);
                            match literal {
                                ligature_ast::Literal::Integer(i) => {
                                    hasher.write_u8(0);
                                    hasher.write_i64(*i);
                                }
                                ligature_ast::Literal::Float(f) => {
                                    hasher.write_u8(1);
                                    hasher.write_u64(f.to_bits());
                                }
                                ligature_ast::Literal::String(s) => {
                                    hasher.write_u8(2);
                                    hasher.write(s.as_bytes());
                                }
                                ligature_ast::Literal::Boolean(b) => {
                                    hasher.write_u8(3);
                                    hasher.write_u8(if *b { 1 } else { 0 });
                                }
                                ligature_ast::Literal::Unit => {
                                    hasher.write_u8(4);
                                }
                                ligature_ast::Literal::List(_) => {
                                    hasher.write_u8(5);
                                }
                            }
                        }
                        _ => {
                            // For complex patterns, use a simple hash
                            hasher.write_u8(99);
                        }
                    }
                }
            }
        }

        format!("{:x}", hasher.finish())
    }

    /// Perform the actual pattern matching
    #[allow(clippy::only_used_in_recursion)]
    fn do_match(&self, value: &Value, pattern: &ligature_ast::Pattern) -> bool {
        match pattern {
            ligature_ast::Pattern::Wildcard => true,
            ligature_ast::Pattern::Variable(_) => true,
            ligature_ast::Pattern::Literal(literal) => match (value, literal) {
                (
                    Value {
                        kind: crate::value::ValueKind::Integer(v),
                        ..
                    },
                    ligature_ast::Literal::Integer(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::String(v),
                        ..
                    },
                    ligature_ast::Literal::String(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::Boolean(v),
                        ..
                    },
                    ligature_ast::Literal::Boolean(l),
                ) => **v == *l,
                (
                    Value {
                        kind: crate::value::ValueKind::Float(v),
                        ..
                    },
                    ligature_ast::Literal::Float(l),
                ) => (**v - *l).abs() < f64::EPSILON,
                (
                    Value {
                        kind: crate::value::ValueKind::Unit,
                        ..
                    },
                    ligature_ast::Literal::Unit,
                ) => true,
                _ => false,
            },
            ligature_ast::Pattern::Record { fields } => {
                if let Some(record_fields) = value.as_record() {
                    fields.iter().all(|field| {
                        if let Some(value_field) = record_fields.get(&field.name) {
                            self.do_match(value_field, &field.pattern)
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            }
            ligature_ast::Pattern::Union {
                variant,
                value: pattern_value,
            } => {
                if let Some((value_variant, value_payload)) = value.as_union() {
                    if value_variant == variant {
                        if let Some(pattern_val) = pattern_value {
                            if let Some(value_val) = value_payload {
                                self.do_match(value_val, pattern_val)
                            } else {
                                false
                            }
                        } else {
                            value_payload.is_none()
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            ligature_ast::Pattern::List { elements } => {
                if let Some(list_elements) = value.as_list() {
                    if elements.len() == list_elements.len() {
                        elements
                            .iter()
                            .zip(list_elements.iter())
                            .all(|(pattern, value)| self.do_match(value, pattern))
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    /// Get matcher statistics
    pub fn stats(&self) -> HashMap<String, usize> {
        self.stats
            .iter()
            .map(|entry| (entry.key().clone(), *entry.value()))
            .collect()
    }
}

impl Default for ConcurrentPatternMatcher {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use ligature_ast::{Expr, ExprKind, Literal, Span};

    use super::*;

    #[test]
    fn test_concurrent_expression_cache() {
        let cache = ConcurrentExpressionCache::new(100);

        let expr = Expr {
            kind: ExprKind::Literal(Literal::Integer(42)),
            span: Span::default(),
        };
        let env = EvaluationEnvironment::new();
        let key = CacheKey::new(&expr, &env, 0);
        let value = Value::integer(42, Span::default());

        cache.put(key.clone(), value.clone());
        assert_eq!(cache.get(&key), Some(value));

        let stats = cache.stats();
        assert!(stats.get("insertions").unwrap() > &0);
        assert!(stats.get("hits").unwrap() > &0);
    }

    #[test]
    fn test_concurrent_type_environment() {
        let env = ConcurrentTypeEnvironment::new();

        env.bind("x".to_string(), Type::integer(Span::default()));
        assert_eq!(env.lookup("x"), Some(Type::integer(Span::default())));
        assert!(env.is_bound("x"));

        assert_eq!(env.remove("x"), Some(Type::integer(Span::default())));
        assert!(!env.is_bound("x"));
    }

    #[test]
    fn test_concurrent_value_cache() {
        let cache = ConcurrentValueCache::new(100);

        cache.put("key1".to_string(), Value::integer(42, Span::default()));
        assert_eq!(cache.get("key1"), Some(Value::integer(42, Span::default())));
        assert_eq!(cache.get("key2"), None);

        let stats = cache.stats();
        assert!(stats.get("insertions").unwrap() > &0);
        assert!(stats.get("hits").unwrap() > &0);
    }

    #[test]
    fn test_concurrent_pattern_matcher() {
        let matcher = ConcurrentPatternMatcher::new();

        let value = Value::integer(42, Span::default());
        let pattern = ligature_ast::Pattern::Literal(Literal::Integer(42));

        assert!(matcher.match_pattern(&value, &pattern));

        let pattern2 = ligature_ast::Pattern::Literal(Literal::Integer(43));
        assert!(!matcher.match_pattern(&value, &pattern2));

        let stats = matcher.stats();
        assert!(stats.get("cache_misses").unwrap() > &0);
    }
}
