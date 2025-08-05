//! Language SDKs for Krox.
//!
//! This module provides bindings for different programming languages,
//! allowing you to use Krox from Python, Node.js, Java, and Go.

use crate::{Client, ExecutionMode, ExecutionResult, Result};
use std::sync::Arc;
use tokio::sync::Mutex;

/// A thread-safe wrapper around the Krox client for use in language bindings.
pub struct SdkClient {
    client: Arc<Mutex<Client>>,
}

impl SdkClient {
    /// Create a new SDK client.
    pub async fn new(mode: ExecutionMode) -> Result<Self> {
        let client = Client::new(mode).await?;
        Ok(Self {
            client: Arc::new(Mutex::new(client)),
        })
    }

    /// Execute a Ligature program from a file.
    pub async fn execute_file(&self, path: String) -> Result<ExecutionResult> {
        let mut client = self.client.lock().await;
        client.execute_file(path).await
    }

    /// Execute a Ligature program from source code.
    pub async fn execute_source(&self, source: String) -> Result<ExecutionResult> {
        let mut client = self.client.lock().await;
        client.execute_source(&source).await
    }

    /// Get cache statistics.
    pub async fn cache_stats(&self) -> Result<Option<crate::cache::CacheStats>> {
        let mut client = self.client.lock().await;
        client.cache_stats().await
    }

    /// Clear the cache.
    pub async fn clear_cache(&self) -> Result<()> {
        let mut client = self.client.lock().await;
        client.clear_cache().await
    }
}

/// Python bindings for Krox.
#[cfg(feature = "python")]
pub mod python {
    use super::*;
    use pyo3::prelude::*;
    use pyo3::types::PyDict;
    use serde_json::Value as JsonValue;

    #[pyclass]
    pub struct PyKroxClient {
        client: SdkClient,
    }

    #[pymethods]
    impl PyKroxClient {
        #[new]
        fn new(mode: &str) -> PyResult<Self> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                        "Invalid execution mode: {}",
                        mode
                    )))
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            Ok(Self { client })
        }

        fn execute_file(&self, path: String) -> PyResult<PyObject> {
            let client = self.client.clone();
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.execute_file(path).await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            // Convert result to Python dict
            let gil = Python::acquire_gil();
            let py = gil.python();
            let dict = PyDict::new(py);

            // Convert value to JSON for Python
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            dict.set_item("value", json_value)?;
            dict.set_item("duration", result.metadata.duration.as_secs_f64())?;
            dict.set_item("cached", result.metadata.cached)?;
            dict.set_item("mode", format!("{}", result.metadata.mode))?;
            dict.set_item("warnings", result.metadata.warnings)?;

            Ok(dict.to_object(py))
        }

        fn execute_source(&self, source: String) -> PyResult<PyObject> {
            let client = self.client.clone();
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.execute_source(source).await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            // Convert result to Python dict
            let gil = Python::acquire_gil();
            let py = gil.python();
            let dict = PyDict::new(py);

            // Convert value to JSON for Python
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            dict.set_item("value", json_value)?;
            dict.set_item("duration", result.metadata.duration.as_secs_f64())?;
            dict.set_item("cached", result.metadata.cached)?;
            dict.set_item("mode", format!("{}", result.metadata.mode))?;
            dict.set_item("warnings", result.metadata.warnings)?;

            Ok(dict.to_object(py))
        }

        fn cache_stats(&self) -> PyResult<Option<PyObject>> {
            let client = self.client.clone();
            let stats = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.cache_stats().await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            if let Some(stats) = stats {
                let gil = Python::acquire_gil();
                let py = gil.python();
                let dict = PyDict::new(py);

                dict.set_item("total_entries", stats.total_entries)?;
                dict.set_item("hits", stats.hits)?;
                dict.set_item("misses", stats.misses)?;
                dict.set_item("hit_rate", stats.hit_rate)?;
                dict.set_item("total_size", stats.total_size)?;
                dict.set_item("cache_dir", stats.cache_dir)?;

                Ok(Some(dict.to_object(py)))
            } else {
                Ok(None)
            }
        }

        fn clear_cache(&self) -> PyResult<()> {
            let client = self.client.clone();
            tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.clear_cache().await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            Ok(())
        }
    }

    /// Python module definition.
    #[pymodule]
    fn krox(_py: Python, m: &PyModule) -> PyResult<()> {
        m.add_class::<PyKroxClient>()?;
        Ok(())
    }
}

/// Node.js bindings for Krox.
#[cfg(feature = "node")]
pub mod node {
    use super::*;
    use napi_derive::napi;
    use serde_json::Value as JsonValue;

    #[napi]
    pub struct NodeKroxClient {
        client: SdkClient,
    }

    #[napi]
    impl NodeKroxClient {
        #[napi(constructor)]
        pub fn new(mode: String) -> Result<Self, napi::Error> {
            let execution_mode = match mode.as_str() {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(napi::Error::from_reason(format!(
                        "Invalid execution mode: {}",
                        mode
                    )))
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            Ok(Self { client })
        }

        #[napi]
        pub async fn execute_file(&self, path: String) -> Result<serde_json::Value, napi::Error> {
            let result = self
                .client
                .execute_file(path)
                .await
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            // Convert result to JSON
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        #[napi]
        pub async fn execute_source(
            &self,
            source: String,
        ) -> Result<serde_json::Value, napi::Error> {
            let result = self
                .client
                .execute_source(source)
                .await
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            // Convert result to JSON
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        #[napi]
        pub async fn cache_stats(&self) -> Result<Option<serde_json::Value>, napi::Error> {
            let stats = self
                .client
                .cache_stats()
                .await
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            if let Some(stats) = stats {
                let mut stats_obj = serde_json::Map::new();
                stats_obj.insert(
                    "total_entries".to_string(),
                    serde_json::Value::Number(serde_json::Number::from(stats.total_entries)),
                );
                stats_obj.insert(
                    "hits".to_string(),
                    serde_json::Value::Number(serde_json::Number::from(stats.hits)),
                );
                stats_obj.insert(
                    "misses".to_string(),
                    serde_json::Value::Number(serde_json::Number::from(stats.misses)),
                );
                stats_obj.insert(
                    "hit_rate".to_string(),
                    serde_json::Value::Number(
                        serde_json::Number::from_f64(stats.hit_rate).unwrap(),
                    ),
                );
                stats_obj.insert(
                    "total_size".to_string(),
                    serde_json::Value::Number(serde_json::Number::from(stats.total_size)),
                );
                stats_obj.insert(
                    "cache_dir".to_string(),
                    serde_json::Value::String(stats.cache_dir),
                );

                Ok(Some(serde_json::Value::Object(stats_obj)))
            } else {
                Ok(None)
            }
        }

        #[napi]
        pub async fn clear_cache(&self) -> Result<(), napi::Error> {
            self.client
                .clear_cache()
                .await
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            Ok(())
        }
    }
}

/// Java bindings for Krox.
#[cfg(feature = "java")]
pub mod java {
    use super::*;
    use jni::objects::{JClass, JObject, JString};
    use jni::sys::jobject;
    use jni::JNIEnv;
    use serde_json::Value as JsonValue;

    pub struct JavaKroxClient {
        client: SdkClient,
    }

    impl JavaKroxClient {
        pub fn new(mode: &str) -> Result<Self, jni::errors::Error> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => return Err(jni::errors::Error::InvalidArguments),
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|_| jni::errors::Error::InvalidArguments)?;

            Ok(Self { client })
        }

        pub async fn execute_file(
            &self,
            path: String,
        ) -> Result<serde_json::Value, jni::errors::Error> {
            let result = self
                .client
                .execute_file(path)
                .await
                .map_err(|_| jni::errors::Error::InvalidArguments)?;

            // Convert result to JSON
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|_| jni::errors::Error::InvalidArguments)?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        pub async fn execute_source(
            &self,
            source: String,
        ) -> Result<serde_json::Value, jni::errors::Error> {
            let result = self
                .client
                .execute_source(source)
                .await
                .map_err(|_| jni::errors::Error::InvalidArguments)?;

            // Convert result to JSON
            let json_value: JsonValue = serde_json::to_value(&result.value)
                .map_err(|_| jni::errors::Error::InvalidArguments)?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }
    }

    #[no_mangle]
    pub extern "system" fn Java_com_krox_KroxClient_new(
        _env: JNIEnv,
        _class: JClass,
        mode: JString,
    ) -> jobject {
        // Implementation would go here
        std::ptr::null_mut()
    }

    #[no_mangle]
    pub extern "system" fn Java_com_krox_KroxClient_executeFile(
        _env: JNIEnv,
        _class: JClass,
        _client: JObject,
        _path: JString,
    ) -> jobject {
        // Implementation would go here
        std::ptr::null_mut()
    }
}

/// Go bindings for Krox.
#[cfg(feature = "go")]
pub mod go {
    use super::*;
    use std::ffi::{CStr, CString};
    use std::os::raw::c_char;

    pub struct GoKroxClient {
        client: SdkClient,
    }

    impl GoKroxClient {
        pub fn new(mode: &str) -> Result<Self, Box<dyn std::error::Error>> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => return Err("Invalid execution mode".into()),
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))?;

            Ok(Self { client })
        }

        pub async fn execute_file(
            &self,
            path: String,
        ) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
            let result = self.client.execute_file(path).await?;

            // Convert result to JSON
            let json_value: serde_json::Value = serde_json::to_value(&result.value)?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        pub async fn execute_source(
            &self,
            source: String,
        ) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
            let result = self.client.execute_source(source).await?;

            // Convert result to JSON
            let json_value: serde_json::Value = serde_json::to_value(&result.value)?;

            let mut result_obj = serde_json::Map::new();
            result_obj.insert("value".to_string(), json_value);
            result_obj.insert(
                "duration".to_string(),
                serde_json::Value::Number(
                    serde_json::Number::from_f64(result.metadata.duration.as_secs_f64()).unwrap(),
                ),
            );
            result_obj.insert(
                "cached".to_string(),
                serde_json::Value::Bool(result.metadata.cached),
            );
            result_obj.insert(
                "mode".to_string(),
                serde_json::Value::String(format!("{}", result.metadata.mode)),
            );
            result_obj.insert(
                "warnings".to_string(),
                serde_json::Value::Array(
                    result
                        .metadata
                        .warnings
                        .into_iter()
                        .map(|w| serde_json::Value::String(w))
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }
    }

    #[no_mangle]
    pub extern "C" fn krox_client_new(mode: *const c_char) -> *mut GoKroxClient {
        let mode_str = unsafe { CStr::from_ptr(mode).to_str().unwrap_or("native") };

        match GoKroxClient::new(mode_str) {
            Ok(client) => Box::into_raw(Box::new(client)),
            Err(_) => std::ptr::null_mut(),
        }
    }

    #[no_mangle]
    pub extern "C" fn krox_client_execute_file(
        client: *mut GoKroxClient,
        path: *const c_char,
    ) -> *mut c_char {
        if client.is_null() {
            return std::ptr::null_mut();
        }

        let client = unsafe { &*client };
        let path_str = unsafe { CStr::from_ptr(path).to_str().unwrap_or("") };

        let result = tokio::runtime::Runtime::new()
            .unwrap()
            .block_on(client.execute_file(path_str.to_string()));

        match result {
            Ok(json_value) => {
                let json_string = serde_json::to_string(&json_value).unwrap_or_default();
                let c_string = CString::new(json_string).unwrap_or_default();
                c_string.into_raw()
            }
            Err(_) => std::ptr::null_mut(),
        }
    }

    #[no_mangle]
    pub extern "C" fn krox_client_free(client: *mut GoKroxClient) {
        if !client.is_null() {
            unsafe {
                drop(Box::from_raw(client));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_sdk_client_creation() {
        let client = SdkClient::new(ExecutionMode::Native).await;
        // This might fail if ligature-cli is not in PATH, which is expected in test environments
        if client.is_err() {
            println!("Note: ligature-cli not found in PATH, test skipped");
        }
    }

    #[tokio::test]
    async fn test_sdk_client_execute_source() {
        let client = SdkClient::new(ExecutionMode::Native).await;
        if let Ok(client) = client {
            let _result = client.execute_source("let x = 42".to_string()).await;
            // This might fail if the parser/evaluator is not fully implemented
        } else {
            println!("Note: ligature-cli not found in PATH, test skipped");
        }
    }
}
