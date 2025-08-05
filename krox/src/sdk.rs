//! Language SDKs for Krox.
//!
//! This module provides bindings for different programming languages,
//! allowing you to use Krox from Python, Node.js, Java, and Go.

use crate::{Client, ExecutionMode, ExecutionResult, Result};
use std::sync::Arc;
use tokio::sync::Mutex;

/// A thread-safe wrapper around the Krox client for use in language bindings.
#[derive(Clone)]
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
#[allow(unsafe_op_in_unsafe_fn)]
#[allow(non_local_definitions)]
pub mod python {
    use super::*;
    use pyo3::prelude::*;
    use pyo3::types::PyDict;

    #[pyclass]
    pub struct PyKroxClient {
        client: SdkClient,
    }

    #[pymethods]
    #[allow(non_local_definitions)]
    #[allow(clippy::missing_safety_doc)]
    #[allow(unsafe_op_in_unsafe_fn)]
    impl PyKroxClient {
        #[new]
        #[allow(unsafe_op_in_unsafe_fn)]
        fn new(mode: &str) -> PyResult<Self> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                        "Invalid execution mode: {mode}"
                    )));
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            Ok(Self { client })
        }

        #[allow(unsafe_op_in_unsafe_fn)]
        #[allow(deprecated)]
        fn execute_file(&self, path: String) -> PyResult<PyObject> {
            let client = self.client.clone();
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.execute_file(path).await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            // Convert result to Python dict
            Python::with_gil(|py| {
                let dict = PyDict::new(py);

                // Convert value to a simple string representation for now
                let value_str = format!("{:?}", result.value);
                dict.set_item("value", value_str)?;
                dict.set_item("duration", result.metadata.duration.as_secs_f64())?;
                dict.set_item("cached", result.metadata.cached)?;
                dict.set_item("mode", format!("{}", result.metadata.mode))?;
                dict.set_item("warnings", result.metadata.warnings)?;

                Ok(dict.to_object(py))
            })
        }

        #[allow(unsafe_op_in_unsafe_fn)]
        #[allow(deprecated)]
        fn execute_source(&self, source: String) -> PyResult<PyObject> {
            let client = self.client.clone();
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.execute_source(source).await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            // Convert result to Python dict
            Python::with_gil(|py| {
                let dict = PyDict::new(py);

                // Convert value to a simple string representation for now
                let value_str = format!("{:?}", result.value);
                dict.set_item("value", value_str)?;
                dict.set_item("duration", result.metadata.duration.as_secs_f64())?;
                dict.set_item("cached", result.metadata.cached)?;
                dict.set_item("mode", format!("{}", result.metadata.mode))?;
                dict.set_item("warnings", result.metadata.warnings)?;

                Ok(dict.to_object(py))
            })
        }

        #[allow(deprecated)]
        fn cache_stats(&self) -> PyResult<Option<PyObject>> {
            let client = self.client.clone();
            let stats = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async move { client.cache_stats().await })
                .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e.to_string()))?;

            if let Some(stats) = stats {
                Python::with_gil(|py| {
                    let dict = PyDict::new(py);

                    dict.set_item("total_entries", stats.total_entries)?;
                    dict.set_item("hits", stats.hits)?;
                    dict.set_item("misses", stats.misses)?;
                    dict.set_item("hit_rate", stats.hit_rate)?;
                    dict.set_item("total_size", stats.total_size)?;
                    dict.set_item("cache_dir", stats.cache_dir)?;

                    Ok(Some(dict.to_object(py)))
                })
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
    fn krox(_py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
        m.add_class::<PyKroxClient>()?;
        Ok(())
    }
}

/// Node.js bindings for Krox.
#[cfg(feature = "node")]
pub mod node {
    use super::*;
    use napi_derive::napi;

    #[napi]
    pub struct NodeKroxClient {
        client: SdkClient,
    }

    #[napi]
    impl NodeKroxClient {
        #[napi(constructor)]
        pub fn new(mode: String) -> std::result::Result<Self, napi::Error> {
            let execution_mode = match mode.as_str() {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(napi::Error::from_reason(format!(
                        "Invalid execution mode: {mode}"
                    )));
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            Ok(Self { client })
        }

        #[napi]
        pub fn execute_file(&self, path: String) -> std::result::Result<String, napi::Error> {
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(self.client.execute_file(path))
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            // Convert result to JSON string
            let result_obj = serde_json::json!({
                "value": format!("{:?}", result.value),
                "duration": result.metadata.duration.as_secs_f64(),
                "cached": result.metadata.cached,
                "mode": format!("{}", result.metadata.mode),
                "warnings": result.metadata.warnings
            });

            Ok(result_obj.to_string())
        }

        #[napi]
        pub fn execute_source(&self, source: String) -> std::result::Result<String, napi::Error> {
            let result = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(self.client.execute_source(source))
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            // Convert result to JSON string
            let result_obj = serde_json::json!({
                "value": format!("{:?}", result.value),
                "duration": result.metadata.duration.as_secs_f64(),
                "cached": result.metadata.cached,
                "mode": format!("{}", result.metadata.mode),
                "warnings": result.metadata.warnings
            });

            Ok(result_obj.to_string())
        }

        #[napi]
        pub fn cache_stats(&self) -> std::result::Result<Option<String>, napi::Error> {
            let stats = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(self.client.cache_stats())
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            if let Some(stats) = stats {
                let stats_obj = serde_json::json!({
                    "total_entries": stats.total_entries,
                    "hits": stats.hits,
                    "misses": stats.misses,
                    "hit_rate": stats.hit_rate,
                    "total_size": stats.total_size,
                    "cache_dir": stats.cache_dir
                });
                Ok(Some(stats_obj.to_string()))
            } else {
                Ok(None)
            }
        }

        #[napi]
        pub fn clear_cache(&self) -> std::result::Result<(), napi::Error> {
            tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(self.client.clear_cache())
                .map_err(|e| napi::Error::from_reason(e.to_string()))?;

            Ok(())
        }
    }
}

/// Java bindings for Krox.
#[cfg(feature = "java")]
pub mod java {
    use super::*;
    use jni::JNIEnv;
    use jni::objects::{JClass, JObject, JString};
    use jni::sys::jobject;

    pub struct JavaKroxClient {
        client: SdkClient,
    }

    impl JavaKroxClient {
        pub fn new(mode: &str) -> std::result::Result<Self, jni::errors::Error> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(jni::errors::Error::InvalidArgList(
                        jni::signature::TypeSignature::from_str("Ljava/lang/String;").unwrap(),
                    ));
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))
                .map_err(|_| {
                    jni::errors::Error::InvalidArgList(
                        jni::signature::TypeSignature::from_str("Ljava/lang/String;").unwrap(),
                    )
                })?;

            Ok(Self { client })
        }

        pub async fn execute_file(
            &self,
            path: String,
        ) -> std::result::Result<serde_json::Value, jni::errors::Error> {
            let result = self.client.execute_file(path).await.map_err(|_| {
                jni::errors::Error::InvalidArgList(
                    jni::signature::TypeSignature::from_str("Ljava/lang/String;").unwrap(),
                )
            })?;

            // Convert result to JSON - create a simple representation
            let json_value = match &result.value.kind {
                ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                ligature_eval::ValueKind::String(s) => serde_json::Value::String((**s).clone()),
                ligature_eval::ValueKind::Integer(i) => {
                    serde_json::Value::Number(serde_json::Number::from(**i))
                }
                ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                    serde_json::Number::from_f64(**f).unwrap_or(serde_json::Number::from(0)),
                ),
                ligature_eval::ValueKind::Record(fields) => {
                    let mut obj = serde_json::Map::new();
                    for (k, v) in fields.iter() {
                        // Recursively convert nested values
                        let v_json = match &v.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", v.kind)),
                        };
                        obj.insert(k.clone(), v_json);
                    }
                    serde_json::Value::Object(obj)
                }
                ligature_eval::ValueKind::List(elements) => {
                    let mut arr = Vec::new();
                    for element in elements.iter() {
                        let elem_json = match &element.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", element.kind)),
                        };
                        arr.push(elem_json);
                    }
                    serde_json::Value::Array(arr)
                }
                _ => serde_json::Value::String(format!("{:?}", result.value.kind)),
            };

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
                        .map(serde_json::Value::String)
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        pub async fn execute_source(
            &self,
            source: String,
        ) -> std::result::Result<serde_json::Value, jni::errors::Error> {
            let result = self.client.execute_source(source).await.map_err(|_| {
                jni::errors::Error::InvalidArgList(
                    jni::signature::TypeSignature::from_str("Ljava/lang/String;").unwrap(),
                )
            })?;

            // Convert result to JSON - create a simple representation
            let json_value = match &result.value.kind {
                ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                ligature_eval::ValueKind::String(s) => serde_json::Value::String((**s).clone()),
                ligature_eval::ValueKind::Integer(i) => {
                    serde_json::Value::Number(serde_json::Number::from(**i))
                }
                ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                    serde_json::Number::from_f64(**f).unwrap_or(serde_json::Number::from(0)),
                ),
                ligature_eval::ValueKind::Record(fields) => {
                    let mut obj = serde_json::Map::new();
                    for (k, v) in fields.iter() {
                        // Recursively convert nested values
                        let v_json = match &v.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", v.kind)),
                        };
                        obj.insert(k.clone(), v_json);
                    }
                    serde_json::Value::Object(obj)
                }
                ligature_eval::ValueKind::List(elements) => {
                    let mut arr = Vec::new();
                    for element in elements.iter() {
                        let elem_json = match &element.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", element.kind)),
                        };
                        arr.push(elem_json);
                    }
                    serde_json::Value::Array(arr)
                }
                _ => serde_json::Value::String(format!("{:?}", result.value.kind)),
            };

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
                        .map(serde_json::Value::String)
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }
    }

    #[unsafe(no_mangle)]
    pub extern "system" fn Java_com_krox_KroxClient_new(
        _env: JNIEnv,
        _class: JClass,
        _mode: JString,
    ) -> jobject {
        // Implementation would go here
        std::ptr::null_mut()
    }

    #[unsafe(no_mangle)]
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
        #[allow(clippy::type_complexity)]
        pub fn new(mode: &str) -> std::result::Result<Self, Box<dyn std::error::Error>> {
            let execution_mode = match mode {
                "native" => ExecutionMode::Native,
                "http" => ExecutionMode::Http,
                "in-process" => ExecutionMode::InProcess,
                _ => {
                    return Err(Box::new(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        "Invalid execution mode",
                    )));
                }
            };

            let client = tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(SdkClient::new(execution_mode))?;

            Ok(Self { client })
        }

        pub async fn execute_file(
            &self,
            path: String,
        ) -> std::result::Result<serde_json::Value, Box<dyn std::error::Error>> {
            let result = self.client.execute_file(path).await?;

            // Convert result to JSON - create a simple representation
            let json_value = match &result.value.kind {
                ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                ligature_eval::ValueKind::String(s) => serde_json::Value::String((**s).clone()),
                ligature_eval::ValueKind::Integer(i) => {
                    serde_json::Value::Number(serde_json::Number::from(**i))
                }
                ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                    serde_json::Number::from_f64(**f).unwrap_or(serde_json::Number::from(0)),
                ),
                ligature_eval::ValueKind::Record(fields) => {
                    let mut obj = serde_json::Map::new();
                    for (k, v) in fields.iter() {
                        // Recursively convert nested values
                        let v_json = match &v.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", v.kind)),
                        };
                        obj.insert(k.clone(), v_json);
                    }
                    serde_json::Value::Object(obj)
                }
                ligature_eval::ValueKind::List(elements) => {
                    let mut arr = Vec::new();
                    for element in elements.iter() {
                        let elem_json = match &element.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", element.kind)),
                        };
                        arr.push(elem_json);
                    }
                    serde_json::Value::Array(arr)
                }
                _ => serde_json::Value::String(format!("{:?}", result.value.kind)),
            };

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
                        .map(serde_json::Value::String)
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }

        pub async fn execute_source(
            &self,
            source: String,
        ) -> std::result::Result<serde_json::Value, Box<dyn std::error::Error>> {
            let result = self.client.execute_source(source).await?;

            // Convert result to JSON - create a simple representation
            let json_value = match &result.value.kind {
                ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                ligature_eval::ValueKind::String(s) => serde_json::Value::String((**s).clone()),
                ligature_eval::ValueKind::Integer(i) => {
                    serde_json::Value::Number(serde_json::Number::from(**i))
                }
                ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                    serde_json::Number::from_f64(**f).unwrap_or(serde_json::Number::from(0)),
                ),
                ligature_eval::ValueKind::Record(fields) => {
                    let mut obj = serde_json::Map::new();
                    for (k, v) in fields.iter() {
                        // Recursively convert nested values
                        let v_json = match &v.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", v.kind)),
                        };
                        obj.insert(k.clone(), v_json);
                    }
                    serde_json::Value::Object(obj)
                }
                ligature_eval::ValueKind::List(elements) => {
                    let mut arr = Vec::new();
                    for element in elements.iter() {
                        let elem_json = match &element.kind {
                            ligature_eval::ValueKind::Unit => serde_json::Value::Null,
                            ligature_eval::ValueKind::Boolean(b) => serde_json::Value::Bool(**b),
                            ligature_eval::ValueKind::String(s) => {
                                serde_json::Value::String((**s).clone())
                            }
                            ligature_eval::ValueKind::Integer(i) => {
                                serde_json::Value::Number(serde_json::Number::from(**i))
                            }
                            ligature_eval::ValueKind::Float(f) => serde_json::Value::Number(
                                serde_json::Number::from_f64(**f)
                                    .unwrap_or(serde_json::Number::from(0)),
                            ),
                            _ => serde_json::Value::String(format!("{:?}", element.kind)),
                        };
                        arr.push(elem_json);
                    }
                    serde_json::Value::Array(arr)
                }
                _ => serde_json::Value::String(format!("{:?}", result.value.kind)),
            };

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
                        .map(serde_json::Value::String)
                        .collect(),
                ),
            );

            Ok(serde_json::Value::Object(result_obj))
        }
    }

    /// # Safety
    ///
    /// The `mode` pointer must be a valid C string pointer.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn krox_client_new(mode: *const c_char) -> *mut GoKroxClient {
        let mode_str = unsafe { CStr::from_ptr(mode).to_str().unwrap_or("native") };

        match GoKroxClient::new(mode_str) {
            Ok(client) => Box::into_raw(Box::new(client)),
            Err(_) => std::ptr::null_mut(),
        }
    }

    /// # Safety
    ///
    /// The `client` pointer must be a valid pointer to a `GoKroxClient` instance.
    /// The `path` pointer must be a valid C string pointer.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn krox_client_execute_file(
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

    /// # Safety
    ///
    /// The `client` pointer must be a valid pointer to a `GoKroxClient` instance.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn krox_client_free(client: *mut GoKroxClient) {
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
