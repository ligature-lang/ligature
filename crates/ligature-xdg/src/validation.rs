use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ValidationError {
    #[error("Schema validation error: {0}")]
    SchemaError(String),
    #[error("Constraint violation: {0}")]
    ConstraintViolation(String),
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },
    #[error("Required field missing: {field}")]
    MissingRequiredField { field: String },
    #[error("Invalid value for field {field}: {value}")]
    InvalidValue { field: String, value: String },
    #[error("File not found: {path}")]
    FileNotFound { path: PathBuf },
    #[error("Permission denied: {path}")]
    PermissionDenied { path: PathBuf },
    #[error("Circular dependency detected: {cycle}")]
    CircularDependency { cycle: String },
}

pub type ValidationResult<T> = std::result::Result<T, ValidationError>;

/// Configuration schema definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigSchema {
    pub fields: HashMap<String, FieldSchema>,
    pub required_fields: Vec<String>,
    pub optional_fields: Vec<String>,
    pub dependencies: HashMap<String, Vec<String>>,
    pub constraints: Vec<Constraint>,
}

/// Field schema definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldSchema {
    pub field_type: FieldType,
    pub required: bool,
    pub default: Option<serde_json::Value>,
    pub description: Option<String>,
    pub constraints: Vec<FieldConstraint>,
    pub allowed_values: Option<Vec<serde_json::Value>>,
    pub pattern: Option<String>,
    pub min_value: Option<f64>,
    pub max_value: Option<f64>,
    pub min_length: Option<usize>,
    pub max_length: Option<usize>,
}

/// Field type enumeration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FieldType {
    String,
    Integer,
    Float,
    Boolean,
    Object,
    Array,
    File,
    Directory,
    Url,
    Email,
    IpAddress,
    Port,
    Duration,
    Size,
}

/// Field constraint types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FieldConstraint {
    Required,
    Optional,
    MinValue(f64),
    MaxValue(f64),
    MinLength(usize),
    MaxLength(usize),
    Pattern(String),
    AllowedValues(Vec<serde_json::Value>),
    FileExists,
    DirectoryExists,
    ValidUrl,
    ValidEmail,
    ValidIpAddress,
    ValidPort,
    ValidDuration,
    ValidSize,
    Custom(String),
}

/// Global constraint types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Constraint {
    NoCircularDependencies,
    AllFilesExist,
    AllDirectoriesExist,
    ValidNetworkConfig,
    ValidSecurityConfig,
    Custom(String),
}

/// Type alias for custom validator functions
type CustomValidator = Box<dyn Fn(&serde_json::Value) -> ValidationResult<()> + Send + Sync>;

/// Configuration validator
pub struct ConfigValidator {
    schemas: HashMap<String, ConfigSchema>,
    custom_validators: HashMap<String, CustomValidator>,
}

impl ConfigValidator {
    /// Create a new configuration validator
    pub fn new() -> Self {
        Self {
            schemas: HashMap::new(),
            custom_validators: HashMap::new(),
        }
    }

    /// Register a schema for a configuration type
    pub fn register_schema(&mut self, name: &str, schema: ConfigSchema) {
        self.schemas.insert(name.to_string(), schema);
    }

    /// Register a custom validator function
    pub fn register_custom_validator<F>(&mut self, name: &str, validator: F)
    where
        F: Fn(&serde_json::Value) -> ValidationResult<()> + Send + Sync + 'static,
    {
        self.custom_validators
            .insert(name.to_string(), Box::new(validator));
    }

    /// Validate a configuration against a schema
    pub fn validate_config(
        &self,
        config: &serde_json::Value,
        schema_name: &str,
    ) -> ValidationResult<()> {
        let schema = self.schemas.get(schema_name).ok_or_else(|| {
            ValidationError::SchemaError(format!("Schema '{schema_name}' not found"))
        })?;

        // Validate required fields
        for field_name in &schema.required_fields {
            if config.get(field_name).is_none() {
                return Err(ValidationError::MissingRequiredField {
                    field: field_name.clone(),
                });
            }
        }

        // Validate each field
        for (field_name, field_schema) in &schema.fields {
            if let Some(field_value) = config.get(field_name) {
                self.validate_field(field_value, field_schema)?;
            } else if field_schema.required {
                return Err(ValidationError::MissingRequiredField {
                    field: field_name.clone(),
                });
            }
        }

        // Validate dependencies
        self.validate_dependencies(config, schema)?;

        // Validate global constraints
        self.validate_constraints(config, schema)?;

        Ok(())
    }

    /// Validate a single field
    fn validate_field(
        &self,
        value: &serde_json::Value,
        schema: &FieldSchema,
    ) -> ValidationResult<()> {
        // Check type
        self.validate_field_type(value, &schema.field_type)?;

        // Check constraints
        for constraint in &schema.constraints {
            self.validate_field_constraint(value, constraint)?;
        }

        // Check allowed values
        if let Some(ref allowed_values) = schema.allowed_values {
            if !allowed_values.contains(value) {
                return Err(ValidationError::InvalidValue {
                    field: "unknown".to_string(),
                    value: value.to_string(),
                });
            }
        }

        // Check pattern
        if let Some(ref pattern) = schema.pattern {
            if let Some(s) = value.as_str() {
                let regex = regex::Regex::new(pattern).map_err(|e| {
                    ValidationError::SchemaError(format!("Invalid regex pattern: {e}"))
                })?;
                if !regex.is_match(s) {
                    return Err(ValidationError::InvalidValue {
                        field: "unknown".to_string(),
                        value: s.to_string(),
                    });
                }
            }
        }

        // Check numeric constraints
        if let Some(min_val) = schema.min_value {
            if let Some(num) = value.as_f64() {
                if num < min_val {
                    return Err(ValidationError::ConstraintViolation(format!(
                        "Value {num} is less than minimum {min_val}",
                    )));
                }
            }
        }

        if let Some(max_val) = schema.max_value {
            if let Some(num) = value.as_f64() {
                if num > max_val {
                    return Err(ValidationError::ConstraintViolation(format!(
                        "Value {num} is greater than maximum {max_val}",
                    )));
                }
            }
        }

        // Check length constraints
        if let Some(min_len) = schema.min_length {
            if let Some(s) = value.as_str() {
                if s.len() < min_len {
                    return Err(ValidationError::ConstraintViolation(format!(
                        "String length {} is less than minimum {}",
                        s.len(),
                        min_len
                    )));
                }
            }
        }

        if let Some(max_len) = schema.max_length {
            if let Some(s) = value.as_str() {
                if s.len() > max_len {
                    return Err(ValidationError::ConstraintViolation(format!(
                        "String length {} is greater than maximum {}",
                        s.len(),
                        max_len
                    )));
                }
            }
        }

        Ok(())
    }

    /// Validate field type
    fn validate_field_type(
        &self,
        value: &serde_json::Value,
        expected_type: &FieldType,
    ) -> ValidationResult<()> {
        match expected_type {
            FieldType::String => {
                if !value.is_string() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Integer => {
                if !value.is_i64() && !value.is_u64() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "integer".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Float => {
                if !value.is_f64() && !value.is_i64() && !value.is_u64() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "float".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Boolean => {
                if !value.is_boolean() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "boolean".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Object => {
                if !value.is_object() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "object".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Array => {
                if !value.is_array() {
                    return Err(ValidationError::TypeMismatch {
                        expected: "array".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::File => {
                if let Some(path) = value.as_str() {
                    if !std::path::Path::new(path).exists() {
                        return Err(ValidationError::FileNotFound {
                            path: PathBuf::from(path),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "file path string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Directory => {
                if let Some(path) = value.as_str() {
                    let path = std::path::Path::new(path);
                    if !path.exists() || !path.is_dir() {
                        return Err(ValidationError::FileNotFound {
                            path: path.to_path_buf(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "directory path string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Url => {
                if let Some(url) = value.as_str() {
                    if url::Url::parse(url).is_err() {
                        return Err(ValidationError::InvalidValue {
                            field: "url".to_string(),
                            value: url.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "url string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Email => {
                if let Some(email) = value.as_str() {
                    if !self.is_valid_email(email) {
                        return Err(ValidationError::InvalidValue {
                            field: "email".to_string(),
                            value: email.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "email string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::IpAddress => {
                if let Some(ip) = value.as_str() {
                    if !self.is_valid_ip_address(ip) {
                        return Err(ValidationError::InvalidValue {
                            field: "ip address".to_string(),
                            value: ip.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "ip address string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Port => {
                if let Some(port) = value.as_u64() {
                    if port > 65535 {
                        return Err(ValidationError::InvalidValue {
                            field: "port".to_string(),
                            value: port.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "port number".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Duration => {
                if let Some(duration) = value.as_str() {
                    if !self.is_valid_duration(duration) {
                        return Err(ValidationError::InvalidValue {
                            field: "duration".to_string(),
                            value: duration.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "duration string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
            FieldType::Size => {
                if let Some(size) = value.as_str() {
                    if !self.is_valid_size(size) {
                        return Err(ValidationError::InvalidValue {
                            field: "size".to_string(),
                            value: size.to_string(),
                        });
                    }
                } else {
                    return Err(ValidationError::TypeMismatch {
                        expected: "size string".to_string(),
                        actual: self.get_value_type(value),
                    });
                }
            }
        }
        Ok(())
    }

    /// Validate field constraint
    fn validate_field_constraint(
        &self,
        value: &serde_json::Value,
        constraint: &FieldConstraint,
    ) -> ValidationResult<()> {
        match constraint {
            FieldConstraint::Required => {
                if value.is_null() {
                    return Err(ValidationError::ConstraintViolation(
                        "Field is required".to_string(),
                    ));
                }
            }
            FieldConstraint::Optional => {
                // Optional fields can be null or missing
            }
            FieldConstraint::MinValue(min) => {
                if let Some(num) = value.as_f64() {
                    if num < *min {
                        return Err(ValidationError::ConstraintViolation(format!(
                            "Value {num} is less than minimum {min}",
                        )));
                    }
                }
            }
            FieldConstraint::MaxValue(max) => {
                if let Some(num) = value.as_f64() {
                    if num > *max {
                        return Err(ValidationError::ConstraintViolation(format!(
                            "Value {num} is greater than maximum {max}",
                        )));
                    }
                }
            }
            FieldConstraint::MinLength(min) => {
                if let Some(s) = value.as_str() {
                    if s.len() < *min {
                        return Err(ValidationError::ConstraintViolation(format!(
                            "String length {} is less than minimum {min}",
                            s.len(),
                        )));
                    }
                }
            }
            FieldConstraint::MaxLength(max) => {
                if let Some(s) = value.as_str() {
                    if s.len() > *max {
                        return Err(ValidationError::ConstraintViolation(format!(
                            "String length {} is greater than maximum {max}",
                            s.len(),
                        )));
                    }
                }
            }
            FieldConstraint::Pattern(pattern) => {
                if let Some(s) = value.as_str() {
                    let regex = regex::Regex::new(pattern).map_err(|e| {
                        ValidationError::SchemaError(format!("Invalid regex pattern: {e}"))
                    })?;
                    if !regex.is_match(s) {
                        return Err(ValidationError::InvalidValue {
                            field: "pattern".to_string(),
                            value: s.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::AllowedValues(allowed) => {
                if !allowed.contains(value) {
                    return Err(ValidationError::InvalidValue {
                        field: "allowed values".to_string(),
                        value: value.to_string(),
                    });
                }
            }
            FieldConstraint::FileExists => {
                if let Some(path) = value.as_str() {
                    if !std::path::Path::new(path).exists() {
                        return Err(ValidationError::FileNotFound {
                            path: PathBuf::from(path),
                        });
                    }
                }
            }
            FieldConstraint::DirectoryExists => {
                if let Some(path) = value.as_str() {
                    let path = std::path::Path::new(path);
                    if !path.exists() || !path.is_dir() {
                        return Err(ValidationError::FileNotFound {
                            path: path.to_path_buf(),
                        });
                    }
                }
            }
            FieldConstraint::ValidUrl => {
                if let Some(url) = value.as_str() {
                    if url::Url::parse(url).is_err() {
                        return Err(ValidationError::InvalidValue {
                            field: "url".to_string(),
                            value: url.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::ValidEmail => {
                if let Some(email) = value.as_str() {
                    if !self.is_valid_email(email) {
                        return Err(ValidationError::InvalidValue {
                            field: "email".to_string(),
                            value: email.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::ValidIpAddress => {
                if let Some(ip) = value.as_str() {
                    if !self.is_valid_ip_address(ip) {
                        return Err(ValidationError::InvalidValue {
                            field: "ip address".to_string(),
                            value: ip.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::ValidPort => {
                if let Some(port) = value.as_u64() {
                    if port > 65535 {
                        return Err(ValidationError::InvalidValue {
                            field: "port".to_string(),
                            value: port.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::ValidDuration => {
                if let Some(duration) = value.as_str() {
                    if !self.is_valid_duration(duration) {
                        return Err(ValidationError::InvalidValue {
                            field: "duration".to_string(),
                            value: duration.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::ValidSize => {
                if let Some(size) = value.as_str() {
                    if !self.is_valid_size(size) {
                        return Err(ValidationError::InvalidValue {
                            field: "size".to_string(),
                            value: size.to_string(),
                        });
                    }
                }
            }
            FieldConstraint::Custom(name) => {
                if let Some(validator) = self.custom_validators.get(name) {
                    validator(value)?;
                }
            }
        }
        Ok(())
    }

    /// Validate dependencies
    fn validate_dependencies(
        &self,
        config: &serde_json::Value,
        schema: &ConfigSchema,
    ) -> ValidationResult<()> {
        for (field, dependencies) in &schema.dependencies {
            if config.get(field).is_some() {
                for dep in dependencies {
                    if config.get(dep).is_none() {
                        return Err(ValidationError::ConstraintViolation(format!(
                            "Field '{field}' depends on '{dep}' which is missing",
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    /// Validate global constraints
    fn validate_constraints(
        &self,
        config: &serde_json::Value,
        schema: &ConfigSchema,
    ) -> ValidationResult<()> {
        for constraint in &schema.constraints {
            match constraint {
                Constraint::NoCircularDependencies => {
                    self.check_circular_dependencies(config)?;
                }
                Constraint::AllFilesExist => {
                    self.check_all_files_exist(config)?;
                }
                Constraint::AllDirectoriesExist => {
                    self.check_all_directories_exist(config)?;
                }
                Constraint::ValidNetworkConfig => {
                    self.validate_network_config(config)?;
                }
                Constraint::ValidSecurityConfig => {
                    self.validate_security_config(config)?;
                }
                Constraint::Custom(name) => {
                    if let Some(validator) = self.custom_validators.get(name) {
                        validator(config)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Helper methods for validation
    fn get_value_type(&self, value: &serde_json::Value) -> String {
        if value.is_string() {
            "string".to_string()
        } else if value.is_number() {
            "number".to_string()
        } else if value.is_boolean() {
            "boolean".to_string()
        } else if value.is_object() {
            "object".to_string()
        } else if value.is_array() {
            "array".to_string()
        } else if value.is_null() {
            "null".to_string()
        } else {
            "unknown".to_string()
        }
    }

    fn is_valid_email(&self, email: &str) -> bool {
        // Simple email validation - in production, use a proper email validation library
        email.contains('@') && email.contains('.') && email.len() > 5
    }

    fn is_valid_ip_address(&self, ip: &str) -> bool {
        // Simple IP validation - in production, use a proper IP validation library
        ip.parse::<std::net::IpAddr>().is_ok()
    }

    fn is_valid_duration(&self, duration: &str) -> bool {
        // Simple duration validation - in production, use a proper duration parsing library
        duration
            .chars()
            .all(|c| c.is_ascii_digit() || c == 's' || c == 'm' || c == 'h' || c == 'd')
    }

    fn is_valid_size(&self, size: &str) -> bool {
        // Simple size validation - in production, use a proper size parsing library
        size.chars()
            .all(|c| c.is_ascii_digit() || c == 'B' || c == 'K' || c == 'M' || c == 'G')
    }

    fn check_circular_dependencies(&self, _config: &serde_json::Value) -> ValidationResult<()> {
        // Implementation for checking circular dependencies
        // This would analyze the configuration structure for circular references
        Ok(())
    }

    fn check_all_files_exist(&self, _config: &serde_json::Value) -> ValidationResult<()> {
        // Implementation for checking if all referenced files exist
        // This would recursively traverse the config and check file paths
        Ok(())
    }

    fn check_all_directories_exist(&self, _config: &serde_json::Value) -> ValidationResult<()> {
        // Implementation for checking if all referenced directories exist
        // This would recursively traverse the config and check directory paths
        Ok(())
    }

    fn validate_network_config(&self, _config: &serde_json::Value) -> ValidationResult<()> {
        // Implementation for validating network configuration
        // This would check for valid URLs, ports, IP addresses, etc.
        Ok(())
    }

    fn validate_security_config(&self, _config: &serde_json::Value) -> ValidationResult<()> {
        // Implementation for validating security configuration
        // This would check for secure settings, valid certificates, etc.
        Ok(())
    }
}

impl Default for ConfigValidator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_validation() {
        let mut validator = ConfigValidator::new();

        let schema = ConfigSchema {
            fields: {
                let mut fields = HashMap::new();
                fields.insert(
                    "name".to_string(),
                    FieldSchema {
                        field_type: FieldType::String,
                        required: true,
                        default: None,
                        description: Some("Application name".to_string()),
                        constraints: vec![
                            FieldConstraint::MinLength(1),
                            FieldConstraint::MaxLength(100),
                        ],
                        allowed_values: None,
                        pattern: None,
                        min_value: None,
                        max_value: None,
                        min_length: Some(1),
                        max_length: Some(100),
                    },
                );
                fields.insert(
                    "port".to_string(),
                    FieldSchema {
                        field_type: FieldType::Port,
                        required: false,
                        default: Some(serde_json::Value::Number(8080.into())),
                        description: Some("Server port".to_string()),
                        constraints: vec![
                            FieldConstraint::MinValue(1.0),
                            FieldConstraint::MaxValue(65535.0),
                        ],
                        allowed_values: None,
                        pattern: None,
                        min_value: Some(1.0),
                        max_value: Some(65535.0),
                        min_length: None,
                        max_length: None,
                    },
                );
                fields
            },
            required_fields: vec!["name".to_string()],
            optional_fields: vec!["port".to_string()],
            dependencies: HashMap::new(),
            constraints: vec![],
        };

        validator.register_schema("app", schema);

        // Valid configuration
        let valid_config = serde_json::json!({
            "name": "test-app",
            "port": 3000
        });
        assert!(validator.validate_config(&valid_config, "app").is_ok());

        // Invalid configuration - missing required field
        let invalid_config = serde_json::json!({
            "port": 3000
        });
        assert!(validator.validate_config(&invalid_config, "app").is_err());

        // Invalid configuration - invalid port
        let invalid_config = serde_json::json!({
            "name": "test-app",
            "port": 70000
        });
        assert!(validator.validate_config(&invalid_config, "app").is_err());
    }
}
