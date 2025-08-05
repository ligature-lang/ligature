use crate::error::Result;
use crate::types::{Collection, Environment};
use async_trait::async_trait;
use serde_json::Value;
use std::collections::HashMap;

#[async_trait]
pub trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn description(&self) -> &str;
    fn operations(&self) -> Vec<Box<dyn Operation>>;
    fn configure(&mut self, config: &Value) -> Result<()>;
}

#[async_trait]
pub trait Operation: Send + Sync {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    async fn execute(
        &self,
        collection: &Collection,
        environment: &Environment,
    ) -> Result<OperationResult>;
    fn validate(
        &self,
        collection: &Collection,
        environment: &Environment,
    ) -> Result<ValidationResult>;
}

#[derive(Debug)]
pub struct OperationResult {
    pub success: bool,
    pub message: String,
    pub details: HashMap<String, Value>,
    pub duration: std::time::Duration,
}

#[derive(Debug)]
pub struct ValidationResult {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}
