//! Basic usage example for the baton-engine-plugin crate.
//!
//! This example demonstrates how to create and use a simple verification engine plugin.

use baton_engine_plugin::prelude::*;
use baton_engine_plugin::traits::{EngineStats, EngineHealthStatus};
use async_trait::async_trait;
use serde_json::json;

/// A simple mock verification engine
struct MockEngine {
    name: String,
    version: String,
}

impl MockEngine {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            version: "1.0.0".to_string(),
        }
    }
}

#[async_trait]
impl VerificationEngine for MockEngine {
    async fn verify_evaluation(
        &self,
        expression: &str,
        expected_value: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        // Simple mock implementation
        let result = if expression == "1 + 1" && expected_value == "2" {
            LeanResponse::VerificationSuccess {
                result: "2".to_string(),
                proof: Some("Simple arithmetic".to_string()),
                proof_steps: Some(vec!["1 + 1 = 2".to_string()]),
                execution_time: Some(10),
            }
        } else {
            LeanResponse::VerificationFailure {
                error: format!("Mock engine cannot verify {} = {}", expression, expected_value),
                details: None,
                error_type: Some(ErrorType::Semantics),
                suggestions: Some(vec!["Try a simpler expression".to_string()]),
            }
        };

        Ok(VerificationResponse::new(result, 10))
    }

    async fn verify_type_check(
        &self,
        _expression: &str,
        _expected_type: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Type checking not implemented".to_string()))
    }

    async fn verify_operational_semantics(
        &self,
        _expression: &str,
        _expected_steps: &[String],
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Operational semantics not implemented".to_string()))
    }

    async fn verify_type_safety(
        &self,
        _expression: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Type safety not implemented".to_string()))
    }

    async fn verify_termination(
        &self,
        _expression: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Termination not implemented".to_string()))
    }

    async fn verify_determinism(
        &self,
        _expression: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Determinism not implemented".to_string()))
    }

    async fn verify_theorem(
        &self,
        _theorem: &str,
        _proof: Option<&str>,
        _timeout: Option<u64>,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Theorem verification not implemented".to_string()))
    }

    async fn verify_lemma(
        &self,
        _lemma: &str,
        _proof: Option<&str>,
        _dependencies: &[String],
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Lemma verification not implemented".to_string()))
    }

    async fn verify_invariant(
        &self,
        _invariant: &str,
        _expression: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Invariant verification not implemented".to_string()))
    }

    async fn verify_refinement(
        &self,
        _abstract_spec: &str,
        _concrete_spec: &str,
        _refinement_relation: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Refinement verification not implemented".to_string()))
    }

    async fn run_differential_test(
        &self,
        _test_case: &str,
        _test_type: DifferentialTestType,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Differential testing not implemented".to_string()))
    }

    async fn extract_test_cases(
        &self,
        _specification_file: &str,
        _test_type: Option<TestType>,
    ) -> BatonResult<Vec<String>> {
        Err(BatonError::InternalError("Test extraction not implemented".to_string()))
    }

    async fn check_specification(
        &self,
        _specification_file: &str,
        _check_type: SpecificationCheckType,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Specification checking not implemented".to_string()))
    }

    async fn check_consistency(
        &self,
        _specification_files: &[String],
        _check_type: ConsistencyCheckType,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Consistency checking not implemented".to_string()))
    }

    async fn generate_counterexample(
        &self,
        _property: &str,
        _context: Option<VerificationContext>,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Counterexample generation not implemented".to_string()))
    }

    async fn compare_results(
        &self,
        _rust_result: &str,
        _lean_result: &str,
        _comparison_type: ComparisonType,
    ) -> BatonResult<VerificationResponse> {
        Err(BatonError::InternalError("Result comparison not implemented".to_string()))
    }

    async fn get_version(&self) -> BatonResult<String> {
        Ok(self.version.clone())
    }

    async fn ping(&self) -> BatonResult<bool> {
        Ok(true)
    }

    fn get_stats(&self) -> EngineStats {
        EngineStats::default()
    }

    async fn get_health_status(&self) -> BatonResult<EngineHealthStatus> {
        Ok(EngineHealthStatus::default())
    }
}

/// A simple mock plugin
struct MockPlugin {
    name: String,
    engine: Option<MockEngine>,
    initialized: bool,
}

impl MockPlugin {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            engine: None,
            initialized: false,
        }
    }
}

#[async_trait]
impl EnginePlugin for MockPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        "1.0.0"
    }

    fn description(&self) -> &str {
        "A simple mock verification engine for demonstration"
    }

    fn engine_info(&self) -> EngineInfo {
        EngineInfo {
            name: self.name.clone(),
            version: "1.0.0".to_string(),
            description: "Mock verification engine".to_string(),
            vendor: "Example".to_string(),
            homepage: Some("https://example.com".to_string()),
            documentation: None,
            license: Some("MIT".to_string()),
            supported_languages: vec!["rust".to_string()],
            supported_features: vec!["evaluation".to_string()],
            config_schema: None,
        }
    }

    fn capabilities(&self) -> EngineCapabilities {
        EngineCapabilities {
            supports_evaluation: true,
            supports_type_checking: false,
            supports_theorem_verification: false,
            supports_differential_testing: false,
            supports_result_comparison: false,
            ..Default::default()
        }
    }

    async fn initialize(&mut self, _config: &serde_json::Value) -> BatonResult<()> {
        self.engine = Some(MockEngine::new(&self.name));
        self.initialized = true;
        Ok(())
    }

    async fn shutdown(&mut self) -> BatonResult<()> {
        self.engine = None;
        self.initialized = false;
        Ok(())
    }

    async fn status(&self) -> BatonResult<EngineStatus> {
        if self.initialized {
            Ok(EngineStatus::Ready)
        } else {
            Ok(EngineStatus::Uninitialized)
        }
    }

    async fn configure(&mut self, _config: &serde_json::Value) -> BatonResult<()> {
        Ok(())
    }

    fn get_engine(&self) -> BatonResult<Box<dyn VerificationEngine>> {
        if let Some(ref engine) = self.engine {
            Ok(Box::new(engine.clone()))
        } else {
            Err(BatonError::InternalError("Engine not initialized".to_string()))
        }
    }
}

impl Clone for MockEngine {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            version: self.version.clone(),
        }
    }
}

#[tokio::main]
async fn main() -> BatonResult<()> {
    println!("=== Baton Engine Plugin Example ===\n");

    // Create a plugin manager
    let manager = EnginePluginManager::new();
    println!("Created plugin manager");

    // Create and register a mock plugin
    let mock_plugin = MockPlugin::new("mock-engine");
    manager.register_plugin(Box::new(mock_plugin)).await?;
    println!("Registered mock plugin");

    // Initialize the plugin
    let config = json!({
        "timeout": 30,
        "memory_limit": 1024
    });
    manager.initialize_plugin("mock-engine", &config).await?;
    println!("Initialized mock plugin");

    // Get plugin information
    let info = manager.get_plugin_info("mock-engine").await?;
    println!("Plugin info: {:?}", info);

    // Get plugin capabilities
    let capabilities = manager.get_plugin_capabilities("mock-engine").await?;
    println!("Plugin capabilities: {:?}", capabilities);

    // Get plugin status
    let status = manager.get_plugin_status("mock-engine").await?;
    println!("Plugin status: {:?}", status);

    // List all plugins
    let plugins = manager.list_plugins().await;
    println!("Registered plugins: {:?}", plugins);

    // Get manager statistics
    let stats = manager.get_stats().await;
    println!("Manager stats: {:?}", stats);

    // Note: The current implementation doesn't support engine cloning,
    // so we can't demonstrate actual verification usage yet.
    // This would be implemented in a future version.
    println!("\nNote: Engine usage demonstration requires engine cloning support");

    // Health check
    let health = manager.health_check().await;
    println!("Health status: {:?}", health);

    // Shutdown
    manager.shutdown_all().await?;
    println!("Shutdown complete");

    println!("\n=== Example completed successfully ===");
    Ok(())
} 