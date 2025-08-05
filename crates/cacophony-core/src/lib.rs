pub mod config;
pub mod error;
pub mod traits;
pub mod types;

pub use config::{
    CacophonyConfig, CollectionConfig, EnvironmentConfig, OperationConfig, PluginConfig,
    ProjectConfig,
};
pub use error::{CacophonyError, Result};
pub use traits::{Operation, OperationResult, Plugin, ValidationResult};
pub use types::{Collection, Environment, LigatureProgram};

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_ligature_program_creation() {
        let program = LigatureProgram::new(
            "test".to_string(),
            "content".to_string(),
            std::path::PathBuf::from("test.lig"),
        );
        assert_eq!(program.name, "test");
        assert_eq!(program.content, "content");
    }

    #[test]
    fn test_environment_variable_access() {
        let mut env = Environment {
            name: "test".to_string(),
            description: None,
            variables: HashMap::new(),
            plugins: Vec::new(),
            overrides: None,
        };
        env.variables
            .insert("TEST_VAR".to_string(), "test_value".to_string());

        assert_eq!(
            env.get_variable("TEST_VAR"),
            Some(&"test_value".to_string())
        );
        assert_eq!(env.get_variable("NONEXISTENT"), None);
    }
}
