use thiserror::Error;

#[derive(Error, Debug)]
pub enum CacophonyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("TOML deserialization error: {0}")]
    TomlDe(#[from] toml::de::Error),

    #[error("TOML serialization error: {0}")]
    TomlSer(#[from] toml::ser::Error),

    #[error("Not found: {0}")]
    NotFound(String),

    #[error("Validation error: {0}")]
    Validation(String),

    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Plugin error: {0}")]
    Plugin(String),

    #[error("Operation error: {0}")]
    Operation(String),

    // Additional error variants for the main crate
    #[error("Environment error: {0}")]
    Environment(String),

    #[error("Collection error: {0}")]
    Collection(String),

    #[error("YAML serialization error: {0}")]
    Yaml(String),

    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    #[error("Unsupported operation: {0}")]
    Unsupported(String),

    #[error("Internal error: {0}")]
    Internal(String),
}

impl From<anyhow::Error> for CacophonyError {
    fn from(err: anyhow::Error) -> Self {
        CacophonyError::Internal(err.to_string())
    }
}

pub type Result<T> = std::result::Result<T, CacophonyError>;
