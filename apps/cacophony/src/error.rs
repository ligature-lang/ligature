use thiserror::Error;

#[derive(Error, Debug)]
pub enum CacophonyError {
    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Environment error: {0}")]
    Environment(String),

    #[error("Collection error: {0}")]
    Collection(String),

    #[error("Operation error: {0}")]
    Operation(String),

    #[error("Plugin error: {0}")]
    Plugin(String),

    #[error("File I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON serialization error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("TOML serialization error: {0}")]
    Toml(#[from] toml::de::Error),

    #[error("YAML serialization error: {0}")]
    Yaml(String),

    #[error("Validation error: {0}")]
    Validation(String),

    #[error("Not found: {0}")]
    NotFound(String),

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
