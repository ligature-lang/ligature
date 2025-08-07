//! Utility functions and macros for the Baton client.

/// Debug logging macro
#[macro_export]
macro_rules! debug_log {
    ($config:expr, $($arg:tt)*) => {
        if $config.debug_logging {
            eprintln!("[ENGINE DEBUG] {}", format!($($arg)*));
        }
    };
}

/// Find engine executable in PATH.
pub fn find_engine_executable(engine_name: &str) -> crate::BatonResult<String> {
    use baton_error::BatonError;
    use std::process::Command;

    let possible_names = [
        engine_name.to_string(),
        format!("{engine_name}-4"),
        format!("{engine_name}-3"),
        format!("{engine_name}4"),
        format!("{engine_name}3"),
    ];

    for name in &possible_names {
        if let Ok(output) = Command::new(name).arg("--version").output() {
            if output.status.success() {
                return Ok(name.clone());
            }
        }
    }

    Err(BatonError::ConfigurationError(format!(
        "Could not find {engine_name} executable in PATH"
    )))
}

/// Find specification path.
pub fn find_specification_path(engine_name: &str) -> crate::BatonResult<String> {
    use baton_error::BatonError;

    let possible_paths = [
        format!("./{engine_name}-spec"),
        format!("./spec/{engine_name}"),
        format!("./specifications/{engine_name}"),
        "./spec".to_string(),
        "./specifications".to_string(),
    ];

    for path in &possible_paths {
        if std::path::Path::new(path).exists() {
            return Ok(path.clone());
        }
    }

    // Create default specification directory
    let default_path = format!("./{engine_name}-spec");
    std::fs::create_dir_all(&default_path).map_err(|e| {
        BatonError::FileSystemError(format!("Failed to create spec directory: {e}"))
    })?;

    Ok(default_path)
}
