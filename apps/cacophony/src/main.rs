use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;
use ligature_ast::DeclarationKind;
use ligature_error::{ErrorReportConfig, StandardError, StandardErrorReporter};
use ligature_eval::value::ValueKind;
use ligature_eval::{Evaluator, Value};
use ligature_parser::Declaration;

/// Type alias for configuration values
type ConfigValues = Vec<(String, Value)>;

#[derive(Parser)]
#[command(name = "cacophony")]
#[command(about = "Configuration management tool for Ligature")]
struct Cli {
    #[arg(short, long)]
    file: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,

    #[arg(long)]
    validate: bool,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(file) = cli.file {
        process_file(&file, cli.verbose, cli.validate)
    } else {
        process_stdin(cli.verbose, cli.validate)
    }
}

fn process_file(file: &PathBuf, verbose: bool, validate: bool) -> Result<()> {
    // Read file with context
    let source = std::fs::read_to_string(file)
        .with_context(|| format!("Failed to read file: {}", file.display()))?;

    // Process the configuration
    let result = process_configuration(&source, file, validate);

    match result {
        Ok(config_values) => {
            if verbose {
                println!("Configuration processed successfully:");
                println!("  File: {}", file.display());
                println!("  Size: {} bytes", source.len());
                println!("  Validated: {validate}");
                println!("  Configuration values:");
                for (name, value) in &config_values {
                    println!("    {name} = {value:?}");
                }
            } else {
                println!("✓ Configuration processed successfully");
                println!("  Found {} configuration values", config_values.len());
            }
            Ok(())
        }
        Err(e) => {
            // Use the new standardized error reporter
            let mut reporter = StandardErrorReporter::with_source_and_config(
                source,
                ErrorReportConfig {
                    show_source: true,
                    show_suggestions: true,
                    show_error_codes: true,
                    show_categories: true,
                    color_output: true,
                    max_errors: 10,
                    show_metadata: false,
                    group_by_category: true,
                },
            );

            // Convert anyhow error to standard error
            let standard_error = StandardError::internal_error(e.to_string());
            reporter.add_error(standard_error);

            eprintln!("{}", reporter.report());
            Err(e)
        }
    }
}

fn process_stdin(verbose: bool, validate: bool) -> Result<()> {
    use std::io::{self, BufRead};

    let stdin = io::stdin();
    let mut handle = stdin.lock();
    let mut buffer = String::new();

    while handle.read_line(&mut buffer)? > 0 {
        let result = process_configuration(&buffer, PathBuf::from("<stdin>").as_path(), validate);

        match result {
            Ok(config_values) => {
                if verbose {
                    println!("✓ Line processed successfully");
                    for (name, value) in &config_values {
                        println!("  {name} = {value:?}");
                    }
                }
            }
            Err(e) => {
                if verbose {
                    eprintln!("Error: {e:?}");
                } else {
                    eprintln!("Error: {e}");
                }
            }
        }

        buffer.clear();
    }

    Ok(())
}

fn process_configuration(
    source: &str,
    file: &std::path::Path,
    validate: bool,
) -> Result<ConfigValues> {
    // Parse configuration with error context
    let mut parser = ligature_parser::Parser::new();
    let program = parser
        .parse_program(source)
        .with_context(|| format!("Failed to parse configuration from {}", file.display()))?;

    if validate {
        // Validate configuration with error context
        validate_configuration(&program).with_context(|| "Configuration validation failed")?;
    }

    // Apply configuration using the evaluator and extract values
    let config_values =
        apply_configuration(&program).with_context(|| "Failed to apply configuration")?;

    Ok(config_values)
}

fn validate_configuration(program: &ligature_parser::Program) -> Result<()> {
    // Validate each declaration
    for decl in &program.declarations {
        validate_declaration(decl).with_context(|| "Failed to validate declaration".to_string())?;
    }
    Ok(())
}

fn validate_declaration(decl: &Declaration) -> Result<()> {
    // Validate declaration structure
    match &decl.kind {
        DeclarationKind::Value(value_decl) => {
            if value_decl.name.is_empty() {
                return Err(anyhow::anyhow!("Variable name cannot be empty"));
            }
            // Additional validation could be added here (type checking, etc.)
        }
        _ => {
            // For now, we only process value declarations as configuration
            // Other declaration types are ignored
        }
    }
    Ok(())
}

fn apply_configuration(program: &ligature_parser::Program) -> Result<ConfigValues> {
    // Create a new evaluator
    let mut evaluator = Evaluator::new();

    // Evaluate the program - this will populate the evaluator's environment
    evaluator
        .evaluate_program(program)
        .with_context(|| "Failed to evaluate configuration program")?;

    // Extract configuration values from the evaluator's environment
    let config_values = extract_configuration_values(&evaluator.environment);

    Ok(config_values)
}

fn extract_configuration_values(
    environment: &ligature_eval::EvaluationEnvironment,
) -> ConfigValues {
    let mut config_values = Vec::new();

    // Get all bindings from the environment
    let bindings = environment.current_bindings();

    for (name, value) in bindings {
        // Only include values that are not functions or modules (i.e., actual configuration data)
        if !is_function_or_module(value) {
            config_values.push((name.clone(), value.clone()));
        }
    }

    config_values
}

fn is_function_or_module(value: &Value) -> bool {
    matches!(
        &value.kind,
        ValueKind::Function { .. } | ValueKind::Closure { .. } | ValueKind::Module { .. }
    )
}
