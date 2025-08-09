use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;
use ligature_ast::DeclarationKind;
use ligature_error::{ErrorReportConfig, StandardError, StandardErrorReporter};
use ligature_parser::Declaration;

#[derive(Parser)]
#[command(name = "cacophony")]
#[command(about = "Configuration management tool for Ligature")]
struct Cli {
    #[arg(short, long)]
    file: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,

    #[arg(short, long)]
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
        Ok(config) => {
            if verbose {
                println!("Configuration processed successfully:");
                println!("  File: {}", file.display());
                println!("  Size: {} bytes", source.len());
                println!("  Validated: {}", validate);
            } else {
                println!("✓ Configuration processed successfully");
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
            Ok(_) => {
                if verbose {
                    println!("✓ Line processed successfully");
                }
            }
            Err(e) => {
                if verbose {
                    eprintln!("Error: {:?}", e);
                } else {
                    eprintln!("Error: {}", e);
                }
            }
        }

        buffer.clear();
    }

    Ok(())
}

fn process_configuration(source: &str, file: &std::path::Path, validate: bool) -> Result<()> {
    // Parse configuration with error context
    let mut parser = ligature_parser::Parser::new();
    let program = parser
        .parse_program(source)
        .with_context(|| format!("Failed to parse configuration from {}", file.display()))?;

    if validate {
        // Validate configuration with error context
        validate_configuration(&program).with_context(|| "Configuration validation failed")?;
    }

    // Apply configuration with error context
    apply_configuration(&program).with_context(|| "Failed to apply configuration")?;

    Ok(())
}

fn validate_configuration(program: &ligature_parser::Program) -> Result<()> {
    // Simulate validation logic
    for decl in &program.declarations {
        validate_declaration(decl).with_context(|| format!("Failed to validate declaration"))?;
    }
    Ok(())
}

fn validate_declaration(decl: &Declaration) -> Result<()> {
    // Simulate declaration validation
    match &decl.kind {
        DeclarationKind::Value(value_decl) => {
            if value_decl.name.is_empty() {
                return Err(anyhow::anyhow!("Variable name cannot be empty"));
            }
        }
        _ => {}
    }
    Ok(())
}

fn apply_configuration(program: &ligature_parser::Program) -> Result<()> {
    // Simulate configuration application
    for decl in &program.declarations {
        apply_declaration(decl).with_context(|| "Failed to apply declaration")?;
    }
    Ok(())
}

fn apply_declaration(decl: &Declaration) -> Result<()> {
    // Simulate declaration application
    match &decl.kind {
        DeclarationKind::Value(value_decl) => {
            // In a real implementation, this would set the value in the environment
            println!("Setting {} = {:?}", value_decl.name, value_decl.value);
        }
        _ => {}
    }
    Ok(())
}
