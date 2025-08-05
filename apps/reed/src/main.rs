// Copyright 2024 Ligature Language Team
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Command-line interface for the Ligature language.

use clap::{Parser, Subcommand};
use ligature_eval::Evaluator;
use ligature_parser::Parser as LigatureParser;
use ligature_types::type_check_program;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

mod xdg_config;
use xdg_config::xdg_config_for_cli;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse and validate a Ligature program
    Parse {
        /// Input file to parse
        #[arg(short, long)]
        file: String,
    },
    /// Type check a Ligature program
    Typecheck {
        /// Input file to type check
        #[arg(short, long)]
        file: String,
    },
    /// Evaluate a Ligature program
    Eval {
        /// Input file to evaluate
        #[arg(short, long)]
        file: String,
    },
    /// Run the complete pipeline (parse -> type check -> evaluate)
    Run {
        /// Input file to run
        #[arg(short, long)]
        file: String,
    },
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize XDG configuration
    let xdg_config = match xdg_config_for_cli().await {
        Ok(config) => {
            // Ensure XDG directories exist
            if let Err(e) = config.ensure_directories().await {
                eprintln!("Warning: Failed to ensure XDG directories: {e}");
            }
            Some(config)
        }
        Err(e) => {
            eprintln!("Warning: Failed to initialize XDG configuration: {e}");
            None
        }
    };

    let cli = Cli::parse();

    Ok(match &cli.command {
        Some(Commands::Parse { file }) => {
            let source = std::fs::read_to_string(file)?;

            // Use XDG configuration for output format if available
            let output_format = if let Some(ref config) = xdg_config {
                config
                    .output_format()
                    .await
                    .unwrap_or_else(|_| "text".to_string())
            } else {
                "text".to_string()
            };

            let mut parser = LigatureParser::new();
            match parser.parse_program(&source) {
                Ok(program) => {
                    println!("✓ Parsing successful");
                    println!("  Declarations: {}", program.declarations.len());

                    // Output in configured format
                    match output_format.as_str() {
                        "json" => {
                            println!("{}", serde_json::to_string_pretty(&program)?);
                        }
                        "yaml" => {
                            println!("{}", serde_yaml::to_string(&program)?);
                        }
                        _ => {
                            // Default text output
                            println!("Program structure:");
                            for (i, decl) in program.declarations.iter().enumerate() {
                                println!("  {}. {:?}", i + 1, decl.kind);
                            }
                        }
                    }
                    Ok(())
                }
                Err(e) => {
                    println!("✗ Parsing failed: {e:?}");
                    Err(Box::new(e))
                }
            }
        }
        Some(Commands::Typecheck { file }) => {
            let source = std::fs::read_to_string(file)?;
            let mut parser = LigatureParser::new();

            let program = parser.parse_program(&source)?;
            type_check_program(&program)?;

            // Use XDG configuration for verbose output if available
            let verbose = if let Some(ref config) = xdg_config {
                config.verbose_enabled().await.unwrap_or(false)
            } else {
                false
            };

            println!("✓ Type checking successful");

            if verbose {
                println!("  Program has {} declarations", program.declarations.len());
                println!("  All types are valid");
            }
            Ok(())
        }
        Some(Commands::Eval { file }) => {
            let source = std::fs::read_to_string(file)?;
            let mut parser = LigatureParser::new();
            let mut evaluator = Evaluator::new();

            let program = parser.parse_program(&source)?;
            let result = evaluator.evaluate_program(&program)?;

            // Use XDG configuration for output format if available
            let output_format = if let Some(ref config) = xdg_config {
                config
                    .output_format()
                    .await
                    .unwrap_or_else(|_| "text".to_string())
            } else {
                "text".to_string()
            };

            println!("✓ Evaluation successful");

            // Output in configured format
            match output_format.as_str() {
                "json" => {
                    // TODO: Implement proper Value serialization
                    println!("{}", serde_json::to_string_pretty(&format!("{result:?}"))?);
                }
                "yaml" => {
                    // TODO: Implement proper Value serialization
                    println!("{}", serde_yaml::to_string(&format!("{result:?}"))?);
                }
                _ => {
                    println!("  Result: {result:?}");
                }
            }
            Ok(())
        }
        Some(Commands::Run { file }) => {
            let source = std::fs::read_to_string(file)?;
            let mut parser = LigatureParser::new();
            let mut evaluator = Evaluator::new();

            // Use XDG configuration for progress display if available
            let show_progress = if let Some(ref config) = xdg_config {
                config
                    .load_config()
                    .await
                    .ok()
                    .and_then(|c| c.map(|cfg| cfg.defaults.show_progress))
                    .unwrap_or(true)
            } else {
                true
            };

            if show_progress {
                println!("Processing file: {file}");
            }

            // Parse
            let program = parser.parse_program(&source)?;
            if show_progress {
                println!("✓ Parsing successful");
            }

            // Type check
            type_check_program(&program)?;
            if show_progress {
                println!("✓ Type checking successful");
            }

            // Evaluate
            let result = evaluator.evaluate_program(&program)?;
            if show_progress {
                println!("✓ Evaluation successful");
            }

            // Use XDG configuration for output format if available
            let output_format = if let Some(ref config) = xdg_config {
                config
                    .output_format()
                    .await
                    .unwrap_or_else(|_| "text".to_string())
            } else {
                "text".to_string()
            };

            // Output in configured format
            match output_format.as_str() {
                "json" => {
                    // TODO: Implement proper Value serialization
                    println!("{}", serde_json::to_string_pretty(&format!("{result:?}"))?);
                }
                "yaml" => {
                    // TODO: Implement proper Value serialization
                    println!("{}", serde_yaml::to_string(&format!("{result:?}"))?);
                }
                _ => {
                    println!("  Final result: {result:?}");
                }
            }
            Ok(())
        }
        None => {
            println!("Ligature Language CLI");
            println!("Use --help for more information");
            Ok(())
        }
    }?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test CLI command parsing
    #[test]
    fn test_cli_parsing() {
        // Test parse command
        let args = vec!["ligature", "parse", "--file", "test.lig"];
        let cli = Cli::try_parse_from(args).unwrap();
        assert!(matches!(cli.command, Some(Commands::Parse { .. })));

        // Test typecheck command
        let args = vec!["ligature", "typecheck", "--file", "test.lig"];
        let cli = Cli::try_parse_from(args).unwrap();
        assert!(matches!(cli.command, Some(Commands::Typecheck { .. })));

        // Test eval command
        let args = vec!["ligature", "eval", "--file", "test.lig"];
        let cli = Cli::try_parse_from(args).unwrap();
        assert!(matches!(cli.command, Some(Commands::Eval { .. })));

        // Test run command
        let args = vec!["ligature", "run", "--file", "test.lig"];
        let cli = Cli::try_parse_from(args).unwrap();
        assert!(matches!(cli.command, Some(Commands::Run { .. })));
    }

    /// Test basic functionality
    #[test]
    fn test_basic_functionality() {
        let mut parser = LigatureParser::new();
        let mut evaluator = Evaluator::new();

        // Test parsing
        let source = "let x = 42;";
        let program = parser.parse_program(source).unwrap();
        assert_eq!(program.declarations.len(), 1);

        // Test type checking
        let type_result = type_check_program(&program);
        assert!(type_result.is_ok());

        // Test evaluation
        let result = evaluator.evaluate_program(&program).unwrap();
        assert!(result.is_unit());
    }
}
