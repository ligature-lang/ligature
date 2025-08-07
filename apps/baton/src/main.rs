//! CLI tool for Baton formal verification.

use clap::{Parser, Subcommand};
use colored::*;
use baton_verification::prelude::*;
use baton_protocol::prelude::*;

#[derive(Parser)]
#[command(name = "baton")]
#[command(about = "CLI tool for Baton formal verification")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Check if Lean is available and working
    Ping,

    /// Get Lean version information
    Version,

    /// Build the Lean specification
    Build,

    /// Verify expression evaluation
    VerifyEvaluation {
        /// Expression to verify
        expression: String,
        /// Expected value
        expected_value: String,
    },

    /// Verify type checking
    VerifyTypeCheck {
        /// Expression to verify
        expression: String,
        /// Expected type
        expected_type: String,
    },

    /// Run differential test
    DifferentialTest {
        /// Test case
        test_case: String,
        /// Test type (evaluation, typecheck, operational, config)
        test_type: String,
    },

    /// Verify type safety
    VerifyTypeSafety {
        /// Expression to verify
        expression: String,
    },

    /// Verify termination
    VerifyTermination {
        /// Expression to verify
        expression: String,
    },

    /// Verify determinism
    VerifyDeterminism {
        /// Expression to verify
        expression: String,
    },

    /// List specification files
    ListFiles,

    /// Check specification compilation
    CheckSpec,

    /// Extract test cases from specification
    ExtractTests {
        /// Specification file
        file: String,
    },

    /// Run comprehensive verification suite
    VerifySuite {
        /// Test expressions (comma-separated)
        expressions: String,
    },
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Ping => {
            println!("{}", "Pinging Lean process...".blue());
            let engine = VerificationEngine::new()?;
            match engine.ping().await {
                Ok(true) => println!("{}", "✓ Lean process is available".green()),
                Ok(false) => println!("{}", "✗ Lean process is not responding".red()),
                Err(e) => println!("{}: {}", "✗ Error pinging Lean".red(), e),
            }
        }

        Commands::Version => {
            println!("{}", "Getting Lean version...".blue());
            let engine = VerificationEngine::new()?;
            match engine.get_lean_version().await {
                Ok(version) => println!("{}: {}", "Lean version".green(), version),
                Err(e) => println!("{}: {}", "✗ Error getting version".red(), e),
            }
        }

        Commands::Build => {
            println!("{}", "Building Lean specification...".blue());
            let engine = VerificationEngine::new()?;
            match engine.build_specification().await {
                Ok(build_status) => {
                    if build_status.success {
                        println!("{}", "✓ Specification built successfully".green());
                        println!("Build time: {}ms", build_status.build_time);
                        println!("Built targets: {:?}", build_status.built_targets);
                    } else {
                        println!("{}", "✗ Specification build failed".red());
                        for error in build_status.errors {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error building specification".red(), e),
            }
        }

        Commands::VerifyEvaluation { expression, expected_value } => {
            println!("{}", "Verifying expression evaluation...".blue());
            let engine = VerificationEngine::new()?;
            match engine.verify_evaluation(&expression, &expected_value, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Evaluation verification successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Evaluation verification failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error verifying evaluation".red(), e),
            }
        }

        Commands::VerifyTypeCheck { expression, expected_type } => {
            println!("{}", "Verifying type checking...".blue());
            let engine = VerificationEngine::new()?;
            match engine.verify_type_check(&expression, &expected_type, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Type checking verification successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Type checking verification failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error verifying type checking".red(), e),
            }
        }

        Commands::DifferentialTest { test_case, test_type } => {
            println!("{}", "Running differential test...".blue());
            let engine = VerificationEngine::new()?;
            
            let test_type_enum = match test_type.as_str() {
                "evaluation" => DifferentialTestType::Evaluation,
                "typecheck" => DifferentialTestType::TypeCheck,
                "operational" => DifferentialTestType::OperationalSemantics,
                "config" => DifferentialTestType::ConfigurationValidation,
                _ => {
                    println!("{}: Invalid test type '{}'. Use: evaluation, typecheck, operational, config", 
                             "✗ Error".red(), test_type);
                    return Ok(());
                }
            };

            match engine.run_differential_test(&test_case, test_type_enum, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Differential test successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Differential test failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error running differential test".red(), e),
            }
        }

        Commands::VerifyTypeSafety { expression } => {
            println!("{}", "Verifying type safety...".blue());
            let engine = VerificationEngine::new()?;
            match engine.verify_type_safety(&expression, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Type safety verification successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Type safety verification failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error verifying type safety".red(), e),
            }
        }

        Commands::VerifyTermination { expression } => {
            println!("{}", "Verifying termination...".blue());
            let engine = VerificationEngine::new()?;
            match engine.verify_termination(&expression, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Termination verification successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Termination verification failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error verifying termination".red(), e),
            }
        }

        Commands::VerifyDeterminism { expression } => {
            println!("{}", "Verifying determinism...".blue());
            let engine = VerificationEngine::new()?;
            match engine.verify_determinism(&expression, None).await {
                Ok(response) => {
                    if response.is_success() {
                        println!("{}", "✓ Determinism verification successful".green());
                        println!("Execution time: {}ms", response.execution_time_ms());
                    } else {
                        println!("{}", "✗ Determinism verification failed".red());
                        if let Some(error) = response.error_message() {
                            println!("Error: {error}");
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error verifying determinism".red(), e),
            }
        }

        Commands::ListFiles => {
            println!("{}", "Listing specification files...".blue());
            let engine = VerificationEngine::new()?;
            match engine.validate_specification().await {
                Ok(validation) => {
                    println!("{}", "✓ Specification validation completed".green());
                    println!("Files validated: {}", validation.files_validated.len());
                    println!("Success: {}", validation.success);
                    println!("Errors: {}", validation.errors.len());
                    println!("Warnings: {}", validation.warnings.len());
                }
                Err(e) => println!("{}: {}", "✗ Error listing files".red(), e),
            }
        }

        Commands::CheckSpec => {
            println!("{}", "Checking specification compilation...".blue());
            let engine = VerificationEngine::new()?;
            match engine.validate_specification().await {
                Ok(validation) => {
                    if validation.success {
                        println!("{}", "✓ Specification is valid".green());
                        println!("Files validated: {}", validation.files_validated.len());
                    } else {
                        println!("{}", "✗ Specification has errors".red());
                        for error in validation.errors {
                            println!("Error: {} - {}", error.file, error.message);
                        }
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error checking specification".red(), e),
            }
        }

        Commands::ExtractTests { file } => {
            println!("{}", "Extracting test cases...".blue());
            let engine = VerificationEngine::new()?;
            match engine.extract_test_cases(&file).await {
                Ok(test_cases) => {
                    println!("{}", "✓ Test cases extracted successfully".green());
                    println!("Found {} test cases:", test_cases.len());
                    for (i, test_case) in test_cases.iter().enumerate() {
                        println!("  {}. {}", i + 1, test_case);
                    }
                }
                Err(e) => println!("{}: {}", "✗ Error extracting test cases".red(), e),
            }
        }

        Commands::VerifySuite { expressions } => {
            println!("{}", "Running verification suite...".blue());
            let engine = VerificationEngine::new()?;
            let expressions: Vec<&str> = expressions.split(',').collect();
            
            let mut success_count = 0;
            let total_count = expressions.len();

            for expression in expressions {
                let expr = expression.trim();
                if expr.is_empty() {
                    continue;
                }

                println!("Verifying: {expr}");
                match engine.verify_evaluation(expr, "expected", None).await {
                    Ok(response) => {
                        if response.is_success() {
                            println!("  {} ✓", "".green());
                            success_count += 1;
                        } else {
                            println!("  {} ✗", "".red());
                        }
                    }
                    Err(e) => {
                        println!("  {} ✗: {}", "".red(), e);
                    }
                }
            }

            println!("\nVerification suite completed:");
            println!("Success: {success_count}/{total_count}");
            if success_count == total_count {
                println!("{}", "✓ All verifications passed".green());
            } else {
                println!("{}", "✗ Some verifications failed".red());
            }
        }
    }

    Ok(())
} 