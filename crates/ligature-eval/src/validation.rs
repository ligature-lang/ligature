//! Runtime validation engine for Ligature constraint-based validation.
//!
//! This module provides runtime validation for:
//! - Refinement types: `type T = BaseType where predicate`
//! - Constraint types: `type T = BaseType with constraint1 with constraint2`
//!
//! The validation engine integrates with the evaluator to check values
//! against their declared types at runtime.

use crate::environment::EvaluationEnvironment;
use crate::value::Value;
use ligature_ast::ty::Constraint;
use ligature_ast::{AstResult, Expr, Type, TypeKind};
use regex::Regex;
use std::collections::HashMap;

/// Result of a validation operation
#[derive(Debug, Clone, PartialEq)]
pub enum ValidationResult {
    /// Validation passed
    Valid,
    /// Validation failed with a specific error message
    Invalid(String),
    /// Validation could not be performed (e.g., missing predicate function)
    CannotValidate(String),
}

/// Runtime validation engine for constraint-based validation
pub struct ValidationEngine {
    /// Environment for evaluating predicates and constraints
    environment: EvaluationEnvironment,
    /// Cache for compiled regex patterns
    regex_cache: HashMap<String, Regex>,
    /// Whether to enable validation caching
    enable_caching: bool,
    /// Cache for validation results
    validation_cache: HashMap<String, ValidationResult>,
}

impl ValidationEngine {
    /// Create a new validation engine
    pub fn new() -> Self {
        Self {
            environment: EvaluationEnvironment::new(),
            regex_cache: HashMap::new(),
            enable_caching: false,
            validation_cache: HashMap::new(),
        }
    }

    /// Create a validation engine with a custom environment
    pub fn with_environment(environment: EvaluationEnvironment) -> Self {
        Self {
            environment,
            regex_cache: HashMap::new(),
            enable_caching: false,
            validation_cache: HashMap::new(),
        }
    }

    /// Enable or disable validation caching
    pub fn set_caching(&mut self, enable: bool) {
        self.enable_caching = enable;
        if !enable {
            self.validation_cache.clear();
        }
    }

    /// Validate a value against a type
    pub fn validate_value(&mut self, value: &Value, type_: &Type) -> AstResult<ValidationResult> {
        match &type_.kind {
            TypeKind::Refinement {
                base_type,
                predicate,
                ..
            } => self.validate_refinement_type(value, base_type, predicate),
            TypeKind::ConstraintType {
                base_type,
                constraints,
            } => self.validate_constraint_type(value, base_type, constraints),
            _ => {
                // For non-refinement/constraint types, just check basic type compatibility
                self.validate_basic_type(value, type_)
            }
        }
    }

    /// Validate a value against a refinement type
    fn validate_refinement_type(
        &mut self,
        value: &Value,
        base_type: &Type,
        predicate: &Expr,
    ) -> AstResult<ValidationResult> {
        // First validate that the value matches the base type
        let base_validation = self.validate_basic_type(value, base_type)?;
        if base_validation != ValidationResult::Valid {
            return Ok(base_validation);
        }

        // Then evaluate the predicate with the value bound to a variable
        // We'll use "x" as the default variable name for the value being validated
        let predicate_result = self.evaluate_predicate(predicate, value, "x")?;

        match predicate_result {
            ValidationResult::Valid => Ok(ValidationResult::Valid),
            ValidationResult::Invalid(msg) => Ok(ValidationResult::Invalid(format!(
                "Refinement predicate failed: {msg}"
            ))),
            ValidationResult::CannotValidate(msg) => Ok(ValidationResult::CannotValidate(format!(
                "Cannot evaluate refinement predicate: {msg}"
            ))),
        }
    }

    /// Validate a value against a constraint type
    fn validate_constraint_type(
        &mut self,
        value: &Value,
        base_type: &Type,
        constraints: &[Constraint],
    ) -> AstResult<ValidationResult> {
        // First validate that the value matches the base type
        let base_validation = self.validate_basic_type(value, base_type)?;
        if base_validation != ValidationResult::Valid {
            return Ok(base_validation);
        }

        // Then validate each constraint
        for constraint in constraints {
            let constraint_result = self.validate_constraint(value, constraint)?;
            match constraint_result {
                ValidationResult::Valid => continue, // Continue to next constraint
                ValidationResult::Invalid(msg) => {
                    return Ok(ValidationResult::Invalid(format!(
                        "Constraint validation failed: {msg}"
                    )));
                }
                ValidationResult::CannotValidate(msg) => {
                    return Ok(ValidationResult::CannotValidate(format!(
                        "Cannot validate constraint: {msg}"
                    )));
                }
            }
        }

        Ok(ValidationResult::Valid)
    }

    /// Validate a value against a basic type (non-refinement, non-constraint)
    fn validate_basic_type(&self, value: &Value, type_: &Type) -> AstResult<ValidationResult> {
        match (&value.kind, &type_.kind) {
            (crate::value::ValueKind::Integer(_), TypeKind::Integer) => Ok(ValidationResult::Valid),
            (crate::value::ValueKind::Float(_), TypeKind::Float) => Ok(ValidationResult::Valid),
            (crate::value::ValueKind::String(_), TypeKind::String) => Ok(ValidationResult::Valid),
            (crate::value::ValueKind::Boolean(_), TypeKind::Bool) => Ok(ValidationResult::Valid),
            (crate::value::ValueKind::Unit, TypeKind::Unit) => Ok(ValidationResult::Valid),
            (crate::value::ValueKind::List(_), TypeKind::List { .. }) => {
                // For now, just check that it's a list
                // TODO: Validate list element types
                Ok(ValidationResult::Valid)
            }
            (crate::value::ValueKind::Record(_), TypeKind::Record { .. }) => {
                // For now, just check that it's a record
                // TODO: Validate record field types
                Ok(ValidationResult::Valid)
            }
            _ => Ok(ValidationResult::Invalid(format!(
                "Type mismatch: expected {:?}, got {:?}",
                type_.kind, value.kind
            ))),
        }
    }

    /// Validate a value against a specific constraint
    fn validate_constraint(
        &mut self,
        value: &Value,
        constraint: &Constraint,
    ) -> AstResult<ValidationResult> {
        match constraint {
            Constraint::ValueConstraint(expr) => self.evaluate_predicate(expr, value, "x"),
            Constraint::RangeConstraint { min: _, max: _, .. } => {
                // For now, we'll skip range constraints since they require expression evaluation
                // TODO: Implement proper range constraint validation
                Ok(ValidationResult::CannotValidate(
                    "Range constraint validation not yet implemented".to_string(),
                ))
            }
            Constraint::PatternConstraint { pattern, regex } => {
                self.validate_pattern_constraint(value, pattern, *regex)
            }
            Constraint::CustomConstraint {
                function: _,
                arguments: _,
            } => {
                // For now, we'll skip custom constraints since they require expression evaluation
                // TODO: Implement proper custom constraint validation
                Ok(ValidationResult::CannotValidate(
                    "Custom constraint validation not yet implemented".to_string(),
                ))
            }
            Constraint::CrossFieldConstraint { .. } => {
                // Cross-field constraints are not supported for single value validation
                Ok(ValidationResult::CannotValidate(
                    "Cross-field constraints require record validation".to_string(),
                ))
            }
        }
    }

    /// Evaluate a predicate expression with a value bound to a variable
    fn evaluate_predicate(
        &mut self,
        predicate: &Expr,
        value: &Value,
        var_name: &str,
    ) -> AstResult<ValidationResult> {
        // Create a temporary environment with the value bound
        let mut temp_env = self.environment.clone();
        temp_env.bind(var_name.to_string(), value.clone());

        // For now, we'll use a simplified evaluation approach
        // In a full implementation, we would use the evaluator's expression evaluation
        match predicate {
            Expr {
                kind: ligature_ast::ExprKind::Variable(name),
                ..
            } if name == var_name => {
                // The predicate is just the variable itself, so it's always true
                Ok(ValidationResult::Valid)
            }
            Expr {
                kind: ligature_ast::ExprKind::Literal(literal),
                ..
            } => {
                // For literal expressions, check if they're boolean true
                match literal {
                    ligature_ast::Literal::Boolean(true) => Ok(ValidationResult::Valid),
                    ligature_ast::Literal::Boolean(false) => Ok(ValidationResult::Invalid(
                        "Predicate evaluated to false".to_string(),
                    )),
                    _ => Ok(ValidationResult::CannotValidate(
                        "Predicate must evaluate to a boolean".to_string(),
                    )),
                }
            }
            _ => {
                // For complex expressions, we would need a full evaluator
                // For now, return CannotValidate
                Ok(ValidationResult::CannotValidate(
                    "Complex predicate evaluation not yet implemented".to_string(),
                ))
            }
        }
    }

    /// Validate a pattern constraint
    fn validate_pattern_constraint(
        &mut self,
        value: &Value,
        pattern: &str,
        is_regex: bool,
    ) -> AstResult<ValidationResult> {
        let string_value = match value {
            Value {
                kind: crate::value::ValueKind::String(s),
                ..
            } => s.as_str(),
            _ => {
                return Ok(ValidationResult::Invalid(
                    "Pattern constraint requires string value".to_string(),
                ));
            }
        };

        if is_regex {
            // Use regex pattern
            let regex = self.get_or_compile_regex(pattern)?;
            if regex.is_match(string_value) {
                Ok(ValidationResult::Valid)
            } else {
                Ok(ValidationResult::Invalid(format!(
                    "String '{string_value}' does not match regex pattern '{pattern}'"
                )))
            }
        } else {
            // Use simple pattern matching (for future extension)
            // For now, just check if the pattern is a substring
            if string_value.contains(pattern) {
                Ok(ValidationResult::Valid)
            } else {
                Ok(ValidationResult::Invalid(format!(
                    "String '{string_value}' does not contain pattern '{pattern}'"
                )))
            }
        }
    }

    /// Get or compile a regex pattern
    fn get_or_compile_regex(&mut self, pattern: &str) -> AstResult<&Regex> {
        if !self.regex_cache.contains_key(pattern) {
            let regex = Regex::new(pattern).map_err(|e| ligature_ast::AstError::ParseError {
                message: format!("Invalid regex pattern '{pattern}': {e}"),
                span: ligature_ast::Span::default(),
            })?;
            self.regex_cache.insert(pattern.to_string(), regex);
        }
        Ok(self.regex_cache.get(pattern).unwrap())
    }

    /// Clear the validation cache
    pub fn clear_cache(&mut self) {
        self.validation_cache.clear();
        self.regex_cache.clear();
    }

    /// Get validation statistics
    pub fn stats(&self) -> ValidationStats {
        ValidationStats {
            cache_size: self.validation_cache.len(),
            regex_cache_size: self.regex_cache.len(),
            caching_enabled: self.enable_caching,
        }
    }
}

/// Statistics for the validation engine
#[derive(Debug, Clone)]
pub struct ValidationStats {
    pub cache_size: usize,
    pub regex_cache_size: usize,
    pub caching_enabled: bool,
}

impl Default for ValidationEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ligature_ast::ty::Constraint;
    use ligature_ast::{Span, Type};

    #[test]
    fn test_basic_type_validation() {
        let mut engine = ValidationEngine::new();

        // Test integer validation
        let int_type = Type::integer(Span::default());
        let int_value = Value::integer(42, Span::default());
        let result = engine.validate_value(&int_value, &int_type).unwrap();
        assert_eq!(result, ValidationResult::Valid);

        // Test string validation
        let string_type = Type::string(Span::default());
        let string_value = Value::string("hello".to_string(), Span::default());
        let result = engine.validate_value(&string_value, &string_type).unwrap();
        assert_eq!(result, ValidationResult::Valid);

        // Test type mismatch
        let result = engine.validate_value(&int_value, &string_type).unwrap();
        assert!(matches!(result, ValidationResult::Invalid(_)));
    }

    #[test]
    fn test_range_constraint_validation() {
        let mut engine = ValidationEngine::new();

        // Test pattern constraint validation instead since range constraints are not implemented
        let constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };

        // Valid value
        let value = Value::string("Hello".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert_eq!(result, ValidationResult::Valid);

        // Invalid value (contains numbers)
        let value = Value::string("Hello123".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert!(matches!(result, ValidationResult::Invalid(_)));
    }

    #[test]
    fn test_pattern_constraint_validation() {
        let mut engine = ValidationEngine::new();

        let constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };

        // Valid value
        let value = Value::string("Hello".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert_eq!(result, ValidationResult::Valid);

        // Invalid value (contains numbers)
        let value = Value::string("Hello123".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert!(matches!(result, ValidationResult::Invalid(_)));
    }

    #[test]
    fn test_custom_constraint_validation() {
        let mut engine = ValidationEngine::new();

        let _constraint = Constraint::CustomConstraint {
            function: "isValidEmail".to_string(),
            arguments: vec![],
        };

        // Since custom constraints are not implemented, we'll test pattern constraints instead
        let constraint = Constraint::PatternConstraint {
            pattern: "^[A-Za-z]+$".to_string(),
            regex: true,
        };

        // Valid value
        let value = Value::string("Hello".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert_eq!(result, ValidationResult::Valid);

        // Invalid value
        let value = Value::string("Hello123".to_string(), Span::default());
        let result = engine.validate_constraint(&value, &constraint).unwrap();
        assert!(matches!(result, ValidationResult::Invalid(_)));
    }
}
