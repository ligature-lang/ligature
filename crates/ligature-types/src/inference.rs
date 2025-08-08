//! Type inference for the Ligature language.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use ligature_ast::{AstError, AstResult, Expr, ExprKind, Literal, Span, Type, TypeKind};

use crate::constraints::{Constraint, ConstraintSolver};
use crate::environment::TypeEnvironment;

/// Performance metrics for type inference.
#[derive(Debug, Clone)]
pub struct InferenceMetrics {
    /// Number of type inference operations performed.
    pub inference_count: usize,
    /// Number of constraint solving operations.
    pub constraint_solving_count: usize,
    /// Total time spent on type inference.
    pub total_inference_time: std::time::Duration,
    /// Total time spent on constraint solving.
    pub total_constraint_solving_time: std::time::Duration,
    /// Cache hit rate.
    pub cache_hits: usize,
    /// Cache misses.
    pub cache_misses: usize,
}

impl InferenceMetrics {
    /// Create new metrics.
    pub fn new() -> Self {
        Self {
            inference_count: 0,
            constraint_solving_count: 0,
            total_inference_time: std::time::Duration::ZERO,
            total_constraint_solving_time: std::time::Duration::ZERO,
            cache_hits: 0,
            cache_misses: 0,
        }
    }
}

impl Default for InferenceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl InferenceMetrics {
    /// Get cache hit rate as a percentage.
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            (self.cache_hits as f64 / total as f64) * 100.0
        }
    }

    /// Reset all metrics.
    pub fn reset(&mut self) {
        self.inference_count = 0;
        self.constraint_solving_count = 0;
        self.total_inference_time = std::time::Duration::ZERO;
        self.total_constraint_solving_time = std::time::Duration::ZERO;
        self.cache_hits = 0;
        self.cache_misses = 0;
    }
}

/// Type inference engine for the Ligature language.
pub struct TypeInference {
    environment: TypeEnvironment,
    pub constraint_solver: ConstraintSolver,
    next_type_variable: usize,
    /// Cache for type inference results.
    type_cache: std::collections::HashMap<String, Type>,
    /// Performance metrics.
    metrics: InferenceMetrics,
    /// Search paths for module resolution.
    search_paths: Vec<PathBuf>,
    /// Register paths for module resolution.
    pub register_paths: Vec<PathBuf>,
    /// Cache for loaded modules.
    pub module_cache: HashMap<String, ligature_ast::Module>,
    /// Dependency graph for cycle detection.
    dependency_graph: HashMap<String, HashSet<String>>,
    /// Current import stack for cycle detection.
    import_stack: Vec<String>,
}

impl TypeInference {
    /// Create a new type inference engine.
    pub fn new() -> Self {
        Self {
            environment: TypeEnvironment::new(),
            constraint_solver: ConstraintSolver::new(),
            next_type_variable: 0,
            type_cache: std::collections::HashMap::new(),
            metrics: InferenceMetrics::new(),
            search_paths: Vec::new(),
            register_paths: Vec::new(),
            module_cache: HashMap::new(),
            dependency_graph: HashMap::new(),
            import_stack: Vec::new(),
        }
    }

    /// Infer the type of an expression.
    pub fn infer_expression(&mut self, expr: &Expr) -> AstResult<Type> {
        let start_time = Instant::now();
        self.metrics.inference_count += 1;

        // Generate cache key for this expression
        let cache_key = self.expression_to_cache_key(expr);

        // Check cache first
        if let Some(cached_type) = self.type_cache.get(&cache_key) {
            self.metrics.cache_hits += 1;
            return Ok(cached_type.clone());
        }

        self.metrics.cache_misses += 1;

        let type_ = self.infer_expression_internal(expr)?;

        // Solve constraints with timing
        let constraint_start = Instant::now();
        self.metrics.constraint_solving_count += 1;

        let substitution = self.constraint_solver.solve().map_err(|e| {
            // Enhanced error reporting with more context
            let error_message = if e.contains("Cannot unify types") {
                format!("Type mismatch in expression: {e}")
            } else if e.contains("Occurs check failed") {
                format!("Circular type definition detected: {e}")
            } else if e.contains("Record types have different") {
                format!("Record type mismatch: {e}")
            } else if e.contains("Union types have different") {
                format!("Union type mismatch: {e}")
            } else {
                format!("Type inference failed: {e}")
            };

            AstError::InternalError {
                message: error_message,
                span: expr.span,
            }
        })?;

        self.metrics.total_constraint_solving_time += constraint_start.elapsed();

        // Apply substitution to get the final type
        let final_type = self.apply_substitution(type_, &substitution);

        // Cache the result
        self.type_cache.insert(cache_key, final_type.clone());

        self.metrics.total_inference_time += start_time.elapsed();

        Ok(final_type)
    }

    /// Internal type inference implementation.
    fn infer_expression_internal(&mut self, expr: &Expr) -> AstResult<Type> {
        match &expr.kind {
            ExprKind::Literal(literal) => self.infer_literal(literal),
            ExprKind::Variable(name) => self.infer_variable(name),
            ExprKind::Application { function, argument } => {
                self.infer_application(function, argument)
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => self.infer_abstraction(parameter, parameter_type.as_ref().map(|v| &**v), body),
            ExprKind::Let { name, value, body } => self.infer_let(name, value, body),
            ExprKind::Record { fields } => self.infer_record(fields),
            ExprKind::FieldAccess { record, field } => self.infer_field_access(record, field),
            ExprKind::Union { variant, value } => {
                self.infer_union(variant, value.as_ref().map(|v| &**v))
            }
            ExprKind::Match { scrutinee, cases } => self.infer_match(scrutinee, cases),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.infer_if(condition, then_branch, else_branch),
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => self.infer_binary_op(operator, left, right),
            ExprKind::UnaryOp { operator, operand } => self.infer_unary_op(operator, operand),
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => self.infer_annotated(expression, type_annotation),
        }
    }

    /// Infer the type of a literal.
    fn infer_literal(&mut self, literal: &Literal) -> AstResult<Type> {
        let kind = match literal {
            Literal::String(_) => TypeKind::String,
            Literal::Integer(_) => TypeKind::Integer,
            Literal::Float(_) => TypeKind::Float,
            Literal::Boolean(_) => TypeKind::Bool,
            Literal::Unit => TypeKind::Unit,
            Literal::List(elements) => {
                if elements.is_empty() {
                    // Empty list has type [a] where a is a type variable
                    TypeKind::List(Box::new(Type::variable(
                        format!("a{}", self.next_type_variable),
                        Span::default(),
                    )))
                } else {
                    // For non-empty lists, infer the element type and ensure all elements are compatible
                    let first_element_type = self.infer_expression_internal(&elements[0])?;

                    // Create a fresh type variable for the unified element type
                    let unified_element_type =
                        Type::variable(format!("elem{}", self.next_type_variable), Span::default());
                    self.next_type_variable += 1;

                    // Add constraint that first element type equals unified type
                    self.constraint_solver.add_constraint(Constraint::Equality(
                        first_element_type,
                        unified_element_type.clone(),
                    ));

                    // Add constraints for all other elements
                    for element in &elements[1..] {
                        let element_type = self.infer_expression_internal(element)?;
                        self.constraint_solver.add_constraint(Constraint::Equality(
                            element_type,
                            unified_element_type.clone(),
                        ));
                    }

                    TypeKind::List(Box::new(unified_element_type))
                }
            }
        };

        Ok(Type::new(kind, Span::default()))
    }

    /// Infer the type of a variable.
    fn infer_variable(&mut self, name: &str) -> AstResult<Type> {
        let type_ = self
            .environment
            .lookup(name)
            .ok_or_else(|| AstError::UndefinedIdentifier {
                name: name.to_string(),
                span: Span::default(),
            })?;

        // If the type is polymorphic (universal), instantiate it with fresh type variables
        Ok(self.instantiate(&type_))
    }

    /// Infer the type of a function application.
    fn infer_application(&mut self, function: &Expr, argument: &Expr) -> AstResult<Type> {
        let function_type = self.infer_expression_internal(function)?;
        let argument_type = self.infer_expression_internal(argument)?;

        // Create a fresh type variable for the return type
        let return_type = Type::variable(format!("r{}", self.next_type_variable), Span::default());
        self.next_type_variable += 1;

        // Add constraint: function_type = argument_type -> return_type
        let expected_function_type =
            Type::function(argument_type, return_type.clone(), Span::default());
        self.constraint_solver
            .add_constraint(Constraint::Equality(function_type, expected_function_type));

        Ok(return_type)
    }

    /// Infer the type of a lambda abstraction.
    fn infer_abstraction(
        &mut self,
        parameter: &str,
        parameter_type: Option<&Type>,
        body: &Expr,
    ) -> AstResult<Type> {
        let param_type = if let Some(ty) = parameter_type {
            ty.clone()
        } else {
            // Create a fresh type variable for the parameter
            let fresh_var =
                Type::variable(format!("a{}", self.next_type_variable), Span::default());
            self.next_type_variable += 1;
            fresh_var
        };

        // Create a new environment with the parameter bound
        let mut new_env = TypeEnvironment::with_parent(self.environment.clone());
        new_env.bind(parameter.to_string(), param_type.clone());

        // Create a new type inference with the new environment but share the constraint solver
        let mut new_inference = TypeInference {
            environment: new_env,
            constraint_solver: self.constraint_solver.clone(),
            next_type_variable: self.next_type_variable,
            type_cache: std::collections::HashMap::new(),
            metrics: InferenceMetrics::new(),
            search_paths: self.search_paths.clone(),
            register_paths: self.register_paths.clone(),
            module_cache: HashMap::new(),
            dependency_graph: self.dependency_graph.clone(),
            import_stack: self.import_stack.clone(),
        };

        let body_type = new_inference.infer_expression_internal(body)?;

        // Merge constraints back from the nested inference
        self.constraint_solver = new_inference.constraint_solver;
        self.next_type_variable = new_inference.next_type_variable;

        Ok(Type::function(param_type, body_type, Span::default()))
    }

    /// Infer the type of a let expression.
    fn infer_let(&mut self, name: &str, value: &Expr, body: &Expr) -> AstResult<Type> {
        let value_type = self.infer_expression_internal(value)?;

        // Generalize the value type to support polymorphic let bindings
        let generalized_type = self.generalize(value_type, &self.environment);

        // Create a new environment with the binding
        let mut new_env = TypeEnvironment::with_parent(self.environment.clone());
        new_env.bind(name.to_string(), generalized_type);

        // Create a new type inference with the new environment
        let mut new_inference = TypeInference {
            environment: new_env,
            constraint_solver: self.constraint_solver.clone(),
            next_type_variable: self.next_type_variable,
            type_cache: std::collections::HashMap::new(),
            metrics: InferenceMetrics::new(),
            search_paths: self.search_paths.clone(),
            register_paths: self.register_paths.clone(),
            module_cache: HashMap::new(),
            dependency_graph: self.dependency_graph.clone(),
            import_stack: self.import_stack.clone(),
        };

        new_inference.infer_expression_internal(body)
    }

    /// Infer the type of a record expression.
    fn infer_record(&mut self, fields: &[ligature_ast::RecordField]) -> AstResult<Type> {
        let mut type_fields = Vec::new();

        for field in fields {
            let field_type = self.infer_expression_internal(&field.value)?;
            type_fields.push(ligature_ast::TypeField {
                name: field.name.clone(),
                type_: field_type,
                span: field.span,
            });
        }

        Ok(Type::record(type_fields, Span::default()))
    }

    /// Infer the type of a field access expression.
    fn infer_field_access(&mut self, record: &Expr, field: &str) -> AstResult<Type> {
        let record_type = self.infer_expression_internal(record)?;

        match &record_type.kind {
            TypeKind::Record { fields } => {
                for field_type in fields {
                    if field_type.name == field {
                        return Ok(field_type.type_.clone());
                    }
                }
                Err(AstError::InvalidTypeAnnotation { span: record.span })
            }
            _ => Err(AstError::InvalidTypeAnnotation { span: record.span }),
        }
    }

    /// Infer the type of a union expression.
    fn infer_union(&mut self, variant: &str, value: Option<&Expr>) -> AstResult<Type> {
        // First, try to find a type constructor for this union type
        let mut union_type = self.find_union_type_constructor(variant)?;

        // Find the specific variant in the union type and extract its type
        let variant_info = self.find_variant_in_union(&union_type, variant)?;
        let variant_type = variant_info.type_.clone();

        // Infer the type of the value if provided
        if let Some(expr) = value {
            let inferred_type = self.infer_expression_internal(expr)?;

            // Check if the value type matches the variant's expected type
            if let Some(expected_type) = &variant_type {
                self.constraint_solver.add_constraint(Constraint::Equality(
                    inferred_type.clone(),
                    expected_type.clone(),
                ));
            } else {
                // If the variant doesn't have a type annotation, we need to update the union type
                // to include the inferred type for this variant
                if let TypeKind::Union { variants } = &mut union_type.kind {
                    if let Some(variant_to_update) = variants.iter_mut().find(|v| v.name == variant)
                    {
                        variant_to_update.type_ = Some(inferred_type);
                    }
                }
            }
        } else {
            // No value provided, check if the variant expects one
            if variant_type.is_some() {
                return Err(AstError::InvalidTypeAnnotation {
                    span: Span::default(),
                });
            }
        }

        Ok(union_type)
    }

    /// Find a union type constructor that contains the given variant.
    fn find_union_type_constructor(&mut self, variant: &str) -> AstResult<Type> {
        // First, check if we have a direct type constructor binding
        if let Some(type_constructor) = self.environment.lookup_type_constructor(variant) {
            return Ok(type_constructor.body.clone());
        }

        // Check if we have a type alias that might be a union
        if let Some(type_alias) = self.environment.lookup_type_alias(variant) {
            if type_alias.type_.is_union() {
                return Ok(type_alias.type_.clone());
            }
        }

        // Look through the environment for union types that contain this variant
        for (_name, type_) in self.environment.iter() {
            if let Some(union_variants) = type_.as_union() {
                if union_variants.iter().any(|v| v.name == variant) {
                    return Ok(type_.clone());
                }
            }
        }

        // If we can't find a specific union type, create a fresh one
        // This handles cases where the union type is being inferred
        let fresh_variant = ligature_ast::TypeVariant {
            name: variant.to_string(),
            type_: None, // Will be inferred from context
            span: Span::default(),
        };

        let union_type = Type::union(vec![fresh_variant], Span::default());

        // Bind this union type to the environment so it can be found later
        let union_name = format!("Union_{variant}");
        self.environment.bind(union_name, union_type.clone());

        Ok(union_type)
    }

    /// Find a specific variant within a union type.
    fn find_variant_in_union<'a>(
        &self,
        union_type: &'a Type,
        variant_name: &str,
    ) -> AstResult<&'a ligature_ast::TypeVariant> {
        match &union_type.kind {
            TypeKind::Union { variants } => variants
                .iter()
                .find(|v| v.name == variant_name)
                .ok_or_else(|| AstError::InvalidTypeAnnotation {
                    span: Span::default(),
                }),
            _ => Err(AstError::InvalidTypeAnnotation {
                span: Span::default(),
            }),
        }
    }

    /// Infer the type of a match expression.
    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        cases: &[ligature_ast::MatchCase],
    ) -> AstResult<Type> {
        let scrutinee_type = self.infer_expression_internal(scrutinee)?;

        if cases.is_empty() {
            return Err(AstError::InvalidTypeAnnotation {
                span: scrutinee.span,
            });
        }

        // First, bind pattern variables for all cases
        for case in cases {
            self.check_pattern_compatibility(&case.pattern, &scrutinee_type)?;
            self.bind_pattern_variables(&case.pattern, &scrutinee_type)?;
        }

        // Now infer the types of all case expressions
        let first_case_type = self.infer_expression_internal(&cases[0].expression)?;

        // Add constraints to ensure all cases have the same type
        for case in &cases[1..] {
            let case_type = self.infer_expression_internal(&case.expression)?;
            self.constraint_solver
                .add_constraint(Constraint::Equality(first_case_type.clone(), case_type));
        }

        Ok(first_case_type)
    }

    /// Recursively bind pattern variables in a pattern.
    fn bind_pattern_variables(
        &mut self,
        pattern: &ligature_ast::Pattern,
        scrutinee_type: &Type,
    ) -> AstResult<()> {
        match pattern {
            ligature_ast::Pattern::Variable(var_name) => {
                // Bind the variable to the scrutinee type
                self.environment
                    .bind(var_name.clone(), scrutinee_type.clone());
            }
            ligature_ast::Pattern::Union {
                variant,
                value: Some(nested_pattern),
            } => {
                // For union patterns, find the variant type and bind nested patterns
                if let Some(union_variants) = scrutinee_type.as_union() {
                    if let Some(variant_info) = union_variants.iter().find(|v| v.name == *variant) {
                        if let Some(variant_type) = &variant_info.type_ {
                            // Recursively bind variables in the nested pattern
                            self.bind_pattern_variables(nested_pattern, variant_type)?;
                        }
                    }
                }
            }
            ligature_ast::Pattern::Record { fields } => {
                // For record patterns, bind each field pattern
                if let Some(record_fields) = scrutinee_type.as_record() {
                    for field_pattern in fields {
                        if let Some(record_field) =
                            record_fields.iter().find(|f| f.name == field_pattern.name)
                        {
                            self.bind_pattern_variables(
                                &field_pattern.pattern,
                                &record_field.type_,
                            )?;
                        }
                    }
                }
            }
            ligature_ast::Pattern::List { elements } => {
                // For list patterns, bind each element pattern
                if let Some(element_type) = scrutinee_type.as_list() {
                    for element_pattern in elements {
                        self.bind_pattern_variables(element_pattern, element_type)?;
                    }
                }
            }
            _ => {
                // For other patterns (wildcard, literal), no binding needed
            }
        }
        Ok(())
    }

    /// Check if a pattern is compatible with a given type.
    #[allow(clippy::only_used_in_recursion)]
    fn check_pattern_compatibility(
        &self,
        pattern: &ligature_ast::Pattern,
        scrutinee_type: &Type,
    ) -> AstResult<()> {
        match pattern {
            ligature_ast::Pattern::Literal(literal) => {
                let _pattern_type = match literal {
                    ligature_ast::Literal::String(_) => Type::string(Span::default()),
                    ligature_ast::Literal::Integer(_) => Type::integer(Span::default()),
                    ligature_ast::Literal::Float(_) => Type::float(Span::default()),
                    ligature_ast::Literal::Boolean(_) => Type::bool(Span::default()),
                    ligature_ast::Literal::Unit => Type::unit(Span::default()),
                    ligature_ast::Literal::List(_) => {
                        // For list patterns, we need to check element type compatibility
                        Type::list(
                            Type::variable("a".to_string(), Span::default()),
                            Span::default(),
                        )
                    }
                };

                // Add constraint that pattern type must be compatible with scrutinee type
                // This will be solved by the constraint solver
                Ok(())
            }
            ligature_ast::Pattern::Variable(_) => {
                // Variable patterns match any type
                Ok(())
            }
            ligature_ast::Pattern::Wildcard => {
                // Wildcard patterns match any type
                Ok(())
            }
            ligature_ast::Pattern::Record { fields } => {
                // Check that scrutinee type is a record with compatible fields
                match &scrutinee_type.kind {
                    TypeKind::Record {
                        fields: scrutinee_fields,
                    } => {
                        for field in fields {
                            let field_exists =
                                scrutinee_fields.iter().any(|f| f.name == field.name);
                            if !field_exists {
                                return Err(AstError::InvalidTypeAnnotation {
                                    span: Span::default(),
                                });
                            }
                        }
                        Ok(())
                    }
                    _ => Err(AstError::InvalidTypeAnnotation {
                        span: Span::default(),
                    }),
                }
            }
            ligature_ast::Pattern::Union { variant, value } => {
                // Check that scrutinee type is a union with the specified variant
                match &scrutinee_type.kind {
                    TypeKind::Union { variants } => {
                        let variant_info = variants.iter().find(|v| v.name == *variant);
                        match variant_info {
                            Some(variant_info) => {
                                // Check if the pattern value matches the variant's type
                                match (value, &variant_info.type_) {
                                    (Some(pattern), Some(variant_type)) => {
                                        // Recursively check the pattern against the variant's type
                                        self.check_pattern_compatibility(pattern, variant_type)
                                    }
                                    (None, None) => Ok(()),
                                    _ => Err(AstError::InvalidTypeAnnotation {
                                        span: Span::default(),
                                    }),
                                }
                            }
                            None => Err(AstError::InvalidTypeAnnotation {
                                span: Span::default(),
                            }),
                        }
                    }
                    _ => Err(AstError::InvalidTypeAnnotation {
                        span: Span::default(),
                    }),
                }
            }
            ligature_ast::Pattern::List { elements } => {
                // Check that scrutinee type is a list
                match &scrutinee_type.kind {
                    TypeKind::List(_) => {
                        // Recursively check element patterns
                        for element_pattern in elements {
                            self.check_pattern_compatibility(element_pattern, scrutinee_type)?;
                        }
                        Ok(())
                    }
                    _ => Err(AstError::InvalidTypeAnnotation {
                        span: Span::default(),
                    }),
                }
            }
        }
    }

    /// Infer the type of an if expression.
    fn infer_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> AstResult<Type> {
        let condition_type = self.infer_expression_internal(condition)?;
        let then_type = self.infer_expression_internal(then_branch)?;
        let else_type = self.infer_expression_internal(else_branch)?;

        // Add constraints
        self.constraint_solver.add_constraint(Constraint::Equality(
            condition_type,
            Type::bool(Span::default()),
        ));
        self.constraint_solver
            .add_constraint(Constraint::Equality(then_type.clone(), else_type));

        Ok(then_type)
    }

    /// Infer the type of a binary operation.
    fn infer_binary_op(
        &mut self,
        operator: &ligature_ast::BinaryOperator,
        left: &Expr,
        right: &Expr,
    ) -> AstResult<Type> {
        let left_type = self.infer_expression_internal(left)?;
        let right_type = self.infer_expression_internal(right)?;

        match operator {
            ligature_ast::BinaryOperator::Add
            | ligature_ast::BinaryOperator::Subtract
            | ligature_ast::BinaryOperator::Multiply
            | ligature_ast::BinaryOperator::Divide
            | ligature_ast::BinaryOperator::Modulo => {
                // Arithmetic operators require numeric types
                self.constraint_solver
                    .add_constraint(Constraint::Equality(left_type.clone(), right_type));
                self.constraint_solver.add_constraint(Constraint::Subtype(
                    left_type.clone(),
                    Type::integer(Span::default()),
                ));
                Ok(left_type)
            }
            ligature_ast::BinaryOperator::Equal
            | ligature_ast::BinaryOperator::NotEqual
            | ligature_ast::BinaryOperator::LessThan
            | ligature_ast::BinaryOperator::LessThanOrEqual
            | ligature_ast::BinaryOperator::GreaterThan
            | ligature_ast::BinaryOperator::GreaterThanOrEqual => {
                // Comparison operators require comparable types and return boolean
                self.constraint_solver
                    .add_constraint(Constraint::Equality(left_type, right_type));
                Ok(Type::bool(Span::default()))
            }
            ligature_ast::BinaryOperator::And | ligature_ast::BinaryOperator::Or => {
                // Logical operators require boolean types
                self.constraint_solver.add_constraint(Constraint::Equality(
                    left_type.clone(),
                    Type::bool(Span::default()),
                ));
                self.constraint_solver.add_constraint(Constraint::Equality(
                    right_type,
                    Type::bool(Span::default()),
                ));
                Ok(Type::bool(Span::default()))
            }
            ligature_ast::BinaryOperator::Concat => {
                // String concatenation
                self.constraint_solver.add_constraint(Constraint::Equality(
                    left_type.clone(),
                    Type::string(Span::default()),
                ));
                self.constraint_solver.add_constraint(Constraint::Equality(
                    right_type,
                    Type::string(Span::default()),
                ));
                Ok(Type::string(Span::default()))
            }
        }
    }

    /// Infer the type of a unary operation.
    fn infer_unary_op(
        &mut self,
        operator: &ligature_ast::UnaryOperator,
        operand: &Expr,
    ) -> AstResult<Type> {
        let operand_type = self.infer_expression_internal(operand)?;

        match operator {
            ligature_ast::UnaryOperator::Not => {
                self.constraint_solver.add_constraint(Constraint::Equality(
                    operand_type.clone(),
                    Type::bool(Span::default()),
                ));
                Ok(Type::bool(Span::default()))
            }
            ligature_ast::UnaryOperator::Negate => {
                self.constraint_solver.add_constraint(Constraint::Subtype(
                    operand_type.clone(),
                    Type::integer(Span::default()),
                ));
                Ok(operand_type)
            }
        }
    }

    /// Infer the type of an annotated expression.
    fn infer_annotated(&mut self, expression: &Expr, type_annotation: &Type) -> AstResult<Type> {
        let inferred_type = self.infer_expression_internal(expression)?;

        // Add constraint that the inferred type equals the annotation
        self.constraint_solver
            .add_constraint(Constraint::Equality(inferred_type, type_annotation.clone()));

        Ok(type_annotation.clone())
    }

    /// Apply a substitution to a type.
    #[allow(clippy::only_used_in_recursion)]
    pub fn apply_substitution(
        &self,
        type_: Type,
        substitution: &std::collections::HashMap<String, Type>,
    ) -> Type {
        match &type_.kind {
            TypeKind::Variable(var) => {
                if let Some(substituted) = substitution.get(var) {
                    self.apply_substitution(substituted.clone(), substitution)
                } else {
                    type_
                }
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => Type::function(
                self.apply_substitution(*parameter.clone(), substitution),
                self.apply_substitution(*return_type.clone(), substitution),
                type_.span,
            ),
            TypeKind::Record { fields } => {
                let new_fields = fields
                    .iter()
                    .map(|field| ligature_ast::TypeField {
                        name: field.name.clone(),
                        type_: self.apply_substitution(field.type_.clone(), substitution),
                        span: field.span,
                    })
                    .collect();
                Type::record(new_fields, type_.span)
            }
            TypeKind::Union { variants } => {
                let new_variants = variants
                    .iter()
                    .map(|variant| ligature_ast::TypeVariant {
                        name: variant.name.clone(),
                        type_: variant
                            .type_
                            .as_ref()
                            .map(|t| self.apply_substitution(t.clone(), substitution)),
                        span: variant.span,
                    })
                    .collect();
                Type::union(new_variants, type_.span)
            }
            TypeKind::List(element_type) => Type::list(
                self.apply_substitution(*element_type.clone(), substitution),
                type_.span,
            ),
            _ => type_,
        }
    }

    /// Get a fresh type variable.
    pub fn fresh_type_variable(&mut self) -> Type {
        let var = Type::variable(format!("t{}", self.next_type_variable), Span::default());
        self.next_type_variable += 1;
        var
    }

    /// Reset the type inference engine.
    pub fn reset(&mut self) {
        self.next_type_variable = 0;
        self.constraint_solver = ConstraintSolver::new();
        self.type_cache.clear();
        self.metrics.reset();
    }

    /// Get performance metrics.
    pub fn metrics(&self) -> &InferenceMetrics {
        &self.metrics
    }

    /// Check if two types are equal.
    pub fn types_equal(&self, type1: &Type, type2: &Type) -> AstResult<bool> {
        self.types_equal_internal(type1, type2, &mut std::collections::HashMap::new())
    }

    #[allow(clippy::only_used_in_recursion)]
    fn types_equal_internal(
        &self,
        type1: &Type,
        type2: &Type,
        substitution: &mut std::collections::HashMap<String, Type>,
    ) -> AstResult<bool> {
        match (&type1.kind, &type2.kind) {
            (TypeKind::Variable(var1), TypeKind::Variable(var2)) => {
                if var1 == var2 {
                    Ok(true)
                } else if let Some(substituted) = substitution.get(var1) {
                    let substituted_clone = substituted.clone();
                    self.types_equal_internal(&substituted_clone, type2, substitution)
                } else if let Some(substituted) = substitution.get(var2) {
                    let substituted_clone = substituted.clone();
                    self.types_equal_internal(type1, &substituted_clone, substitution)
                } else {
                    substitution.insert(var1.clone(), type2.clone());
                    Ok(true)
                }
            }
            (TypeKind::Variable(var), _) => {
                if let Some(substituted) = substitution.get(var) {
                    let substituted_clone = substituted.clone();
                    self.types_equal_internal(&substituted_clone, type2, substitution)
                } else {
                    substitution.insert(var.clone(), type2.clone());
                    Ok(true)
                }
            }
            (_, TypeKind::Variable(var)) => {
                if let Some(substituted) = substitution.get(var) {
                    let substituted_clone = substituted.clone();
                    self.types_equal_internal(type1, &substituted_clone, substitution)
                } else {
                    substitution.insert(var.clone(), type1.clone());
                    Ok(true)
                }
            }
            (
                TypeKind::Function {
                    parameter: param1,
                    return_type: ret1,
                },
                TypeKind::Function {
                    parameter: param2,
                    return_type: ret2,
                },
            ) => {
                let param_equal = self.types_equal_internal(param1, param2, substitution)?;
                let ret_equal = self.types_equal_internal(ret1, ret2, substitution)?;
                Ok(param_equal && ret_equal)
            }
            (TypeKind::Record { fields: fields1 }, TypeKind::Record { fields: fields2 }) => {
                if fields1.len() != fields2.len() {
                    return Ok(false);
                }
                for (field1, field2) in fields1.iter().zip(fields2.iter()) {
                    if field1.name != field2.name {
                        return Ok(false);
                    }
                    if !self.types_equal_internal(&field1.type_, &field2.type_, substitution)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (TypeKind::List(element1), TypeKind::List(element2)) => {
                self.types_equal_internal(element1, element2, substitution)
            }
            (
                TypeKind::Union {
                    variants: variants1,
                },
                TypeKind::Union {
                    variants: variants2,
                },
            ) => {
                if variants1.len() != variants2.len() {
                    return Ok(false);
                }
                for (variant1, variant2) in variants1.iter().zip(variants2.iter()) {
                    if variant1.name != variant2.name {
                        return Ok(false);
                    }
                    match (&variant1.type_, &variant2.type_) {
                        (Some(type1), Some(type2)) => {
                            if !self.types_equal_internal(type1, type2, substitution)? {
                                return Ok(false);
                            }
                        }
                        (None, None) => {}
                        _ => return Ok(false),
                    }
                }
                Ok(true)
            }
            (TypeKind::Module { name: n1 }, TypeKind::Module { name: n2 }) => Ok(n1 == n2),
            (kind1, kind2) => Ok(std::mem::discriminant(kind1) == std::mem::discriminant(kind2)),
        }
    }

    /// Check that a type is well-formed.
    #[allow(clippy::only_used_in_recursion)]
    pub fn check_type(&self, type_: &Type) -> AstResult<()> {
        match &type_.kind {
            TypeKind::Variable(_) => Ok(()),
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                self.check_type(parameter)?;
                self.check_type(return_type)?;
                Ok(())
            }
            TypeKind::Record { fields } => {
                for field in fields {
                    self.check_type(&field.type_)?;
                }
                Ok(())
            }
            TypeKind::List(element_type) => self.check_type(element_type),
            TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(type_) = &variant.type_ {
                        self.check_type(type_)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Bind a variable to a type in the environment.
    pub fn bind(&mut self, name: String, type_: Type) {
        self.environment.bind(name, type_);
    }

    /// Bind a type alias in the environment.
    pub fn bind_type_alias(&mut self, name: String, type_alias: ligature_ast::TypeAlias) {
        self.environment.bind_type_alias(name, type_alias);
    }

    /// Bind a type constructor.
    pub fn bind_type_constructor(
        &mut self,
        name: String,
        type_constructor: ligature_ast::TypeConstructor,
    ) {
        self.environment
            .bind_type_constructor(name, type_constructor);
    }

    /// Bind a type class.
    pub fn bind_type_class(
        &mut self,
        name: String,
        type_class: ligature_ast::TypeClassDeclaration,
    ) {
        self.environment.bind_type_class(name, type_class);
    }

    /// Bind a type class instance.
    pub fn bind_instance(
        &mut self,
        class_name: String,
        instance: ligature_ast::InstanceDeclaration,
    ) {
        self.environment.bind_instance(class_name, instance);
    }

    /// Resolve and type check an imported module.
    pub fn resolve_and_check_import(&mut self, import: &ligature_ast::Import) -> AstResult<()> {
        // Validate the import path
        if import.path.is_empty() {
            return Err(AstError::InvalidImportPath {
                path: import.path.clone(),
                span: import.span,
            });
        }

        // Check for import cycles
        if self.detect_import_cycle(import) {
            return Err(AstError::ImportCycle {
                path: import.path.clone(),
                span: import.span,
            });
        }

        // Parse the import path to get module identifiers
        let (register_name, module_name) = self.parse_import_path(&import.path)?;
        let current_module_id = self.get_current_module_id();
        let target_module_id = format!("{register_name}:{module_name}");

        // Add dependency to the graph
        if let Some(current_id) = current_module_id {
            self.add_dependency(&current_id, &target_module_id);
        }

        // Load and type check the imported module
        let imported_module = self.load_module(&import.path)?;

        // Add imported bindings to the environment
        self.add_imported_bindings(import, &imported_module)?;

        Ok(())
    }

    /// Get the current module identifier for dependency tracking.
    fn get_current_module_id(&self) -> Option<String> {
        // This is a simplified implementation
        // In a real implementation, you'd track the current module being processed
        None
    }

    /// Detect import cycles using dependency graph.
    pub fn detect_import_cycle(&self, import: &ligature_ast::Import) -> bool {
        // Check for self-imports first
        if import.path == "self" || import.path == "." {
            return true;
        }

        // Parse the import path to get the module identifier
        let module_id = match self.parse_import_path(&import.path) {
            Ok((register, module)) => format!("{register}:{module}"),
            Err(_) => return false, // Invalid path, let other error handling deal with it
        };

        // Check if this import would create a cycle
        self.would_create_cycle(&module_id)
    }

    /// Check if adding a dependency would create a cycle.
    pub fn would_create_cycle(&self, target_module: &str) -> bool {
        // Use depth-first search to detect cycles
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();

        self.has_cycle_dfs(target_module, &mut visited, &mut rec_stack)
    }

    /// Depth-first search to detect cycles in the dependency graph.
    fn has_cycle_dfs(
        &self,
        module: &str,
        visited: &mut HashSet<String>,
        rec_stack: &mut HashSet<String>,
    ) -> bool {
        if rec_stack.contains(module) {
            return true; // Back edge found - cycle detected
        }

        if visited.contains(module) {
            return false; // Already processed, no cycle
        }

        visited.insert(module.to_string());
        rec_stack.insert(module.to_string());

        // Check all dependencies of this module
        if let Some(dependencies) = self.dependency_graph.get(module) {
            for dep in dependencies {
                if self.has_cycle_dfs(dep, visited, rec_stack) {
                    return true;
                }
            }
        }

        rec_stack.remove(module);
        false
    }

    /// Add a dependency to the graph.
    pub fn add_dependency(&mut self, from_module: &str, to_module: &str) {
        self.dependency_graph
            .entry(from_module.to_string())
            .or_default()
            .insert(to_module.to_string());
    }

    /// Get all dependencies of a module.
    pub fn get_dependencies(&self, module: &str) -> Option<&HashSet<String>> {
        self.dependency_graph.get(module)
    }

    /// Get the dependency graph for debugging.
    pub fn get_dependency_graph(&self) -> &HashMap<String, HashSet<String>> {
        &self.dependency_graph
    }

    /// Parse an import path to extract register and module names with support for nested paths.
    pub fn parse_import_path(&self, path: &str) -> AstResult<(String, String)> {
        let parts: Vec<&str> = path.split('.').collect();
        match parts.as_slice() {
            [register_name, module_name] => {
                Ok((register_name.to_string(), module_name.to_string()))
            }
            [register_name, _module_name, ..] => {
                // Support nested module paths by joining the remaining parts
                let nested_path = parts[1..].join("/");
                Ok((register_name.to_string(), nested_path))
            }
            _ => Err(AstError::ParseError {
                message: format!("Invalid import path format: {path}"),
                span: ligature_ast::Span::default(),
            }),
        }
    }

    /// Find a module within a specific register.
    fn find_module_in_register(
        &self,
        register_name: &str,
        module_name: &str,
    ) -> AstResult<PathBuf> {
        // First, find the register directory
        let register_path = self.find_register_directory(register_name)?;

        // Then find the module within that register
        self.find_in_register(&register_path, module_name)
    }

    /// Find a register directory by name.
    fn find_register_directory(&self, register_name: &str) -> AstResult<PathBuf> {
        // Search in register paths
        for register_path in &self.register_paths {
            let potential_register = register_path.join(register_name);
            if potential_register.exists() && potential_register.is_dir() {
                return Ok(potential_register);
            }
        }

        Err(AstError::ModuleNotFound {
            module: register_name.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Find a module within a register.
    fn find_in_register(&self, register_path: &Path, module_name: &str) -> AstResult<PathBuf> {
        // Look for register.toml to understand the register structure
        let register_manifest = register_path.join("register.toml");
        if register_manifest.exists() {
            if let Ok(exports) = self.parse_register_toml(&register_manifest) {
                // Check if the module is exported
                if let Some(export_path) = exports.get(module_name) {
                    let full_path = register_path.join(export_path);
                    if full_path.exists() && full_path.is_file() {
                        return Ok(full_path);
                    }
                }
            }
        }

        // Fallback: Look for the module file directly
        let module_file = register_path.join(format!("{module_name}.lig"));
        if module_file.exists() && module_file.is_file() {
            return Ok(module_file);
        }

        // Look in src/ subdirectory
        let src_module_file = register_path.join("src").join(format!("{module_name}.lig"));
        if src_module_file.exists() && src_module_file.is_file() {
            return Ok(src_module_file);
        }

        // For nested paths, try to resolve them
        if module_name.contains('/') {
            let path_parts: Vec<&str> = module_name.split('/').collect();
            let mut current_path = register_path.to_path_buf();

            for (i, part) in path_parts.iter().enumerate() {
                if i == path_parts.len() - 1 {
                    // Last part should be a .lig file
                    let lig_file = current_path.join(format!("{part}.lig"));
                    if lig_file.exists() && lig_file.is_file() {
                        return Ok(lig_file);
                    }
                } else {
                    // Intermediate parts should be directories
                    current_path = current_path.join(part);
                    if !current_path.exists() || !current_path.is_dir() {
                        break;
                    }
                }
            }
        }

        Err(AstError::ModuleNotFound {
            module: module_name.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Get the actual type from an exported item.
    pub fn get_exported_item_type(
        &mut self,
        module: &ligature_ast::Module,
        item_name: &str,
    ) -> AstResult<Type> {
        // Search through all declarations in the module to find the item
        for declaration in &module.declarations {
            match &declaration.kind {
                ligature_ast::DeclarationKind::Value(value_decl) => {
                    if value_decl.name == item_name {
                        // Infer the type from the value declaration
                        return self.infer_expression(&value_decl.value);
                    }
                }
                ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                    if type_alias.name == item_name {
                        // Return the type alias type
                        return Ok(type_alias.type_.clone());
                    }
                }
                ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                    if type_constructor.name == item_name {
                        // Return the type constructor body type
                        return Ok(type_constructor.body.clone());
                    }
                }
                ligature_ast::DeclarationKind::TypeClass(type_class) => {
                    if type_class.name == item_name {
                        // For type classes, return a module type representing the class
                        return Ok(Type::module(type_class.name.clone(), type_class.span));
                    }
                }
                ligature_ast::DeclarationKind::Instance(instance) => {
                    if instance.class_name == item_name {
                        // For instances, return a module type representing the class
                        return Ok(Type::module(instance.class_name.clone(), instance.span));
                    }
                }
                ligature_ast::DeclarationKind::Import(_) => {
                    // Skip imports
                    continue;
                }
                ligature_ast::DeclarationKind::Export(_) => {
                    // Skip exports
                    continue;
                }
            }
        }

        // If not found, return an error
        Err(AstError::UndefinedIdentifier {
            name: item_name.to_string(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Parse register.toml to understand exports.
    pub fn parse_register_toml(&self, manifest_path: &Path) -> AstResult<HashMap<String, String>> {
        use std::fs;

        use toml::Value;

        let content = fs::read_to_string(manifest_path).map_err(|e| AstError::ParseError {
            message: format!("Failed to read register.toml: {e}"),
            span: ligature_ast::Span::default(),
        })?;

        let value: Value = toml::from_str(&content).map_err(|e| AstError::ParseError {
            message: format!("Failed to parse register.toml: {e}"),
            span: ligature_ast::Span::default(),
        })?;

        let mut exports = HashMap::new();

        if let Some(exports_table) = value.get("exports") {
            if let Some(exports_map) = exports_table.as_table() {
                for (key, value) in exports_map {
                    if let Some(path) = value.as_str() {
                        exports.insert(key.clone(), path.to_string());
                    }
                }
            }
        }

        Ok(exports)
    }

    /// Load a module from a file path.
    fn load_module(&mut self, path: &str) -> AstResult<ligature_ast::Module> {
        // Check cache first
        if let Some(module) = self.module_cache.get(path) {
            return Ok(module.clone());
        }

        // Parse the import path to extract register and module names
        let (register_name, module_name) = self.parse_import_path(path)?;

        // Try to find the module file
        let module_path = self.find_module_in_register(&register_name, &module_name)?;

        // Load and parse the module
        let module_content =
            std::fs::read_to_string(&module_path).map_err(|e| AstError::ParseError {
                message: format!("Failed to read module file: {e}"),
                span: ligature_ast::Span::default(),
            })?;

        let mut parser = ligature_parser::Parser::new();
        let module_ast = parser.parse_module(&module_content)?;

        // Cache the module
        self.module_cache
            .insert(path.to_string(), module_ast.clone());

        Ok(module_ast)
    }

    /// Add imported bindings to the environment.
    fn add_imported_bindings(
        &mut self,
        import: &ligature_ast::Import,
        module: &ligature_ast::Module,
    ) -> AstResult<()> {
        match import.alias.as_ref() {
            Some(alias) => {
                // Import with alias - create a module value
                let module_type = Type::module(alias.clone(), import.span);
                self.environment.bind(alias.clone(), module_type);
            }
            None => {
                // Import without alias - add all exported bindings
                for declaration in &module.declarations {
                    if let ligature_ast::DeclarationKind::Export(export) = &declaration.kind {
                        // Add exported items to the environment
                        for item in &export.items {
                            let binding_name = item.alias.as_ref().unwrap_or(&item.name);
                            // Get the actual type from the exported item
                            let item_type = self.get_exported_item_type(module, &item.name)?;
                            self.environment.bind(binding_name.clone(), item_type);
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Check a type class declaration.
    pub fn check_type_class(
        &mut self,
        type_class: &ligature_ast::TypeClassDeclaration,
    ) -> AstResult<()> {
        // Check that the type class name is not already defined
        if self
            .environment
            .lookup_type_class(&type_class.name)
            .is_some()
        {
            return Err(AstError::DuplicateTypeClass {
                name: type_class.name.clone(),
                span: type_class.span,
            });
        }

        // Check that all superclass constraints are valid
        for superclass in &type_class.superclasses {
            self.check_type_class_constraint(superclass)?;
        }

        // Check that all method signatures are well-formed
        for method in &type_class.methods {
            self.check_type(&method.type_)?;
        }

        // Check that all type parameters are used in method signatures
        let used_params = self.collect_type_parameters_in_methods(&type_class.methods);
        for param in &type_class.parameters {
            if !used_params.contains(param) {
                return Err(AstError::UnusedTypeParameter {
                    parameter: param.clone(),
                    span: type_class.span,
                });
            }
        }

        Ok(())
    }

    /// Check a type class instance declaration.
    pub fn check_instance(
        &mut self,
        instance: &ligature_ast::InstanceDeclaration,
    ) -> AstResult<()> {
        // Check that the type class exists
        let type_class = self
            .environment
            .lookup_type_class(&instance.class_name)
            .ok_or_else(|| AstError::UndefinedTypeClass {
                name: instance.class_name.clone(),
                span: instance.span,
            })?
            .clone();

        // Check that the number of type arguments matches the class parameters
        if instance.type_arguments.len() != type_class.parameters.len() {
            return Err(AstError::TypeArgumentMismatch {
                expected: type_class.parameters.len(),
                found: instance.type_arguments.len(),
                span: instance.span,
            });
        }

        // Check that all type arguments are well-formed
        for type_arg in &instance.type_arguments {
            self.check_type(type_arg)?;
        }

        // Check that superclass constraints are satisfied
        for superclass in &type_class.superclasses {
            let instantiated_constraint =
                self.instantiate_type_class_constraint(superclass, &instance.type_arguments)?;
            self.check_type_class_constraint(&instantiated_constraint)?;
        }

        // Check that all required methods are implemented
        let implemented_methods: std::collections::HashSet<_> =
            instance.methods.iter().map(|m| &m.name).collect();

        for method in &type_class.methods {
            if !implemented_methods.contains(&method.name) {
                return Err(AstError::MissingMethod {
                    method: method.name.clone(),
                    class: instance.class_name.clone(),
                    span: instance.span,
                });
            }
        }

        // Check that method implementations match their signatures
        for method_impl in &instance.methods {
            let expected_signature = type_class
                .methods
                .iter()
                .find(|m| m.name == method_impl.name)
                .ok_or_else(|| AstError::UndefinedMethod {
                    method: method_impl.name.clone(),
                    class: instance.class_name.clone(),
                    span: method_impl.span,
                })?;

            let instantiated_signature =
                self.instantiate_type(&expected_signature.type_, &instance.type_arguments)?;
            let inferred_type = self.infer_expression(&method_impl.implementation)?;

            if !self.types_equal(&instantiated_signature, &inferred_type)? {
                return Err(AstError::MethodTypeMismatch {
                    method: method_impl.name.clone(),
                    expected: instantiated_signature,
                    found: inferred_type,
                    span: method_impl.span,
                });
            }
        }

        Ok(())
    }

    /// Check a type class constraint.
    pub fn check_type_class_constraint(
        &mut self,
        constraint: &ligature_ast::TypeClassConstraint,
    ) -> AstResult<()> {
        // Check that the type class exists
        if self
            .environment
            .lookup_type_class(&constraint.class_name)
            .is_none()
        {
            return Err(AstError::UndefinedTypeClass {
                name: constraint.class_name.clone(),
                span: constraint.span,
            });
        }

        // Check that all type arguments are well-formed
        for type_arg in &constraint.type_arguments {
            self.check_type(type_arg)?;
        }

        Ok(())
    }

    /// Resolve a type class constraint.
    pub fn resolve_type_class_constraint(
        &mut self,
        constraint: &ligature_ast::TypeClassConstraint,
    ) -> AstResult<()> {
        // Try to find a matching instance
        if let Some(_instance) = self
            .environment
            .find_matching_instance(&constraint.class_name, &constraint.type_arguments)
        {
            // Instance found - add constraints for superclasses if any
            if let Some(type_class) = self.environment.lookup_type_class(&constraint.class_name) {
                let superclasses = type_class.superclasses.clone();
                for superclass in &superclasses {
                    let instantiated_constraint = self.instantiate_type_class_constraint(
                        superclass,
                        &constraint.type_arguments,
                    )?;
                    self.resolve_type_class_constraint(&instantiated_constraint)?;
                }
            }
            Ok(())
        } else {
            // No instance found
            Err(AstError::NoInstanceFound {
                class: constraint.class_name.clone(),
                type_: constraint.type_arguments[0].clone(),
                span: constraint.span,
            })
        }
    }

    /// Instantiate a type class constraint with type arguments.
    fn instantiate_type_class_constraint(
        &mut self,
        constraint: &ligature_ast::TypeClassConstraint,
        type_arguments: &[Type],
    ) -> AstResult<ligature_ast::TypeClassConstraint> {
        let mut instantiated_args = Vec::new();

        for type_arg in &constraint.type_arguments {
            let instantiated = self.instantiate_type(type_arg, type_arguments)?;
            instantiated_args.push(instantiated);
        }

        Ok(ligature_ast::TypeClassConstraint {
            class_name: constraint.class_name.clone(),
            type_arguments: instantiated_args,
            span: constraint.span,
        })
    }

    /// Collect all type parameters used in method signatures.
    fn collect_type_parameters_in_methods(
        &self,
        methods: &[ligature_ast::MethodSignature],
    ) -> std::collections::HashSet<String> {
        let mut params = std::collections::HashSet::new();

        for method in methods {
            self.collect_type_parameters(&method.type_, &mut params);
        }

        params
    }

    /// Collect type parameters from a type.
    #[allow(clippy::only_used_in_recursion)]
    fn collect_type_parameters(
        &self,
        type_: &Type,
        params: &mut std::collections::HashSet<String>,
    ) {
        match &type_.kind {
            TypeKind::Variable(name) => {
                params.insert(name.clone());
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                self.collect_type_parameters(parameter, params);
                self.collect_type_parameters(return_type, params);
            }
            TypeKind::List(element_type) => {
                self.collect_type_parameters(element_type, params);
            }
            TypeKind::Record { fields } => {
                for field in fields {
                    self.collect_type_parameters(&field.type_, params);
                }
            }
            TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(field_type) = &variant.type_ {
                        self.collect_type_parameters(field_type, params);
                    }
                }
            }
            _ => {}
        }
    }

    /// Generalize a type by quantifying over free type variables.
    pub fn generalize(&self, type_: Type, environment: &TypeEnvironment) -> Type {
        let free_vars = self.free_type_variables(&type_);
        let bound_vars = self.bound_type_variables(environment);

        // Find variables that are free in the type but not bound in the environment
        let unbound_vars: Vec<String> = free_vars
            .into_iter()
            .filter(|var| !bound_vars.contains(var))
            .collect();

        if unbound_vars.is_empty() {
            type_
        } else {
            // Create a universal type quantifying over the unbound variables
            Type::new(
                TypeKind::ForAll {
                    parameter: unbound_vars[0].clone(),
                    body: Box::new(type_.clone()),
                },
                type_.span,
            )
        }
    }

    /// Get free type variables in a type.
    fn free_type_variables(&self, type_: &Type) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_free_variables(type_, &mut vars);
        vars
    }

    /// Collect free type variables in a type.
    #[allow(clippy::only_used_in_recursion)]
    fn collect_free_variables(&self, type_: &Type, vars: &mut Vec<String>) {
        match &type_.kind {
            TypeKind::Variable(var) => {
                if !vars.contains(var) {
                    vars.push(var.clone());
                }
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                self.collect_free_variables(parameter, vars);
                self.collect_free_variables(return_type, vars);
            }
            TypeKind::Record { fields } => {
                for field in fields {
                    self.collect_free_variables(&field.type_, vars);
                }
            }
            TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(type_) = &variant.type_ {
                        self.collect_free_variables(type_, vars);
                    }
                }
            }
            TypeKind::List(element_type) => {
                self.collect_free_variables(element_type, vars);
            }
            TypeKind::ForAll { body, .. } => {
                self.collect_free_variables(body, vars);
            }
            TypeKind::Exists { body, .. } => {
                self.collect_free_variables(body, vars);
            }
            TypeKind::Pi {
                parameter_type,
                return_type,
                ..
            } => {
                self.collect_free_variables(parameter_type, vars);
                self.collect_free_variables(return_type, vars);
            }
            TypeKind::Sigma {
                parameter_type,
                return_type,
                ..
            } => {
                self.collect_free_variables(parameter_type, vars);
                self.collect_free_variables(return_type, vars);
            }
            TypeKind::Application { function, argument } => {
                self.collect_free_variables(function, vars);
                self.collect_free_variables(argument, vars);
            }
            _ => {}
        }
    }

    /// Get bound type variables in the environment.
    fn bound_type_variables(&self, _environment: &TypeEnvironment) -> Vec<String> {
        // This is a simplified implementation
        // In a full implementation, we'd track bound variables in the environment
        Vec::new()
    }

    /// Instantiate a universal type by substituting type variables.
    pub fn instantiate(&mut self, type_: &Type) -> Type {
        match &type_.kind {
            TypeKind::ForAll { parameter, body } => {
                let fresh_var = self.fresh_type_variable();
                self.substitute_type_variable(body, parameter, &fresh_var)
            }
            _ => type_.clone(),
        }
    }

    /// Substitute a type variable in a type.
    #[allow(clippy::only_used_in_recursion)]
    pub fn substitute_type_variable(&self, type_: &Type, var: &str, replacement: &Type) -> Type {
        match &type_.kind {
            TypeKind::Variable(v) if v == var => replacement.clone(),
            TypeKind::Variable(_) => type_.clone(),
            TypeKind::Function {
                parameter,
                return_type,
            } => Type::function(
                self.substitute_type_variable(parameter, var, replacement),
                self.substitute_type_variable(return_type, var, replacement),
                type_.span,
            ),
            TypeKind::Record { fields } => {
                let new_fields = fields
                    .iter()
                    .map(|field| ligature_ast::TypeField {
                        name: field.name.clone(),
                        type_: self.substitute_type_variable(&field.type_, var, replacement),
                        span: field.span,
                    })
                    .collect();
                Type::record(new_fields, type_.span)
            }
            TypeKind::Union { variants } => {
                let new_variants = variants
                    .iter()
                    .map(|variant| ligature_ast::TypeVariant {
                        name: variant.name.clone(),
                        type_: variant
                            .type_
                            .as_ref()
                            .map(|t| self.substitute_type_variable(t, var, replacement)),
                        span: variant.span,
                    })
                    .collect();
                Type::union(new_variants, type_.span)
            }
            TypeKind::List(element_type) => Type::list(
                self.substitute_type_variable(element_type, var, replacement),
                type_.span,
            ),
            TypeKind::Pi {
                parameter,
                parameter_type,
                return_type,
            } => {
                // Don't substitute in the parameter name itself
                if parameter == var {
                    type_.clone()
                } else {
                    Type::new(
                        TypeKind::Pi {
                            parameter: parameter.clone(),
                            parameter_type: Box::new(self.substitute_type_variable(
                                parameter_type,
                                var,
                                replacement,
                            )),
                            return_type: Box::new(self.substitute_type_variable(
                                return_type,
                                var,
                                replacement,
                            )),
                        },
                        type_.span,
                    )
                }
            }
            TypeKind::Sigma {
                parameter,
                parameter_type,
                return_type,
            } => {
                // Don't substitute in the parameter name itself
                if parameter == var {
                    type_.clone()
                } else {
                    Type::new(
                        TypeKind::Sigma {
                            parameter: parameter.clone(),
                            parameter_type: Box::new(self.substitute_type_variable(
                                parameter_type,
                                var,
                                replacement,
                            )),
                            return_type: Box::new(self.substitute_type_variable(
                                return_type,
                                var,
                                replacement,
                            )),
                        },
                        type_.span,
                    )
                }
            }
            _ => type_.clone(),
        }
    }

    /// Instantiate a type with type arguments.
    pub fn instantiate_type(&mut self, type_: &Type, type_arguments: &[Type]) -> AstResult<Type> {
        match &type_.kind {
            TypeKind::ForAll { parameter, body } => {
                if type_arguments.len() != 1 {
                    return Err(AstError::TypeArgumentMismatch {
                        expected: 1,
                        found: type_arguments.len(),
                        span: type_.span,
                    });
                }
                let instantiated_body =
                    self.substitute_type_variable(body, parameter, &type_arguments[0]);
                Ok(instantiated_body)
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                let instantiated_parameter = self.instantiate_type(parameter, type_arguments)?;
                let instantiated_return_type =
                    self.instantiate_type(return_type, type_arguments)?;
                Ok(Type::function(
                    instantiated_parameter,
                    instantiated_return_type,
                    type_.span,
                ))
            }
            TypeKind::Record { fields } => {
                let mut new_fields = Vec::new();
                for field in fields {
                    let instantiated_type = self.instantiate_type(&field.type_, type_arguments)?;
                    new_fields.push(ligature_ast::TypeField {
                        name: field.name.clone(),
                        type_: instantiated_type,
                        span: field.span,
                    });
                }
                Ok(Type::record(new_fields, type_.span))
            }
            TypeKind::Union { variants } => {
                let mut new_variants = Vec::new();
                for variant in variants {
                    let instantiated_type = if let Some(t) = &variant.type_ {
                        Some(self.instantiate_type(t, type_arguments)?)
                    } else {
                        None
                    };
                    new_variants.push(ligature_ast::TypeVariant {
                        name: variant.name.clone(),
                        type_: instantiated_type,
                        span: variant.span,
                    });
                }
                Ok(Type::union(new_variants, type_.span))
            }
            TypeKind::List(element_type) => {
                let instantiated_element_type =
                    self.instantiate_type(element_type, type_arguments)?;
                Ok(Type::list(instantiated_element_type, type_.span))
            }
            TypeKind::Pi {
                parameter,
                parameter_type,
                return_type,
            } => {
                let instantiated_parameter_type =
                    self.instantiate_type(parameter_type, type_arguments)?;
                let instantiated_return_type =
                    self.instantiate_type(return_type, type_arguments)?;
                Ok(Type::new(
                    TypeKind::Pi {
                        parameter: parameter.clone(),
                        parameter_type: Box::new(instantiated_parameter_type),
                        return_type: Box::new(instantiated_return_type),
                    },
                    type_.span,
                ))
            }
            TypeKind::Sigma {
                parameter,
                parameter_type,
                return_type,
            } => {
                let instantiated_parameter_type =
                    self.instantiate_type(parameter_type, type_arguments)?;
                let instantiated_return_type =
                    self.instantiate_type(return_type, type_arguments)?;
                Ok(Type::new(
                    TypeKind::Sigma {
                        parameter: parameter.clone(),
                        parameter_type: Box::new(instantiated_parameter_type),
                        return_type: Box::new(instantiated_return_type),
                    },
                    type_.span,
                ))
            }
            TypeKind::Exists { parameter, body } => {
                let instantiated_body = self.instantiate_type(body, type_arguments)?;
                Ok(Type::new(
                    TypeKind::Exists {
                        parameter: parameter.clone(),
                        body: Box::new(instantiated_body),
                    },
                    type_.span,
                ))
            }
            TypeKind::Application { function, argument } => {
                let instantiated_function = self.instantiate_type(function, type_arguments)?;
                let instantiated_argument = self.instantiate_type(argument, type_arguments)?;
                Ok(Type::new(
                    TypeKind::Application {
                        function: Box::new(instantiated_function),
                        argument: Box::new(instantiated_argument),
                    },
                    type_.span,
                ))
            }
            _ => Ok(type_.clone()),
        }
    }

    /// Solve all constraints.
    pub fn solve_constraints(&mut self) -> AstResult<()> {
        match self.constraint_solver.solve() {
            Ok(_) => Ok(()),
            Err(_msg) => Err(AstError::InvalidTypeAnnotation {
                span: ligature_ast::Span::default(),
            }),
        }
    }

    /// Generate a cache key for an expression.
    #[allow(clippy::only_used_in_recursion)]
    fn expression_to_cache_key(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Literal(literal) => {
                format!("lit:{literal:?}")
            }
            ExprKind::Variable(name) => {
                format!("var:{name}")
            }
            ExprKind::Application { function, argument } => {
                format!(
                    "app:{}->{}",
                    self.expression_to_cache_key(function),
                    self.expression_to_cache_key(argument)
                )
            }
            ExprKind::Abstraction {
                parameter,
                parameter_type,
                body,
            } => {
                let param_type_key = parameter_type
                    .as_ref()
                    .map(|t| format!("{:?}", t.kind))
                    .unwrap_or_else(|| "none".to_string());
                format!(
                    "abs:{}:{}->{}",
                    parameter,
                    param_type_key,
                    self.expression_to_cache_key(body)
                )
            }
            ExprKind::Let { name, value, body } => {
                format!(
                    "let:{}={}->{}",
                    name,
                    self.expression_to_cache_key(value),
                    self.expression_to_cache_key(body)
                )
            }
            ExprKind::Record { fields } => {
                let field_keys: Vec<String> = fields
                    .iter()
                    .map(|f| format!("{}:{}", f.name, self.expression_to_cache_key(&f.value)))
                    .collect();
                format!("record:{{{}}}", field_keys.join(","))
            }
            ExprKind::FieldAccess { record, field } => {
                format!("field:{}:{}", self.expression_to_cache_key(record), field)
            }
            ExprKind::Union { variant, value } => {
                let value_key = value
                    .as_ref()
                    .map(|v| self.expression_to_cache_key(v))
                    .unwrap_or_else(|| "none".to_string());
                format!("union:{variant}:{value_key}")
            }
            ExprKind::Match { scrutinee, cases } => {
                let case_keys: Vec<String> = cases
                    .iter()
                    .map(|c| {
                        format!(
                            "{:?}->{}",
                            c.pattern,
                            self.expression_to_cache_key(&c.expression)
                        )
                    })
                    .collect();
                format!(
                    "match:{}->[{}]",
                    self.expression_to_cache_key(scrutinee),
                    case_keys.join(",")
                )
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                format!(
                    "if:{}?{}:{}",
                    self.expression_to_cache_key(condition),
                    self.expression_to_cache_key(then_branch),
                    self.expression_to_cache_key(else_branch)
                )
            }
            ExprKind::BinaryOp {
                operator,
                left,
                right,
            } => {
                format!(
                    "bin:{:?}:{}:{}",
                    operator,
                    self.expression_to_cache_key(left),
                    self.expression_to_cache_key(right)
                )
            }
            ExprKind::UnaryOp { operator, operand } => {
                format!(
                    "unary:{:?}:{}",
                    operator,
                    self.expression_to_cache_key(operand)
                )
            }
            ExprKind::Annotated {
                expression,
                type_annotation,
            } => {
                format!(
                    "annot:{}:{:?}",
                    self.expression_to_cache_key(expression),
                    type_annotation.kind
                )
            }
        }
    }

    /// Add a search path for module resolution.
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    /// Add a register path for module resolution.
    pub fn add_register_path(&mut self, path: PathBuf) {
        self.register_paths.push(path);
    }

    /// Clear the module cache.
    pub fn clear_module_cache(&mut self) {
        self.module_cache.clear();
    }
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}
