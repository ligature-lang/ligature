//! Constraint solver for type inference.

use std::collections::HashMap;

use ligature_ast::{Span, Type, TypeKind};
use ligature_error::StandardResult;

use crate::error::TypeError;

/// A type constraint.
#[derive(Debug, Clone, PartialEq)]
pub enum Constraint {
    /// Equality constraint: left = right
    Equality(Type, Type),
    /// Subtype constraint: left <: right
    Subtype(Type, Type),
    /// Instance constraint: type implements class
    Instance(Type, String),
    /// Type class constraint: type implements class with context
    ClassConstraint(Type, String, Vec<Constraint>),
}

/// A constraint solver for type inference.
#[derive(Clone)]
pub struct ConstraintSolver {
    /// Current substitution (type variable -> type).
    substitution: HashMap<String, Type>,
    /// Pending constraints to solve.
    constraints: Vec<Constraint>,
    /// Type cache for performance optimization.
    type_cache: HashMap<String, Type>,
    /// Cache for substitution applications.
    substitution_cache: HashMap<String, Type>,
}

impl ConstraintSolver {
    /// Create a new constraint solver.
    pub fn new() -> Self {
        Self {
            substitution: HashMap::new(),
            constraints: Vec::new(),
            type_cache: HashMap::new(),
            substitution_cache: HashMap::new(),
        }
    }

    /// Add a constraint to be solved.
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Solve all constraints and return the final substitution.
    #[allow(clippy::type_complexity)]
    pub fn solve(&mut self) -> StandardResult<HashMap<String, Type>> {
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 1000; // Prevent infinite loops

        while !self.constraints.is_empty() && iterations < MAX_ITERATIONS {
            iterations += 1;

            // Process constraints in order, but prioritize simple constraints
            let mut i = 0;
            while i < self.constraints.len() {
                let constraint = self.constraints[i].clone();

                // Try to solve the constraint
                match self.solve_constraint(constraint) {
                    Ok(()) => {
                        // Constraint was solved, remove it
                        self.constraints.remove(i);
                        // Don't increment i since we removed an element
                    }
                    Err(_) => {
                        // Constraint couldn't be solved yet, move to next
                        i += 1;
                    }
                }
            }

            // If no constraints were solved in this iteration, we're done
            if i == self.constraints.len() && !self.constraints.is_empty() {
                break;
            }
        }

        if !self.constraints.is_empty() {
            return Err(TypeError::ConstraintSolvingFailed {
                message: format!(
                    "Failed to solve all constraints after {MAX_ITERATIONS} iterations"
                ),
                span: Span::default(),
            }
            .into());
        }

        Ok(self.substitution.clone())
    }

    /// Solve a single constraint.
    fn solve_constraint(&mut self, constraint: Constraint) -> StandardResult<()> {
        match constraint {
            Constraint::Equality(left, right) => self.solve_equality(left, right),
            Constraint::Subtype(left, right) => self.solve_subtype(left, right),
            Constraint::Instance(type_, class) => self.solve_instance(type_, class),
            Constraint::ClassConstraint(type_, class, context) => {
                self.solve_class_constraint_with_ambiguity_check(type_, class, context)
            }
        }
    }

    /// Solve an equality constraint.
    fn solve_equality(&mut self, left: Type, right: Type) -> StandardResult<()> {
        let left = self.apply_substitution(left);
        let right = self.apply_substitution(right);

        match (&left.kind, &right.kind) {
            // Same types are always equal
            (TypeKind::Unit, TypeKind::Unit)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::String, TypeKind::String)
            | (TypeKind::Integer, TypeKind::Integer)
            | (TypeKind::Float, TypeKind::Float) => Ok(()),

            // Type variables
            (TypeKind::Variable(var), _) => self.unify_variable(var.clone(), right),
            (_, TypeKind::Variable(var)) => self.unify_variable(var.clone(), left),

            // Function types
            (
                TypeKind::Function {
                    parameter: p1,
                    return_type: r1,
                },
                TypeKind::Function {
                    parameter: p2,
                    return_type: r2,
                },
            ) => {
                self.add_constraint(Constraint::Equality(*p1.clone(), *p2.clone()));
                self.add_constraint(Constraint::Equality(*r1.clone(), *r2.clone()));
                Ok(())
            }

            // Record types
            (TypeKind::Record { fields: f1 }, TypeKind::Record { fields: f2 }) => {
                if f1.len() != f2.len() {
                    return Err(TypeError::UnificationFailed {
                        left: format!("{:?}", left.kind),
                        right: format!("{:?}", right.kind),
                        span: left.span,
                    }
                    .into());
                }

                for (field1, field2) in f1.iter().zip(f2.iter()) {
                    if field1.name != field2.name {
                        return Err(TypeError::UnificationFailed {
                            left: format!("{:?}", left.kind),
                            right: format!("{:?}", right.kind),
                            span: left.span,
                        }
                        .into());
                    }
                    self.add_constraint(Constraint::Equality(
                        field1.type_.clone(),
                        field2.type_.clone(),
                    ));
                }
                Ok(())
            }

            // Union types
            (TypeKind::Union { variants: v1 }, TypeKind::Union { variants: v2 }) => {
                if v1.len() != v2.len() {
                    return Err(TypeError::UnificationFailed {
                        left: format!("{:?}", left.kind),
                        right: format!("{:?}", right.kind),
                        span: left.span,
                    }
                    .into());
                }

                for (variant1, variant2) in v1.iter().zip(v2.iter()) {
                    if variant1.name != variant2.name {
                        return Err(TypeError::UnificationFailed {
                            left: format!("{:?}", left.kind),
                            right: format!("{:?}", right.kind),
                            span: left.span,
                        }
                        .into());
                    }
                    match (&variant1.type_, &variant2.type_) {
                        (Some(t1), Some(t2)) => {
                            self.add_constraint(Constraint::Equality(t1.clone(), t2.clone()));
                        }
                        (None, None) => {}
                        _ => {
                            return Err(TypeError::UnificationFailed {
                                left: format!("{:?}", left.kind),
                                right: format!("{:?}", right.kind),
                                span: left.span,
                            }
                            .into());
                        }
                    }
                }
                Ok(())
            }

            // List types
            (TypeKind::List(e1), TypeKind::List(e2)) => {
                self.add_constraint(Constraint::Equality(*e1.clone(), *e2.clone()));
                Ok(())
            }

            // Incompatible types
            _ => Err(TypeError::UnificationFailed {
                left: format!("{:?}", left.kind),
                right: format!("{:?}", right.kind),
                span: left.span,
            }
            .into()),
        }
    }

    /// Solve a subtype constraint.
    fn solve_subtype(&mut self, left: Type, right: Type) -> StandardResult<()> {
        let left = self.apply_substitution(left);
        let right = self.apply_substitution(right);

        match (&left.kind, &right.kind) {
            // Same types are subtypes of themselves
            (TypeKind::Unit, TypeKind::Unit)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::String, TypeKind::String)
            | (TypeKind::Integer, TypeKind::Integer)
            | (TypeKind::Float, TypeKind::Float) => Ok(()),

            // Integer is a subtype of Float
            (TypeKind::Integer, TypeKind::Float) => Ok(()),

            // Type variables
            (TypeKind::Variable(var), _) => self.unify_variable(var.clone(), right),
            (_, TypeKind::Variable(var)) => self.unify_variable(var.clone(), left),

            // Function types (contravariant in parameter, covariant in return)
            (
                TypeKind::Function {
                    parameter: p1,
                    return_type: r1,
                },
                TypeKind::Function {
                    parameter: p2,
                    return_type: r2,
                },
            ) => {
                // Contravariant: parameter type of supertype must be subtype of parameter type of subtype
                self.add_constraint(Constraint::Subtype(*p2.clone(), *p1.clone()));
                // Covariant: return type of subtype must be subtype of return type of supertype
                self.add_constraint(Constraint::Subtype(*r1.clone(), *r2.clone()));
                Ok(())
            }

            // Record types (width and depth subtyping)
            (TypeKind::Record { fields: f1 }, TypeKind::Record { fields: f2 }) => {
                // Width subtyping: supertype must have all fields of subtype
                for field2 in f2 {
                    let mut found = false;
                    for field1 in f1 {
                        if field1.name == field2.name {
                            // Depth subtyping: field types must be in subtype relationship
                            self.add_constraint(Constraint::Subtype(
                                field1.type_.clone(),
                                field2.type_.clone(),
                            ));
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(TypeError::SubtypingFailed {
                            left: format!("{:?}", left.kind),
                            right: format!("{:?}", right.kind),
                            suggestion: format!(
                                "Record subtyping failed: supertype missing required field '{}'. \
                                 Available fields: [{}]",
                                field2.name,
                                f1.iter()
                                    .map(|f| f.name.as_str())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            span: left.span,
                        }
                        .into());
                    }
                }
                Ok(())
            }

            // Union types (width and depth subtyping)
            (TypeKind::Union { variants: v1 }, TypeKind::Union { variants: v2 }) => {
                // Width subtyping: supertype must have all variants of subtype
                for variant1 in v1 {
                    let mut found = false;
                    for variant2 in v2 {
                        if variant1.name == variant2.name {
                            // Depth subtyping: variant types must be in subtype relationship
                            match (&variant1.type_, &variant2.type_) {
                                (Some(t1), Some(t2)) => {
                                    self.add_constraint(Constraint::Subtype(
                                        t1.clone(),
                                        t2.clone(),
                                    ));
                                }
                                (None, None) => {}
                                _ => {
                                    return Err(TypeError::SubtypingFailed {
                                        left: format!("{:?}", left.kind),
                                        right: format!("{:?}", right.kind),
                                        suggestion: format!(
                                            "Union subtyping failed: variants '{}' have different \
                                             associated types",
                                            variant1.name
                                        ),
                                        span: left.span,
                                    }
                                    .into());
                                }
                            }
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(TypeError::SubtypingFailed {
                            left: format!("{:?}", left.kind),
                            right: format!("{:?}", right.kind),
                            suggestion: format!(
                                "Union subtyping failed: supertype missing required variant '{}'. \
                                 Available variants: [{}]",
                                variant1.name,
                                v2.iter()
                                    .map(|v| v.name.as_str())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            span: left.span,
                        }
                        .into());
                    }
                }
                Ok(())
            }

            // List types
            (TypeKind::List(e1), TypeKind::List(e2)) => {
                self.add_constraint(Constraint::Subtype(*e1.clone(), *e2.clone()));
                Ok(())
            }

            // Incompatible types
            _ => Err(TypeError::SubtypingFailed {
                left: format!("{:?}", left.kind),
                right: format!("{:?}", right.kind),
                suggestion: "Consider if these types should be related or if there's a type error \
                             in your code."
                    .to_string(),
                span: left.span,
            }
            .into()),
        }
    }

    /// Solve an instance constraint.
    pub fn solve_instance(&mut self, type_: Type, class: String) -> StandardResult<()> {
        // Apply current substitution to the type
        let type_ = self.apply_substitution(type_);

        // Check for built-in type class instances
        if self.check_builtin_instance(&type_, &class) {
            return Ok(());
        }

        // Check for user-defined type class instances
        if self.check_user_instance(&type_, &class) {
            return Ok(());
        }

        // Check for derived instances (e.g., for records and unions)
        if self.check_derived_instance(&type_, &class) {
            return Ok(());
        }

        // If no instance found, provide more detailed error information
        let available_instances = self.get_available_instances(&class);
        if available_instances.is_empty() {
            Err(TypeError::TypeClassConstraintUnsatisfied {
                type_: format!("{:?}", type_.kind),
                class,
                span: type_.span,
            }
            .into())
        } else {
            Err(TypeError::TypeClassConstraintUnsatisfiedWithInstances {
                type_: format!("{:?}", type_.kind),
                class,
                available_instances: available_instances.join(", "),
                span: type_.span,
            }
            .into())
        }
    }

    /// Solve a class constraint with context.
    #[allow(dead_code)]
    fn solve_class_constraint(
        &mut self,
        type_: Type,
        class: String,
        context: Vec<Constraint>,
    ) -> StandardResult<()> {
        // First, try to find a matching instance
        // This is a simplified implementation - in practice, you'd need to integrate with the type environment
        if self.check_builtin_instance(&type_, &class) {
            // Built-in instance found, solve context constraints
            for constraint in context {
                self.add_constraint(constraint);
            }
            Ok(())
        } else {
            // No instance found
            Err(TypeError::TypeClassConstraintUnsatisfied {
                type_: format!("{:?}", type_.kind),
                class,
                span: type_.span,
            }
            .into())
        }
    }

    /// Solve a class constraint with ambiguity checking.
    fn solve_class_constraint_with_ambiguity_check(
        &mut self,
        type_: Type,
        class: String,
        context: Vec<Constraint>,
    ) -> StandardResult<()> {
        // Find all matching instances
        let mut matching_instances = Vec::new();

        if self.check_builtin_instance(&type_, &class) {
            matching_instances.push("built-in".to_string());
        }

        if self.check_user_instance(&type_, &class) {
            matching_instances.push("user-defined".to_string());
        }

        if self.check_derived_instance(&type_, &class) {
            matching_instances.push("derived".to_string());
        }

        match matching_instances.len() {
            0 => {
                // No instance found
                let available_instances = self.get_available_instances(&class);
                if available_instances.is_empty() {
                    Err(TypeError::TypeClassConstraintUnsatisfied {
                        type_: format!("{:?}", type_.kind),
                        class,
                        span: type_.span,
                    }
                    .into())
                } else {
                    Err(TypeError::TypeClassConstraintUnsatisfiedWithInstances {
                        type_: format!("{:?}", type_.kind),
                        class,
                        available_instances: available_instances.join(", "),
                        span: type_.span,
                    }
                    .into())
                }
            }
            1 => {
                // Exactly one instance found, solve context constraints
                for constraint in context {
                    self.add_constraint(constraint);
                }
                Ok(())
            }
            _ => {
                // Multiple instances found - ambiguous
                Err(TypeError::AmbiguousTypeClassResolution {
                    type_: format!("{:?}", type_.kind),
                    class,
                    candidate_instances: matching_instances,
                    span: type_.span,
                }
                .into())
            }
        }
    }

    /// Check if a type has a built-in instance for a class.
    #[allow(clippy::only_used_in_recursion)]
    fn check_builtin_instance(&self, type_: &Type, class: &str) -> bool {
        match (type_, class) {
            // Built-in instances for common type classes
            (
                Type {
                    kind: TypeKind::Integer,
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::Integer,
                    ..
                },
                "Ord",
            ) => true,
            (
                Type {
                    kind: TypeKind::Integer,
                    ..
                },
                "Show",
            ) => true,
            (
                Type {
                    kind: TypeKind::Integer,
                    ..
                },
                "Num",
            ) => true,

            (
                Type {
                    kind: TypeKind::String,
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::String,
                    ..
                },
                "Ord",
            ) => true,
            (
                Type {
                    kind: TypeKind::String,
                    ..
                },
                "Show",
            ) => true,

            (
                Type {
                    kind: TypeKind::Bool,
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::Bool,
                    ..
                },
                "Ord",
            ) => true,
            (
                Type {
                    kind: TypeKind::Bool,
                    ..
                },
                "Show",
            ) => true,

            (
                Type {
                    kind: TypeKind::Unit,
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::Unit,
                    ..
                },
                "Show",
            ) => true,

            // List instances
            (
                Type {
                    kind: TypeKind::List(element_type),
                    ..
                },
                "Eq",
            ) => self.check_builtin_instance(element_type, "Eq"),
            (
                Type {
                    kind: TypeKind::List(element_type),
                    ..
                },
                "Ord",
            ) => self.check_builtin_instance(element_type, "Ord"),
            (
                Type {
                    kind: TypeKind::List(element_type),
                    ..
                },
                "Show",
            ) => self.check_builtin_instance(element_type, "Show"),

            // Function instances (for some classes)
            (
                Type {
                    kind: TypeKind::Function { return_type, .. },
                    ..
                },
                "Show",
            ) => self.check_builtin_instance(return_type, "Show"),

            // Variable types - assume they can have instances (will be resolved during unification)
            (
                Type {
                    kind: TypeKind::Variable(_),
                    ..
                },
                _,
            ) => true,

            _ => false,
        }
    }

    /// Check if a type has a user-defined instance for a class.
    fn check_user_instance(&self, _type_: &Type, _class: &str) -> bool {
        // This would integrate with the type environment to check for user-defined instances
        // For now, return false as we'll implement this in the type inference engine
        false
    }

    /// Check if a type has a derived instance for a class.
    fn check_derived_instance(&self, type_: &Type, class: &str) -> bool {
        // This is a simplified implementation
        // In a full implementation, this would check for derived instances
        // based on the structure of the type (records, unions, etc.)
        match (type_, class) {
            // Derived instances for records
            (
                Type {
                    kind: TypeKind::Record { .. },
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::Record { .. },
                    ..
                },
                "Show",
            ) => true,

            // Derived instances for unions
            (
                Type {
                    kind: TypeKind::Union { .. },
                    ..
                },
                "Eq",
            ) => true,
            (
                Type {
                    kind: TypeKind::Union { .. },
                    ..
                },
                "Show",
            ) => true,

            _ => false,
        }
    }

    /// Get available instances for a type class.
    fn get_available_instances(&self, class: &str) -> Vec<String> {
        let mut instances = Vec::new();

        // Add built-in instances
        match class {
            "Eq" => {
                instances.extend(vec![
                    "Integer".to_string(),
                    "String".to_string(),
                    "Bool".to_string(),
                    "Unit".to_string(),
                ]);
            }
            "Ord" => {
                instances.extend(vec!["Integer".to_string(), "String".to_string()]);
            }
            "Show" => {
                instances.extend(vec![
                    "Integer".to_string(),
                    "String".to_string(),
                    "Bool".to_string(),
                    "Unit".to_string(),
                ]);
            }
            "Num" => {
                instances.extend(vec!["Integer".to_string()]);
            }
            _ => {}
        }

        instances
    }

    /// Unify a type variable with a type.
    fn unify_variable(&mut self, var: String, type_: Type) -> StandardResult<()> {
        // Check for occurs check (prevent infinite types)
        if self.occurs_in(&var, &type_) {
            return Err(TypeError::OccursCheckFailed {
                variable: var,
                type_: format!("{:?}", type_.kind),
                span: type_.span,
            }
            .into());
        }

        // Apply current substitution to the type
        let type_ = self.apply_substitution(type_);

        // Add the substitution
        self.substitution.insert(var, type_);
        Ok(())
    }

    /// Check if a type variable occurs in a type.
    #[allow(clippy::only_used_in_recursion)]
    fn occurs_in(&self, var: &str, type_: &Type) -> bool {
        match &type_.kind {
            TypeKind::Variable(v) => v == var,
            TypeKind::Function {
                parameter,
                return_type,
            } => self.occurs_in(var, parameter) || self.occurs_in(var, return_type),
            TypeKind::Record { fields } => {
                fields.iter().any(|field| self.occurs_in(var, &field.type_))
            }
            TypeKind::Union { variants } => variants.iter().any(|variant| {
                variant
                    .type_
                    .as_ref()
                    .is_some_and(|t| self.occurs_in(var, t))
            }),
            TypeKind::List(element_type) => self.occurs_in(var, element_type),
            TypeKind::ForAll { body, .. } => self.occurs_in(var, body),
            TypeKind::Exists { body, .. } => self.occurs_in(var, body),
            TypeKind::Pi {
                parameter_type,
                return_type,
                ..
            } => self.occurs_in(var, parameter_type) || self.occurs_in(var, return_type),
            TypeKind::Sigma {
                parameter_type,
                return_type,
                ..
            } => self.occurs_in(var, parameter_type) || self.occurs_in(var, return_type),
            TypeKind::Application { function, argument } => {
                self.occurs_in(var, function) || self.occurs_in(var, argument)
            }
            _ => false,
        }
    }

    /// Apply the current substitution to a type.
    pub fn apply_substitution(&mut self, type_: Type) -> Type {
        // Create a cache key for this type
        let cache_key = self.type_to_cache_key(&type_);

        // Check if we have a cached result
        if let Some(cached) = self.substitution_cache.get(&cache_key) {
            return cached.clone();
        }

        let result = match &type_.kind {
            TypeKind::Variable(var) => {
                if let Some(substituted) = self.substitution.get(var) {
                    self.apply_substitution(substituted.clone())
                } else {
                    type_
                }
            }
            TypeKind::Function {
                parameter,
                return_type,
            } => Type::function(
                self.apply_substitution(*parameter.clone()),
                self.apply_substitution(*return_type.clone()),
                type_.span,
            ),
            TypeKind::Record { fields } => {
                let new_fields = fields
                    .iter()
                    .map(|field| ligature_ast::TypeField {
                        name: field.name.clone(),
                        type_: self.apply_substitution(field.type_.clone()),
                        span: field.span.clone(),
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
                            .map(|t| self.apply_substitution(t.clone())),
                        span: variant.span.clone(),
                    })
                    .collect();
                Type::union(new_variants, type_.span)
            }
            TypeKind::List(element_type) => {
                Type::list(self.apply_substitution(*element_type.clone()), type_.span)
            }
            TypeKind::ForAll { parameter, body } => Type::new(
                TypeKind::ForAll {
                    parameter: parameter.clone(),
                    body: Box::new(self.apply_substitution(*body.clone())),
                },
                type_.span,
            ),
            TypeKind::Exists { parameter, body } => Type::new(
                TypeKind::Exists {
                    parameter: parameter.clone(),
                    body: Box::new(self.apply_substitution(*body.clone())),
                },
                type_.span,
            ),
            TypeKind::Pi {
                parameter,
                parameter_type,
                return_type,
            } => Type::new(
                TypeKind::Pi {
                    parameter: parameter.clone(),
                    parameter_type: Box::new(self.apply_substitution(*parameter_type.clone())),
                    return_type: Box::new(self.apply_substitution(*return_type.clone())),
                },
                type_.span,
            ),
            TypeKind::Sigma {
                parameter,
                parameter_type,
                return_type,
            } => Type::new(
                TypeKind::Sigma {
                    parameter: parameter.clone(),
                    parameter_type: Box::new(self.apply_substitution(*parameter_type.clone())),
                    return_type: Box::new(self.apply_substitution(*return_type.clone())),
                },
                type_.span,
            ),
            TypeKind::Application { function, argument } => Type::new(
                TypeKind::Application {
                    function: Box::new(self.apply_substitution(*function.clone())),
                    argument: Box::new(self.apply_substitution(*argument.clone())),
                },
                type_.span,
            ),
            _ => type_,
        };

        // Cache the result
        self.substitution_cache.insert(cache_key, result.clone());
        result
    }

    /// Generate a cache key for a type.
    #[allow(clippy::only_used_in_recursion)]
    fn type_to_cache_key(&self, type_: &Type) -> String {
        match &type_.kind {
            TypeKind::Variable(var) => format!("var:{var}"),
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                format!(
                    "fun:{}->{}",
                    self.type_to_cache_key(parameter),
                    self.type_to_cache_key(return_type)
                )
            }
            TypeKind::Record { fields } => {
                let field_keys: Vec<String> = fields
                    .iter()
                    .map(|f| format!("{}:{}", f.name, self.type_to_cache_key(&f.type_)))
                    .collect();
                format!("record:{{{}}}", field_keys.join(","))
            }
            TypeKind::Union { variants } => {
                let variant_keys: Vec<String> = variants
                    .iter()
                    .map(|v| {
                        let type_key = v
                            .type_
                            .as_ref()
                            .map(|t| self.type_to_cache_key(t))
                            .unwrap_or_else(|| "unit".to_string());
                        format!("{}:{}", v.name, type_key)
                    })
                    .collect();
                format!("union:[{}]", variant_keys.join(","))
            }
            TypeKind::List(element_type) => {
                format!("list:[{}]", self.type_to_cache_key(element_type))
            }
            _ => format!("{:?}", type_.kind),
        }
    }

    /// Get the current substitution.
    pub fn substitution(&self) -> &HashMap<String, Type> {
        &self.substitution
    }

    /// Clear all constraints and substitutions.
    pub fn clear(&mut self) {
        self.substitution.clear();
        self.constraints.clear();
        self.type_cache.clear();
        self.substitution_cache.clear();
    }
}

impl Default for ConstraintSolver {
    fn default() -> Self {
        Self::new()
    }
}
