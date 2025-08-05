//! Type environment for managing type bindings and scopes.

use indexmap::IndexMap;
use ligature_ast::{InstanceDeclaration, Type, TypeAlias, TypeClassDeclaration, TypeConstructor};

/// Type alias for conflict error
type ConflictError = (String, Type, Type);

/// Strategy for resolving binding conflicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictResolutionStrategy {
    /// Report binding conflicts as errors.
    Error,
    /// Warn about binding conflicts but continue.
    Warn,
    /// Override existing bindings with new ones.
    Override,
    /// Skip conflicting bindings.
    Skip,
}

/// A type environment that manages type bindings and scopes.
pub struct TypeEnvironment {
    /// Current scope bindings.
    bindings: IndexMap<String, Type>,
    /// Type aliases.
    type_aliases: IndexMap<String, TypeAlias>,
    /// Type constructors.
    type_constructors: IndexMap<String, TypeConstructor>,
    /// Type classes.
    type_classes: IndexMap<String, TypeClassDeclaration>,
    /// Type class instances.
    instances: IndexMap<String, Vec<InstanceDeclaration>>,
    /// Parent environment (for nested scopes).
    parent: Option<Box<TypeEnvironment>>,
    /// Warning messages collected during type checking.
    warnings: Vec<String>,
}

impl TypeEnvironment {
    /// Create a new type environment.
    pub fn new() -> Self {
        Self {
            bindings: IndexMap::new(),
            type_aliases: IndexMap::new(),
            type_constructors: IndexMap::new(),
            type_classes: IndexMap::new(),
            instances: IndexMap::new(),
            parent: None,
            warnings: Vec::new(),
        }
    }

    /// Create a new environment with a parent.
    pub fn with_parent(parent: TypeEnvironment) -> Self {
        Self {
            bindings: IndexMap::new(),
            type_aliases: IndexMap::new(),
            type_constructors: IndexMap::new(),
            type_classes: IndexMap::new(),
            instances: IndexMap::new(),
            parent: Some(Box::new(parent)),
            warnings: Vec::new(),
        }
    }

    /// Bind a name to a type in the current scope.
    pub fn bind(&mut self, name: String, type_: Type) {
        self.bindings.insert(name, type_);
    }

    /// Bind a name to a type in the current scope, checking for conflicts.
    pub fn bind_with_conflict_check(
        &mut self,
        name: String,
        type_: Type,
    ) -> Result<(), ConflictError> {
        if let Some(existing_type) = self.bindings.get(&name) {
            Err((name, existing_type.clone(), type_))
        } else {
            self.bindings.insert(name, type_);
            Ok(())
        }
    }

    /// Bind a name to a type in the current scope, with conflict resolution strategy.
    pub fn bind_with_strategy(
        &mut self,
        name: String,
        type_: Type,
        strategy: ConflictResolutionStrategy,
    ) -> Result<(), ConflictError> {
        match strategy {
            ConflictResolutionStrategy::Error => self.bind_with_conflict_check(name, type_),
            ConflictResolutionStrategy::Warn => {
                if let Some(existing_type) = self.bindings.get(&name) {
                    // Add warning mechanism
                    self.emit_warning(&format!(
                        "Binding conflict for '{name}': existing={existing_type:?}, new={type_:?}",
                    ));
                }
                self.bindings.insert(name, type_);
                Ok(())
            }
            ConflictResolutionStrategy::Override => {
                self.bindings.insert(name, type_);
                Ok(())
            }
            ConflictResolutionStrategy::Skip => {
                if self.bindings.contains_key(&name) {
                    Ok(())
                } else {
                    self.bindings.insert(name, type_);
                    Ok(())
                }
            }
        }
    }

    /// Look up a name in the environment.
    pub fn lookup(&self, name: &str) -> Option<Type> {
        if let Some(type_) = self.bindings.get(name) {
            Some(type_.clone())
        } else if let Some(parent) = &self.parent {
            parent.lookup(name)
        } else {
            None
        }
    }

    /// Check if a name is bound in the current scope.
    pub fn is_bound(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    /// Emit a warning message.
    pub fn emit_warning(&mut self, message: &str) {
        self.warnings.push(message.to_string());
        // Also print to stderr for immediate feedback
        eprintln!("Warning: {message}");
    }

    /// Get all collected warnings.
    pub fn get_warnings(&self) -> &[String] {
        &self.warnings
    }

    /// Clear all warnings.
    pub fn clear_warnings(&mut self) {
        self.warnings.clear();
    }

    /// Check if there are any warnings.
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Bind a type alias.
    pub fn bind_type_alias(&mut self, name: String, alias: TypeAlias) {
        self.type_aliases.insert(name, alias);
    }

    /// Look up a type alias.
    pub fn lookup_type_alias(&self, name: &str) -> Option<&TypeAlias> {
        if let Some(alias) = self.type_aliases.get(name) {
            Some(alias)
        } else if let Some(parent) = &self.parent {
            parent.lookup_type_alias(name)
        } else {
            None
        }
    }

    /// Bind a type constructor.
    pub fn bind_type_constructor(&mut self, name: String, constructor: TypeConstructor) {
        self.type_constructors.insert(name, constructor);
    }

    /// Look up a type constructor.
    pub fn lookup_type_constructor(&self, name: &str) -> Option<&TypeConstructor> {
        if let Some(constructor) = self.type_constructors.get(name) {
            Some(constructor)
        } else if let Some(parent) = &self.parent {
            parent.lookup_type_constructor(name)
        } else {
            None
        }
    }

    /// Bind a type class.
    pub fn bind_type_class(&mut self, name: String, class: TypeClassDeclaration) {
        self.type_classes.insert(name, class);
    }

    /// Look up a type class.
    pub fn lookup_type_class(&self, name: &str) -> Option<&TypeClassDeclaration> {
        if let Some(class) = self.type_classes.get(name) {
            Some(class)
        } else if let Some(parent) = &self.parent {
            parent.lookup_type_class(name)
        } else {
            None
        }
    }

    /// Bind a type class instance.
    pub fn bind_instance(&mut self, class_name: String, instance: InstanceDeclaration) {
        self.instances.entry(class_name).or_default().push(instance);
    }

    /// Look up type class instances for a given class.
    pub fn lookup_instances(&self, class_name: &str) -> Option<&[InstanceDeclaration]> {
        self.lookup_instances_with_depth(class_name, 0)
    }

    /// Look up type class instances with depth tracking to prevent infinite recursion.
    fn lookup_instances_with_depth(
        &self,
        class_name: &str,
        depth: usize,
    ) -> Option<&[InstanceDeclaration]> {
        const MAX_DEPTH: usize = 100; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return None; // Return None to prevent stack overflow
        }

        if let Some(instances) = self.instances.get(class_name) {
            Some(instances.as_slice())
        } else if let Some(parent) = &self.parent {
            parent.lookup_instances_with_depth(class_name, depth + 1)
        } else {
            None
        }
    }

    /// Find a matching instance for a type class and type arguments.
    pub fn find_matching_instance(
        &self,
        class_name: &str,
        type_arguments: &[Type],
    ) -> Option<&InstanceDeclaration> {
        let result = self.find_matching_instance_with_depth(class_name, type_arguments, 0);

        // Debug logging (can be enabled/disabled as needed)
        if result.is_none() {
            // Log available instances for debugging
            if let Some(_instances) = self.lookup_instances(class_name) {
                // This could be expanded to provide more detailed debugging information
            }
        }

        result
    }

    /// Find a matching instance with depth tracking to prevent infinite recursion.
    fn find_matching_instance_with_depth(
        &self,
        class_name: &str,
        type_arguments: &[Type],
        depth: usize,
    ) -> Option<&InstanceDeclaration> {
        const MAX_DEPTH: usize = 100; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return None; // Return None to prevent stack overflow
        }

        if let Some(instances) = self.lookup_instances(class_name) {
            // Find all matching instances
            let mut matching_instances = Vec::new();
            for instance in instances {
                if self.instance_matches(instance, type_arguments) {
                    matching_instances.push(instance);
                }
            }

            // If we found exactly one match, return it
            if matching_instances.len() == 1 {
                return Some(matching_instances[0]);
            }

            // If we found multiple matches, try to select the most specific one
            if matching_instances.len() > 1 {
                return self.select_most_specific_instance(matching_instances, type_arguments);
            }
        }

        // Check parent environment with depth tracking
        if let Some(parent) = &self.parent {
            return parent.find_matching_instance_with_depth(class_name, type_arguments, depth + 1);
        }

        None
    }

    /// Select the most specific instance from a list of matching instances.
    fn select_most_specific_instance<'a>(
        &self,
        instances: Vec<&'a InstanceDeclaration>,
        type_arguments: &[Type],
    ) -> Option<&'a InstanceDeclaration> {
        if instances.is_empty() {
            return None;
        }

        if instances.len() == 1 {
            return Some(instances[0]);
        }

        // For now, we'll use a simple heuristic: prefer instances with fewer type variables
        // In a more sophisticated implementation, we'd use proper specificity ordering
        let mut best_instance = instances[0];
        let mut best_score = self.calculate_instance_specificity(best_instance, type_arguments);

        for instance in instances.iter().skip(1) {
            let score = self.calculate_instance_specificity(instance, type_arguments);
            if score > best_score {
                best_score = score;
                best_instance = instance;
            }
        }

        Some(best_instance)
    }

    /// Calculate a specificity score for an instance (higher is more specific).
    fn calculate_instance_specificity(
        &self,
        instance: &InstanceDeclaration,
        type_arguments: &[Type],
    ) -> usize {
        let mut score = 0;

        // Count non-variable type arguments (more specific)
        for (instance_arg, _provided_arg) in
            instance.type_arguments.iter().zip(type_arguments.iter())
        {
            match &instance_arg.kind {
                ligature_ast::TypeKind::Variable(_) => {
                    // Variables are less specific
                    score += 0;
                }
                _ => {
                    // Concrete types are more specific
                    score += 1;
                }
            }
        }

        score
    }

    /// Debug method to get information about why instance matching failed.
    pub fn debug_instance_matching(&self, class_name: &str, type_arguments: &[Type]) -> String {
        let mut debug_info = format!("Debug info for class '{class_name}' with type arguments:\n");

        for (i, arg) in type_arguments.iter().enumerate() {
            debug_info.push_str(&format!("  Arg {i}: {arg:?}\n"));
        }

        if let Some(instances) = self.lookup_instances(class_name) {
            debug_info.push_str(&format!("Found {} instances:\n", instances.len()));

            for (i, instance) in instances.iter().enumerate() {
                debug_info.push_str(&format!("  Instance {i}:\n"));
                debug_info.push_str(&format!("    Type arguments: {instance:?}\n"));

                let matches = self.instance_matches(instance, type_arguments);
                debug_info.push_str(&format!("    Matches: {matches}\n"));

                if !matches {
                    // Try to identify why it doesn't match
                    if instance.type_arguments.len() != type_arguments.len() {
                        debug_info.push_str(&format!(
                            "    Reason: Argument count mismatch (expected {}, got {})\n",
                            instance.type_arguments.len(),
                            type_arguments.len()
                        ));
                    } else {
                        for (j, (instance_arg, provided_arg)) in instance
                            .type_arguments
                            .iter()
                            .zip(type_arguments.iter())
                            .enumerate()
                        {
                            if !self.types_compatible(instance_arg, provided_arg) {
                                debug_info.push_str(&format!("    Reason: Argument {j} incompatible: {instance_arg:?} vs {provided_arg:?}\n"));
                            }
                        }
                    }
                }
            }
        } else {
            debug_info.push_str("No instances found for this class.\n");
        }

        debug_info
    }

    /// Find all matching instances for a type class and type arguments.
    pub fn find_all_matching_instances(
        &self,
        class_name: &str,
        type_arguments: &[Type],
    ) -> Vec<&InstanceDeclaration> {
        self.find_all_matching_instances_with_depth(class_name, type_arguments, 0)
    }

    /// Find all matching instances with depth tracking to prevent infinite recursion.
    fn find_all_matching_instances_with_depth(
        &self,
        class_name: &str,
        type_arguments: &[Type],
        depth: usize,
    ) -> Vec<&InstanceDeclaration> {
        const MAX_DEPTH: usize = 100; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return Vec::new(); // Return empty result to prevent stack overflow
        }

        let mut matches = Vec::new();

        if let Some(instances) = self.lookup_instances(class_name) {
            for instance in instances {
                if self.instance_matches(instance, type_arguments) {
                    matches.push(instance);
                }
            }
        }

        // Check parent environment with depth tracking
        if let Some(parent) = &self.parent {
            matches.extend(parent.find_all_matching_instances_with_depth(
                class_name,
                type_arguments,
                depth + 1,
            ));
        }

        matches
    }

    /// Check for type class instance conflicts.
    pub fn check_instance_conflicts(
        &self,
        class_name: &str,
        type_arguments: &[Type],
    ) -> Result<(), Vec<&InstanceDeclaration>> {
        let matches = self.find_all_matching_instances(class_name, type_arguments);
        if matches.len() > 1 {
            Err(matches)
        } else {
            Ok(())
        }
    }

    /// Check for type class instance overlaps.
    pub fn check_instance_overlaps(&self, class_name: &str) -> Vec<(String, String)> {
        self.check_instance_overlaps_with_depth(class_name, 0)
    }

    /// Check for type class instance overlaps with depth tracking to prevent infinite recursion.
    fn check_instance_overlaps_with_depth(
        &self,
        class_name: &str,
        depth: usize,
    ) -> Vec<(String, String)> {
        const MAX_DEPTH: usize = 100; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return Vec::new(); // Return empty result to prevent stack overflow
        }

        let mut overlaps = Vec::new();

        if let Some(instances) = self.lookup_instances(class_name) {
            for i in 0..instances.len() {
                for j in (i + 1)..instances.len() {
                    if self.instances_overlap(&instances[i], &instances[j]) {
                        let type1 = format!("{:?}", instances[i].type_arguments);
                        let type2 = format!("{:?}", instances[j].type_arguments);
                        overlaps.push((type1, type2));
                    }
                }
            }
        }

        // Check parent environment with depth tracking
        if let Some(parent) = &self.parent {
            overlaps.extend(parent.check_instance_overlaps_with_depth(class_name, depth + 1));
        }

        overlaps
    }

    /// Check if two instances overlap (can match the same type).
    fn instances_overlap(
        &self,
        instance1: &InstanceDeclaration,
        instance2: &InstanceDeclaration,
    ) -> bool {
        // This is a simplified overlap check
        // In a full implementation, this would use proper type unification
        if instance1.type_arguments.len() != instance2.type_arguments.len() {
            return false;
        }

        // Check if the instances could potentially match the same type
        for (arg1, arg2) in instance1
            .type_arguments
            .iter()
            .zip(instance2.type_arguments.iter())
        {
            if !self.types_could_unify(arg1, arg2) {
                return false;
            }
        }

        true
    }

    /// Check if two types could potentially unify.
    fn types_could_unify(&self, type1: &Type, type2: &Type) -> bool {
        matches!(
            (&type1.kind, &type2.kind),
            (ligature_ast::TypeKind::Variable(_), _)
                | (_, ligature_ast::TypeKind::Variable(_))
                | (
                    ligature_ast::TypeKind::Integer,
                    ligature_ast::TypeKind::Integer
                )
                | (
                    ligature_ast::TypeKind::String,
                    ligature_ast::TypeKind::String
                )
                | (ligature_ast::TypeKind::Bool, ligature_ast::TypeKind::Bool)
                | (ligature_ast::TypeKind::Unit, ligature_ast::TypeKind::Unit)
        )
    }

    /// Check if an instance matches the given type arguments.
    fn instance_matches(&self, instance: &InstanceDeclaration, type_arguments: &[Type]) -> bool {
        if instance.type_arguments.len() != type_arguments.len() {
            return false;
        }

        // Create a substitution map for type variables
        let mut substitution = std::collections::HashMap::new();

        // Try to match instance arguments with provided arguments
        for (instance_arg, provided_arg) in
            instance.type_arguments.iter().zip(type_arguments.iter())
        {
            if !self.types_match_with_substitution(instance_arg, provided_arg, &mut substitution) {
                return false;
            }
        }

        true
    }

    /// Check if two types match with a substitution map for type variables.
    fn types_match_with_substitution(
        &self,
        pattern: &Type,
        target: &Type,
        substitution: &mut std::collections::HashMap<String, Type>,
    ) -> bool {
        self.types_match_with_substitution_depth(pattern, target, substitution, 0)
    }

    /// Check if two types match with a substitution map for type variables and depth tracking.
    fn types_match_with_substitution_depth(
        &self,
        pattern: &Type,
        target: &Type,
        substitution: &mut std::collections::HashMap<String, Type>,
        depth: usize,
    ) -> bool {
        const MAX_DEPTH: usize = 50; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return false; // Return false to prevent stack overflow
        }

        match (&pattern.kind, &target.kind) {
            // Type variables - handle substitution
            (ligature_ast::TypeKind::Variable(var_name), _) => {
                if let Some(substituted_type) = substitution.get(var_name) {
                    // Variable already bound - check consistency
                    self.types_compatible_with_depth(substituted_type, target, depth + 1)
                } else {
                    // New variable binding
                    substitution.insert(var_name.clone(), target.clone());
                    true
                }
            }

            // If target is a variable but pattern is not, we can't match
            (_, ligature_ast::TypeKind::Variable(_)) => {
                // This is a conservative approach - we could be more permissive
                // but for now, we require the pattern to be more specific
                false
            }

            // For all other cases, use the regular compatibility check
            _ => self.types_compatible_with_depth(pattern, target, depth + 1),
        }
    }

    /// Check if two types are compatible.
    fn types_compatible(&self, type1: &Type, type2: &Type) -> bool {
        self.types_compatible_with_depth(type1, type2, 0)
    }

    /// Check if two types are compatible with depth tracking to prevent infinite recursion.
    #[allow(clippy::only_used_in_recursion)]
    fn types_compatible_with_depth(&self, type1: &Type, type2: &Type, depth: usize) -> bool {
        const MAX_DEPTH: usize = 50; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return false; // Return false to prevent stack overflow
        }

        match (&type1.kind, &type2.kind) {
            // Type variables
            (ligature_ast::TypeKind::Variable(var1), ligature_ast::TypeKind::Variable(var2)) => {
                var1 == var2
            }

            // Primitive types
            (ligature_ast::TypeKind::Integer, ligature_ast::TypeKind::Integer) => true,
            (ligature_ast::TypeKind::String, ligature_ast::TypeKind::String) => true,
            (ligature_ast::TypeKind::Bool, ligature_ast::TypeKind::Bool) => true,
            (ligature_ast::TypeKind::Unit, ligature_ast::TypeKind::Unit) => true,
            (ligature_ast::TypeKind::Float, ligature_ast::TypeKind::Float) => true,

            // Function types
            (
                ligature_ast::TypeKind::Function {
                    parameter: param1,
                    return_type: ret1,
                },
                ligature_ast::TypeKind::Function {
                    parameter: param2,
                    return_type: ret2,
                },
            ) => {
                self.types_compatible_with_depth(param1, param2, depth + 1)
                    && self.types_compatible_with_depth(ret1, ret2, depth + 1)
            }

            // Record types
            (
                ligature_ast::TypeKind::Record { fields: fields1 },
                ligature_ast::TypeKind::Record { fields: fields2 },
            ) => {
                if fields1.len() != fields2.len() {
                    return false;
                }
                for (field1, field2) in fields1.iter().zip(fields2.iter()) {
                    if field1.name != field2.name
                        || !self.types_compatible_with_depth(
                            &field1.type_,
                            &field2.type_,
                            depth + 1,
                        )
                    {
                        return false;
                    }
                }
                true
            }

            // Union types
            (
                ligature_ast::TypeKind::Union {
                    variants: variants1,
                },
                ligature_ast::TypeKind::Union {
                    variants: variants2,
                },
            ) => {
                if variants1.len() != variants2.len() {
                    return false;
                }
                for (variant1, variant2) in variants1.iter().zip(variants2.iter()) {
                    if variant1.name != variant2.name {
                        return false;
                    }
                    match (&variant1.type_, &variant2.type_) {
                        (Some(type1), Some(type2)) => {
                            if !self.types_compatible_with_depth(type1, type2, depth + 1) {
                                return false;
                            }
                        }
                        (None, None) => {}
                        _ => return false,
                    }
                }
                true
            }

            // List types
            (ligature_ast::TypeKind::List(element1), ligature_ast::TypeKind::List(element2)) => {
                self.types_compatible_with_depth(element1, element2, depth + 1)
            }

            // Universal quantification
            (
                ligature_ast::TypeKind::ForAll {
                    parameter: param1,
                    body: body1,
                },
                ligature_ast::TypeKind::ForAll {
                    parameter: param2,
                    body: body2,
                },
            ) => param1 == param2 && self.types_compatible_with_depth(body1, body2, depth + 1),

            // Existential quantification
            (
                ligature_ast::TypeKind::Exists {
                    parameter: param1,
                    body: body1,
                },
                ligature_ast::TypeKind::Exists {
                    parameter: param2,
                    body: body2,
                },
            ) => param1 == param2 && self.types_compatible_with_depth(body1, body2, depth + 1),

            // Dependent function types (Pi types)
            (
                ligature_ast::TypeKind::Pi {
                    parameter: param1,
                    parameter_type: param_type1,
                    return_type: ret1,
                },
                ligature_ast::TypeKind::Pi {
                    parameter: param2,
                    parameter_type: param_type2,
                    return_type: ret2,
                },
            ) => {
                param1 == param2
                    && self.types_compatible_with_depth(param_type1, param_type2, depth + 1)
                    && self.types_compatible_with_depth(ret1, ret2, depth + 1)
            }

            // Dependent pair types (Sigma types)
            (
                ligature_ast::TypeKind::Sigma {
                    parameter: param1,
                    parameter_type: param_type1,
                    return_type: ret1,
                },
                ligature_ast::TypeKind::Sigma {
                    parameter: param2,
                    parameter_type: param_type2,
                    return_type: ret2,
                },
            ) => {
                param1 == param2
                    && self.types_compatible_with_depth(param_type1, param_type2, depth + 1)
                    && self.types_compatible_with_depth(ret1, ret2, depth + 1)
            }

            // Type application
            (
                ligature_ast::TypeKind::Application {
                    function: func1,
                    argument: arg1,
                },
                ligature_ast::TypeKind::Application {
                    function: func2,
                    argument: arg2,
                },
            ) => {
                self.types_compatible_with_depth(func1, func2, depth + 1)
                    && self.types_compatible_with_depth(arg1, arg2, depth + 1)
            }

            // Module types
            (
                ligature_ast::TypeKind::Module { name: name1 },
                ligature_ast::TypeKind::Module { name: name2 },
            ) => name1 == name2,

            // Constrained types
            (
                ligature_ast::TypeKind::Constrained {
                    constraint: constraint1,
                    type_: type1,
                },
                ligature_ast::TypeKind::Constrained {
                    constraint: constraint2,
                    type_: type2,
                },
            ) => {
                // For constrained types, we need to check both the constraint and the underlying type
                // This is a simplified check - in a full implementation, we'd need to handle
                // type class constraint compatibility more carefully
                self.types_compatible_with_depth(type1, type2, depth + 1)
                    && constraint1.class_name == constraint2.class_name
                    && constraint1.type_arguments.len() == constraint2.type_arguments.len()
                    && constraint1
                        .type_arguments
                        .iter()
                        .zip(constraint2.type_arguments.iter())
                        .all(|(arg1, arg2)| self.types_compatible_with_depth(arg1, arg2, depth + 1))
            }

            // Type variables are compatible with any type (for now)
            // In a more sophisticated implementation, this would involve unification
            (ligature_ast::TypeKind::Variable(_), _) | (_, ligature_ast::TypeKind::Variable(_)) => {
                true
            }

            // Default case - types are not compatible
            _ => false,
        }
    }

    /// Execute a function with a temporary binding.
    pub fn with_binding<F, R>(&mut self, name: String, type_: Type, f: F) -> R
    where
        F: FnOnce(&mut TypeEnvironment) -> R,
    {
        // Save the current binding if it exists
        let old_binding = self.bindings.swap_remove(&name);

        // Add the new binding
        self.bindings.insert(name.clone(), type_);

        // Execute the function
        let result = f(self);

        // Restore the old binding
        self.bindings.swap_remove(&name);
        if let Some(old_type) = old_binding {
            self.bindings.insert(name, old_type);
        }

        result
    }

    /// Execute a function with a temporary environment.
    pub fn with_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut TypeEnvironment) -> R,
    {
        // Create a new environment without cloning the parent
        let mut new_env = TypeEnvironment::new();

        // Temporarily store the current bindings
        let current_bindings = std::mem::take(&mut self.bindings);
        let current_type_aliases = std::mem::take(&mut self.type_aliases);
        let current_type_constructors = std::mem::take(&mut self.type_constructors);
        let current_type_classes = std::mem::take(&mut self.type_classes);
        let current_instances = std::mem::take(&mut self.instances);

        // Execute the function with the new environment
        let result = f(&mut new_env);

        // Restore the original bindings
        self.bindings = current_bindings;
        self.type_aliases = current_type_aliases;
        self.type_constructors = current_type_constructors;
        self.type_classes = current_type_classes;
        self.instances = current_instances;

        // Merge any new bindings from the temporary environment
        for (name, type_) in new_env.bindings {
            self.bindings.insert(name, type_);
        }
        for (name, alias) in new_env.type_aliases {
            self.type_aliases.insert(name, alias);
        }
        for (name, constructor) in new_env.type_constructors {
            self.type_constructors.insert(name, constructor);
        }
        for (name, class) in new_env.type_classes {
            self.type_classes.insert(name, class);
        }
        for (name, instances) in new_env.instances {
            self.instances.insert(name, instances);
        }

        result
    }

    /// Get all bindings in the current scope.
    pub fn current_bindings(&self) -> &IndexMap<String, Type> {
        &self.bindings
    }

    /// Get all type aliases in the current scope.
    pub fn current_type_aliases(&self) -> &IndexMap<String, TypeAlias> {
        &self.type_aliases
    }

    /// Get all type constructors in the current scope.
    pub fn current_type_constructors(&self) -> &IndexMap<String, TypeConstructor> {
        &self.type_constructors
    }

    /// Get all type classes in the current scope.
    pub fn current_type_classes(&self) -> &IndexMap<String, TypeClassDeclaration> {
        &self.type_classes
    }

    /// Get all type class instances in the current scope.
    pub fn current_instances(&self) -> &IndexMap<String, Vec<InstanceDeclaration>> {
        &self.instances
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
            && self.type_aliases.is_empty()
            && self.type_constructors.is_empty()
            && self.type_classes.is_empty()
            && self.instances.is_empty()
            && self.parent.is_none()
    }

    /// Get the depth of the environment (number of parent scopes).
    pub fn depth(&self) -> usize {
        if let Some(parent) = &self.parent {
            1 + parent.depth()
        } else {
            0
        }
    }

    /// Iterate over all bindings in this environment and its parents.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Type)> {
        let mut current = Some(self);

        std::iter::from_fn(move || {
            if let Some(env) = current {
                if let Some((name, type_)) = env.bindings.iter().next() {
                    return Some((name, type_));
                }
                current = env.parent.as_ref().map(|p| p.as_ref());
                None
            } else {
                None
            }
        })
    }

    /// Check if a type is a union type.
    pub fn is_union_type(&self, type_: &Type) -> bool {
        matches!(&type_.kind, ligature_ast::TypeKind::Union { .. })
    }

    /// Find all union types in the environment that contain a specific variant.
    pub fn find_unions_with_variant(&self, variant_name: &str) -> Vec<Type> {
        let mut unions = Vec::new();

        for (_, type_) in self.iter() {
            if let Some(union_variants) = type_.as_union() {
                if union_variants.iter().any(|v| v.name == variant_name) {
                    unions.push(type_.clone());
                }
            }
        }

        unions
    }
}

impl Clone for TypeEnvironment {
    fn clone(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
            type_aliases: self.type_aliases.clone(),
            type_constructors: self.type_constructors.clone(),
            type_classes: self.type_classes.clone(),
            instances: self.instances.clone(),
            parent: self.parent.clone(),
            warnings: self.warnings.clone(),
        }
    }
}

impl Default for TypeEnvironment {
    fn default() -> Self {
        Self::new()
    }
}
