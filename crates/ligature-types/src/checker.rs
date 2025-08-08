//! Type checker for the Ligature language.

use crate::constraints::ConstraintSolver;
use crate::environment::TypeEnvironment;
use crate::error::TypeError;
use crate::resolver::ModuleResolver;
use ligature_ast::ty::Constraint;
use ligature_ast::{
    AstError, AstResult, BinaryOperator, Declaration, Expr, ExprKind, Import, Literal, MatchCase,
    Module, Pattern, Program, RecordField, Span, Type, TypeAlias, TypeConstructor, TypeKind,
    TypeVariant, UnaryOperator, ValueDeclaration,
};

/// Type checker for Ligature programs.
pub struct TypeChecker {
    environment: TypeEnvironment,
    constraint_solver: ConstraintSolver,
    resolver: ModuleResolver,
    /// Track the current import stack to detect cycles
    import_stack: Vec<String>,
}

impl TypeChecker {
    /// Create a new type checker.
    pub fn new() -> Self {
        let mut checker = Self {
            environment: TypeEnvironment::new(),
            constraint_solver: ConstraintSolver::new(),
            resolver: ModuleResolver::new(),
            import_stack: Vec::new(),
        };

        // Add basic built-in functions
        checker.add_builtins();

        checker
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeChecker {
    /// Add basic built-in functions to the environment.
    fn add_builtins(&mut self) {
        // Add if as a built-in function (Bool -> a -> a -> a)
        let if_type = Type::function(
            Type::bool(Span::default()),
            Type::function(
                Type::variable("a".to_string(), Span::default()),
                Type::function(
                    Type::variable("a".to_string(), Span::default()),
                    Type::variable("a".to_string(), Span::default()),
                    Span::default(),
                ),
                Span::default(),
            ),
            Span::default(),
        );
        self.environment.bind("if".to_string(), if_type);

        // Add then as a built-in function (a -> a)
        let then_type = Type::function(
            Type::variable("a".to_string(), Span::default()),
            Type::variable("a".to_string(), Span::default()),
            Span::default(),
        );
        self.environment.bind("then".to_string(), then_type);

        // Add else as a built-in function (a -> a)
        let else_type = Type::function(
            Type::variable("a".to_string(), Span::default()),
            Type::variable("a".to_string(), Span::default()),
            Span::default(),
        );
        self.environment.bind("else".to_string(), else_type);

        // Add basic Option type constructors
        let option_type = Type::union(
            vec![
                TypeVariant {
                    name: "Some".to_string(),
                    type_: Some(Type::variable("T".to_string(), Span::default())),
                    span: Span::default(),
                },
                TypeVariant {
                    name: "None".to_string(),
                    type_: None,
                    span: Span::default(),
                },
            ],
            Span::default(),
        );

        // Add Option type
        self.environment
            .bind("Option".to_string(), option_type.clone());

        // Add Some constructor (T -> Option T)
        let some_type = Type::function(
            Type::variable("T".to_string(), Span::default()),
            option_type.clone(),
            Span::default(),
        );
        self.environment.bind("Some".to_string(), some_type);

        // Add None constructor (Option T)
        self.environment.bind("None".to_string(), option_type);
    }

    /// Create a new type checker with search paths.
    pub fn with_paths(
        search_paths: Vec<std::path::PathBuf>,
        register_paths: Vec<std::path::PathBuf>,
    ) -> Self {
        let mut resolver = ModuleResolver::new();
        for path in search_paths {
            resolver.add_search_path(path);
        }
        for path in register_paths {
            resolver.add_register_path(path);
        }

        let mut checker = Self {
            environment: TypeEnvironment::new(),
            constraint_solver: ConstraintSolver::new(),
            resolver,
            import_stack: Vec::new(),
        };

        // Add basic built-in functions
        checker.add_builtins();

        checker
    }

    /// Type check a complete program.
    pub fn check_program(&mut self, program: &Program) -> AstResult<()> {
        for declaration in &program.declarations {
            self.check_declaration(declaration)?;
        }
        Ok(())
    }

    /// Type check a complete module.
    pub fn check_module(&mut self, module: &Module) -> AstResult<()> {
        // Check imports first
        for import in &module.imports {
            self.check_import(import)?;
        }

        // Then check declarations
        for declaration in &module.declarations {
            self.check_declaration(declaration)?;
        }

        Ok(())
    }

    /// Type check a single declaration.
    pub fn check_declaration(&mut self, declaration: &Declaration) -> AstResult<()> {
        match &declaration.kind {
            ligature_ast::DeclarationKind::Value(value_decl) => {
                self.check_value_declaration(value_decl)
            }
            ligature_ast::DeclarationKind::TypeAlias(type_alias) => {
                self.check_type_alias(type_alias)
            }
            ligature_ast::DeclarationKind::TypeConstructor(type_constructor) => {
                self.check_type_constructor(type_constructor)
            }
            ligature_ast::DeclarationKind::Import(import) => self.check_import(import),
            ligature_ast::DeclarationKind::Export(_) => {
                // Exports don't need type checking
                Ok(())
            }
            ligature_ast::DeclarationKind::TypeClass(type_class) => {
                self.check_type_class(type_class)
            }
            ligature_ast::DeclarationKind::Instance(instance) => self.check_instance(instance),
        }
    }

    /// Type check a value declaration.
    pub fn check_value_declaration(&mut self, value_decl: &ValueDeclaration) -> AstResult<()> {
        // Infer the type of the value expression
        let inferred_type = self.infer_expression(&value_decl.value)?;

        // If there's a type annotation, check that it matches the inferred type
        if let Some(annotation) = &value_decl.type_annotation {
            if !self.types_equal(&inferred_type, annotation)? {
                return Err(AstError::InvalidTypeAnnotation {
                    span: value_decl.span,
                });
            }
        }

        // Add the binding to the environment
        let final_type = value_decl
            .type_annotation
            .as_ref()
            .unwrap_or(&inferred_type);

        // Check for binding conflicts
        match self
            .environment
            .bind_with_conflict_check(value_decl.name.clone(), final_type.clone())
        {
            Ok(()) => {}
            Err((name, existing_type, new_type)) => {
                return Err(TypeError::binding_conflict(
                    name,
                    format!("{existing_type:?}"),
                    format!("{new_type:?}"),
                    value_decl.span,
                )
                .into());
            }
        }

        Ok(())
    }

    /// Type check a type alias declaration.
    pub fn check_type_alias(&mut self, type_alias: &TypeAlias) -> AstResult<()> {
        // Check that the type alias is well-formed
        self.check_type(&type_alias.type_)?;

        // Add the type alias to the environment
        self.environment
            .bind_type_alias(type_alias.name.clone(), type_alias.clone());

        // If the aliased type is a union, create constructors for the variants
        if let TypeKind::Union { variants } = &type_alias.type_.kind {
            for variant in variants {
                // Create a constructor for this variant
                let constructor = TypeConstructor {
                    name: variant.name.clone(),
                    parameters: vec![], // No type parameters for now
                    body: type_alias.type_.clone(),
                    span: variant.span,
                };

                // Bind the constructor to the environment
                self.environment
                    .bind_type_constructor(variant.name.clone(), constructor);
            }
        }

        Ok(())
    }

    /// Type check a type constructor declaration.
    pub fn check_type_constructor(&mut self, type_constructor: &TypeConstructor) -> AstResult<()> {
        // Check that the type constructor body is well-formed
        self.check_type(&type_constructor.body)?;

        // Add the type constructor to the environment
        self.environment
            .bind_type_constructor(type_constructor.name.clone(), type_constructor.clone());

        Ok(())
    }

    /// Type check an import declaration.
    pub fn check_import(&mut self, import: &Import) -> AstResult<()> {
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

        // Add the current import to the stack
        self.import_stack.push(import.path.clone());

        // Resolve and load the imported module
        let imported_module = self.resolver.resolve_module(&import.path)?;

        // Type check the imported module
        self.check_module(&imported_module)?;

        // Add imported bindings to the environment
        self.add_imported_bindings(import, &imported_module)?;

        // Remove the current import from the stack
        self.import_stack.pop();

        Ok(())
    }

    /// Detect import cycles.
    fn detect_import_cycle(&self, import: &Import) -> bool {
        // Check if the current import path is already in the import stack
        self.import_stack.contains(&import.path)
    }

    /// Resolve a module path to a file path.
    pub fn resolve_module_path(&self, path: &str) -> AstResult<String> {
        // This is now handled by the resolver
        if path.ends_with(".lig") {
            Ok(path.to_string())
        } else {
            Ok(format!("{path}.lig"))
        }
    }

    /// Load a module from a file path.
    #[allow(dead_code)]
    fn load_module(&self, path: &str) -> AstResult<ligature_ast::Module> {
        // This is now handled by the resolver
        Ok(ligature_ast::Module {
            name: path.to_string(),
            imports: Vec::new(),
            declarations: Vec::new(),
            span: ligature_ast::Span::default(),
        })
    }

    /// Add a register path for module resolution.
    pub fn add_register_path(&mut self, path: std::path::PathBuf) {
        self.resolver.add_register_path(path);
    }

    /// Get the register paths.
    pub fn register_paths(&self) -> &[std::path::PathBuf] {
        &self.resolver.register_paths
    }

    /// Get access to the module cache.
    pub fn module_cache(&self) -> &std::collections::HashMap<String, ligature_ast::Module> {
        &self.resolver.cache
    }

    /// Get access to the module resolver.
    pub fn resolver(&mut self) -> &mut ModuleResolver {
        &mut self.resolver
    }

    /// Bind a variable to a type in the environment.
    pub fn bind(&mut self, name: String, type_: Type) {
        self.environment.bind(name, type_);
    }

    /// Resolve and check an import statement.
    pub fn resolve_and_check_import(&mut self, import: &Import) -> AstResult<()> {
        // First check the import
        self.check_import(import)?;

        // Resolve the module
        let module = self.resolver.resolve_module(&import.path)?;

        // Add imported bindings to the environment
        self.add_imported_bindings(import, &module)?;

        Ok(())
    }

    /// Add imported bindings to the environment.
    fn add_imported_bindings(
        &mut self,
        import: &Import,
        module: &ligature_ast::Module,
    ) -> AstResult<()> {
        // Get exported bindings from the module
        let exported_bindings = self.resolver.get_exported_bindings(module);

        match import.alias.as_ref() {
            Some(alias) => {
                // Import with alias - create a module type
                let module_type = Type::module(alias.clone(), import.span);
                self.environment.bind(alias.clone(), module_type);

                // Handle selective imports
                if let Some(ref items) = import.items {
                    // Import only specified items with alias prefix
                    for item in items {
                        if let Some(binding_type) = exported_bindings.get(&item.name) {
                            let import_name = item.alias.as_ref().unwrap_or(&item.name);
                            let prefixed_name = format!("{alias}.{import_name}");
                            self.environment.bind(prefixed_name, binding_type.clone());
                        }
                    }
                } else {
                    // Import all exported bindings with alias prefix
                    for (name, binding_type) in exported_bindings {
                        let prefixed_name = format!("{alias}.{name}");
                        self.environment.bind(prefixed_name, binding_type);
                    }
                }
            }
            None => {
                // Import without alias
                if let Some(ref items) = import.items {
                    // Import only specified items
                    for item in items {
                        if let Some(binding_type) = exported_bindings.get(&item.name) {
                            let import_name = item.alias.as_ref().unwrap_or(&item.name);

                            // Check for conflicts with existing bindings
                            match self
                                .environment
                                .bind_with_conflict_check(import_name.clone(), binding_type.clone())
                            {
                                Ok(()) => {}
                                Err((name, existing_type, new_type)) => {
                                    return Err(TypeError::import_binding_conflict(
                                        name,
                                        format!("{existing_type:?}"),
                                        format!("{new_type:?}"),
                                        import.span,
                                    )
                                    .into());
                                }
                            }
                        }
                    }
                } else {
                    // Import all exported bindings directly
                    for (name, binding_type) in exported_bindings {
                        // Check for conflicts with existing bindings
                        match self
                            .environment
                            .bind_with_conflict_check(name.clone(), binding_type.clone())
                        {
                            Ok(()) => {}
                            Err((conflict_name, existing_type, new_type)) => {
                                return Err(TypeError::import_binding_conflict(
                                    conflict_name,
                                    format!("{existing_type:?}"),
                                    format!("{new_type:?}"),
                                    import.span,
                                )
                                .into());
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Type check a type class declaration.
    pub fn check_type_class(
        &mut self,
        type_class: &ligature_ast::TypeClassDeclaration,
    ) -> AstResult<()> {
        // Check that all method signatures are well-formed
        for method in &type_class.methods {
            self.check_type(&method.type_)?;
        }

        // Add the type class to the environment
        self.environment
            .bind_type_class(type_class.name.clone(), type_class.clone());

        Ok(())
    }

    /// Type check an instance declaration.
    pub fn check_instance(
        &mut self,
        instance: &ligature_ast::InstanceDeclaration,
    ) -> AstResult<()> {
        // Check for instance conflicts
        if let Err(conflicting_instances) = self
            .environment
            .check_instance_conflicts(&instance.class_name, &instance.type_arguments)
        {
            let conflicting_names: Vec<String> = conflicting_instances
                .iter()
                .map(|inst| format!("{inst:?}"))
                .collect();

            return Err(TypeError::type_class_instance_conflict(
                instance.class_name.clone(),
                format!("{instance:?}"),
                conflicting_names,
                instance.span,
            )
            .into());
        }

        // Check for instance overlaps
        let overlaps = self
            .environment
            .check_instance_overlaps(&instance.class_name);
        if let Some((type1, type2)) = overlaps.into_iter().next() {
            return Err(TypeError::type_class_overlap(
                instance.class_name.clone(),
                type1,
                type2,
                instance.span,
            )
            .into());
        }

        // Look up the type class to get method signatures
        let type_class_methods = match self.environment.lookup_type_class(&instance.class_name) {
            Some(tc) => tc.methods.clone(),
            None => {
                return Err(TypeError::type_class_constraint_unsatisfied_with_instances(
                    format!("{instance:?}"),
                    instance.class_name.clone(),
                    "No instances available".to_string(),
                    instance.span,
                )
                .into());
            }
        };

        // Check that all method implementations have the correct types
        for method in &instance.methods {
            let inferred_type = self.infer_expression(&method.implementation)?;

            // Find the expected type for this method
            if let Some(expected_method) = type_class_methods.iter().find(|m| m.name == method.name)
            {
                if !self.types_equal(&inferred_type, &expected_method.type_)? {
                    return Err(TypeError::type_class_method_mismatch(
                        method.name.clone(),
                        format!("{expected_method:?}"),
                        format!("{inferred_type:?}"),
                        method.span,
                    )
                    .into());
                }
            } else {
                return Err(TypeError::type_class_method_mismatch(
                    method.name.clone(),
                    "method not found in type class".to_string(),
                    format!("{inferred_type:?}"),
                    method.span,
                )
                .into());
            }
        }

        // Add the instance to the environment
        self.environment
            .bind_instance(instance.class_name.clone(), instance.clone());

        Ok(())
    }

    /// Type check an expression.
    pub fn check_expression(&mut self, expr: &Expr, expected_type: &Type) -> AstResult<()> {
        let inferred_type = self.infer_expression(expr)?;

        if !self.types_equal(&inferred_type, expected_type)? {
            return Err(AstError::InvalidTypeAnnotation { span: expr.span });
        }

        Ok(())
    }

    /// Infer the type of an expression.
    pub fn infer_expression(&mut self, expr: &Expr) -> AstResult<Type> {
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
    pub fn infer_literal(&mut self, literal: &Literal) -> AstResult<Type> {
        let kind = match literal {
            Literal::String(_) => TypeKind::String,
            Literal::Integer(_) => TypeKind::Integer,
            Literal::Float(_) => TypeKind::Float,
            Literal::Boolean(_) => TypeKind::Bool,
            Literal::Unit => TypeKind::Unit,
            Literal::List(elements) => {
                if elements.is_empty() {
                    // Empty list has type [a] where a is a type variable
                    TypeKind::List(Box::new(Type::variable("a".to_string(), Span::default())))
                } else {
                    // Check that all elements have the same type
                    let first_type = self.infer_expression(&elements[0])?;
                    for element in &elements[1..] {
                        let element_type = self.infer_expression(element)?;
                        if !self.types_equal(&first_type, &element_type)? {
                            return Err(AstError::InvalidTypeAnnotation { span: element.span });
                        }
                    }
                    TypeKind::List(Box::new(first_type))
                }
            }
        };

        Ok(Type::new(kind, Span::default()))
    }

    /// Instantiate a polymorphic type with fresh type variables.
    pub fn instantiate(&self, type_: &Type) -> Type {
        // For now, just return the type as-is
        // In a full implementation, this would replace universal quantifiers with fresh type variables
        type_.clone()
    }

    /// Infer the type of a variable.
    pub fn infer_variable(&self, name: &str) -> AstResult<Type> {
        // First check if it's a regular variable
        if let Some(type_) = self.environment.lookup(name) {
            return Ok(self.instantiate(&type_));
        }

        // If not found as a variable, check if it's a type constructor
        if let Some(constructor) = self.environment.lookup_type_constructor(name) {
            // For union constructors, we need to return a function type
            if let TypeKind::Union { variants } = &constructor.body.kind {
                // Find the variant with this name
                for variant in variants {
                    if variant.name == name {
                        // Return a function type that takes the payload type and returns the union type
                        let parameter_type = variant
                            .type_
                            .clone()
                            .unwrap_or_else(|| Type::unit(Span::default()));

                        return Ok(Type::function(
                            parameter_type,
                            constructor.body.clone(),
                            Span::default(),
                        ));
                    }
                }
            }

            // For non-union constructors, return the constructor body
            return Ok(constructor.body.clone());
        }

        // If not found as a type constructor, return an error
        Err(AstError::UndefinedIdentifier {
            name: name.to_string(),
            span: Span::default(),
        })
    }

    /// Infer the type of a function application.
    pub fn infer_application(&mut self, function: &Expr, argument: &Expr) -> AstResult<Type> {
        let function_type = self.infer_expression(function)?;
        let argument_type = self.infer_expression(argument)?;

        match &function_type.kind {
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                if self.types_equal(parameter, &argument_type)? {
                    Ok(*return_type.clone())
                } else {
                    // Enhanced error handling for type variables
                    match (&parameter.kind, &argument_type.kind) {
                        (TypeKind::Variable(_), _) | (_, TypeKind::Variable(_)) => {
                            // If either type is a variable, be more lenient
                            // This is a simplified approach - in a full implementation,
                            // you'd want proper type unification
                            Ok(*return_type.clone())
                        }
                        _ => Err(AstError::InvalidTypeAnnotation {
                            span: function.span,
                        }),
                    }
                }
            }
            TypeKind::Variable(_) => {
                // If function type is a variable, be more lenient
                // This handles cases where the function type hasn't been fully inferred yet
                Ok(Type::variable("result".to_string(), function.span))
            }
            _ => Err(AstError::InvalidTypeAnnotation {
                span: function.span,
            }),
        }
    }

    /// Infer the type of a lambda abstraction.
    pub fn infer_abstraction(
        &mut self,
        parameter: &str,
        parameter_type: Option<&Type>,
        body: &Expr,
    ) -> AstResult<Type> {
        let param_type = if let Some(ty) = parameter_type {
            ty.clone()
        } else {
            // Infer parameter type from body
            Type::variable("a".to_string(), Span::default())
        };

        // Create a new environment with the parameter bound
        let mut new_env = TypeEnvironment::with_parent(self.environment.clone());
        new_env.bind(parameter.to_string(), param_type.clone());

        // Create a new type checker with the new environment
        let mut new_checker = TypeChecker {
            environment: new_env,
            constraint_solver: self.constraint_solver.clone(),
            resolver: self.resolver.clone(),
            import_stack: self.import_stack.clone(),
        };

        let body_type = new_checker.infer_expression(body)?;
        Ok(Type::function(param_type, body_type, Span::default()))
    }

    /// Infer the type of a let expression.
    pub fn infer_let(&mut self, name: &str, value: &Expr, body: &Expr) -> AstResult<Type> {
        let value_type = self.infer_expression(value)?;

        // Create a new environment with the binding
        let mut new_env = TypeEnvironment::with_parent(self.environment.clone());
        new_env.bind(name.to_string(), value_type);

        // Create a new type checker with the new environment
        let mut new_checker = TypeChecker {
            environment: new_env,
            constraint_solver: self.constraint_solver.clone(),
            resolver: self.resolver.clone(),
            import_stack: self.import_stack.clone(),
        };

        new_checker.infer_expression(body)
    }

    /// Infer the type of a record expression.
    pub fn infer_record(&mut self, fields: &[RecordField]) -> AstResult<Type> {
        let mut type_fields = Vec::new();

        for field in fields {
            let field_type = self.infer_expression(&field.value)?;
            type_fields.push(ligature_ast::TypeField {
                name: field.name.clone(),
                type_: field_type,
                span: field.span,
            });
        }

        Ok(Type::record(type_fields, Span::default()))
    }

    /// Infer the type of a field access expression.
    pub fn infer_field_access(&mut self, record: &Expr, field: &str) -> AstResult<Type> {
        let record_type = self.infer_expression(record)?;

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
    pub fn infer_union(&mut self, variant: &str, value: Option<&Expr>) -> AstResult<Type> {
        // Create a union type with the given variant
        let variant_type = if let Some(value_expr) = value {
            // If there's a value, infer its type
            let value_type = self.infer_expression(value_expr)?;
            Some(value_type)
        } else {
            // If no value, the variant has no associated type
            None
        };

        // Create a union type with this single variant
        let union_type = Type::union(
            vec![TypeVariant {
                name: variant.to_string(),
                type_: variant_type,
                span: Span::default(),
            }],
            Span::default(),
        );

        Ok(union_type)
    }

    /// Extract the type that should be bound to a pattern variable.
    #[allow(clippy::only_used_in_recursion, clippy::type_complexity)]
    fn extract_pattern_type(
        &self,
        pattern: &ligature_ast::Pattern,
        scrutinee_type: &Type,
    ) -> AstResult<Option<(String, Type)>> {
        match pattern {
            ligature_ast::Pattern::Variable(name) => {
                // For variable patterns, bind the scrutinee type
                Ok(Some((name.clone(), scrutinee_type.clone())))
            }
            ligature_ast::Pattern::Union { variant, value } => {
                // For union patterns, extract the payload type
                match &scrutinee_type.kind {
                    TypeKind::Union { variants } => {
                        for v in variants {
                            if v.name == *variant {
                                if let Some(payload_pattern) = value {
                                    // Extract the type from the payload pattern
                                    let payload_type = match &v.type_ {
                                        Some(t) => t,
                                        None => {
                                            let unit_type = Type::unit(Span::default());
                                            // Store the unit type in a way that outlives the borrow
                                            // For now, we'll use a simple approach
                                            return self
                                                .extract_pattern_type(payload_pattern, &unit_type);
                                        }
                                    };

                                    // Special case: if the payload pattern is a union pattern with no value,
                                    // it might actually be a variable pattern that was incorrectly parsed
                                    if let Pattern::Union {
                                        variant,
                                        value: None,
                                    } = &**payload_pattern
                                    {
                                        // This is likely a variable pattern that was parsed as a union pattern
                                        return Ok(Some((variant.clone(), payload_type.clone())));
                                    }

                                    return self
                                        .extract_pattern_type(payload_pattern, payload_type);
                                }
                                return Ok(None);
                            }
                        }
                        Ok(None)
                    }
                    TypeKind::Variable(_) => {
                        // If scrutinee type is a type variable, we need to handle this specially
                        // This happens when type inference hasn't fully resolved the type yet
                        if let Some(payload_pattern) = value {
                            // Special case: if the payload pattern is a union pattern with no value,
                            // it might actually be a variable pattern that was incorrectly parsed
                            if let Pattern::Union {
                                variant,
                                value: None,
                            } = &**payload_pattern
                            {
                                // This is likely a variable pattern that was parsed as a union pattern
                                // For now, we'll bind it to a generic type variable
                                let generic_type =
                                    Type::variable(format!("{variant}_type"), Span::default());
                                return Ok(Some((variant.clone(), generic_type)));
                            }
                        }
                        Ok(None)
                    }
                    _ => Ok(None),
                }
            }
            ligature_ast::Pattern::Wildcard => {
                // For wildcard patterns, no variable binding needed
                Ok(None)
            }
            ligature_ast::Pattern::Literal(_) => {
                // For literal patterns, no variable binding needed
                Ok(None)
            }
            ligature_ast::Pattern::Record { .. } => {
                // For record patterns, no variable binding needed (for now)
                Ok(None)
            }
            ligature_ast::Pattern::List { .. } => {
                // For list patterns, no variable binding needed (for now)
                Ok(None)
            }
        }
    }

    /// Infer the type of a match expression.
    pub fn infer_match(&mut self, scrutinee: &Expr, cases: &[MatchCase]) -> AstResult<Type> {
        let scrutinee_type = self.infer_expression(scrutinee)?;

        if cases.is_empty() {
            return Err(AstError::InvalidTypeAnnotation {
                span: scrutinee.span,
            });
        }

        // Process each case with pattern variable binding
        let mut case_types = Vec::new();

        for case in cases {
            // Create a new environment for this case to handle pattern bindings
            let case_env = TypeEnvironment::with_parent(self.environment.clone());
            let mut case_checker = TypeChecker {
                environment: case_env,
                constraint_solver: self.constraint_solver.clone(),
                resolver: self.resolver.clone(),
                import_stack: self.import_stack.clone(),
            };

            // Extract pattern variables and bind them in the case environment
            if let Some((var_name, var_type)) =
                self.extract_pattern_type(&case.pattern, &scrutinee_type)?
            {
                case_checker.environment.bind(var_name, var_type);
            }

            // Check guard condition if present
            if let Some(guard) = &case.guard {
                println!("Debug: Checking guard expression: {guard:?}");
                let guard_type = case_checker.infer_expression(guard)?;
                println!("Debug: Guard type: {guard_type:?}");
                if !self.types_equal(&guard_type, &Type::bool(Span::default()))? {
                    return Err(AstError::InvalidTypeAnnotation { span: guard.span });
                }
            }

            // Infer the case expression type
            println!("Debug: Checking case expression: {:?}", case.expression);
            let case_type = case_checker.infer_expression(&case.expression)?;
            println!("Debug: Case type: {case_type:?}");
            case_types.push(case_type);
        }

        // Check that all cases have the same type
        let first_case_type = &case_types[0];
        for case_type in &case_types[1..] {
            if !self.types_equal(first_case_type, case_type)? {
                return Err(AstError::InvalidTypeAnnotation {
                    span: cases[0].span,
                });
            }
        }

        Ok(first_case_type.clone())
    }

    /// Infer the type of an if expression.
    pub fn infer_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> AstResult<Type> {
        let condition_type = self.infer_expression(condition)?;

        // Check that condition is boolean
        if !self.types_equal(&condition_type, &Type::bool(Span::default()))? {
            return Err(AstError::InvalidTypeAnnotation {
                span: condition.span,
            });
        }

        let then_type = self.infer_expression(then_branch)?;
        let else_type = self.infer_expression(else_branch)?;

        // Check that both branches have the same type
        if !self.types_equal(&then_type, &else_type)? {
            return Err(AstError::InvalidTypeAnnotation {
                span: then_branch.span,
            });
        }

        Ok(then_type)
    }

    /// Infer the type of a binary operation.
    pub fn infer_binary_op(
        &mut self,
        operator: &BinaryOperator,
        left: &Expr,
        right: &Expr,
    ) -> AstResult<Type> {
        let left_type = self.infer_expression(left)?;
        let right_type = self.infer_expression(right)?;

        match operator {
            BinaryOperator::Add
            | BinaryOperator::Subtract
            | BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Modulo => {
                // Arithmetic operators require numeric types
                if self.types_equal(&left_type, &right_type)? {
                    if self.types_equal(&left_type, &Type::integer(Span::default()))?
                        || self.types_equal(&left_type, &Type::float(Span::default()))?
                    {
                        Ok(left_type)
                    } else {
                        Err(AstError::InvalidTypeAnnotation { span: left.span })
                    }
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: left.span })
                }
            }
            BinaryOperator::Equal
            | BinaryOperator::NotEqual
            | BinaryOperator::LessThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThan
            | BinaryOperator::GreaterThanOrEqual => {
                // Comparison operators require comparable types and return boolean
                if self.types_equal(&left_type, &right_type)? {
                    Ok(Type::bool(Span::default()))
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: left.span })
                }
            }
            BinaryOperator::And | BinaryOperator::Or => {
                // Logical operators require boolean types
                if self.types_equal(&left_type, &Type::bool(Span::default()))?
                    && self.types_equal(&right_type, &Type::bool(Span::default()))?
                {
                    Ok(Type::bool(Span::default()))
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: left.span })
                }
            }
            BinaryOperator::Concat => {
                // String concatenation
                if self.types_equal(&left_type, &Type::string(Span::default()))?
                    && self.types_equal(&right_type, &Type::string(Span::default()))?
                {
                    Ok(Type::string(Span::default()))
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: left.span })
                }
            }
        }
    }

    /// Infer the type of a unary operation.
    pub fn infer_unary_op(&mut self, operator: &UnaryOperator, operand: &Expr) -> AstResult<Type> {
        let operand_type = self.infer_expression(operand)?;

        match operator {
            UnaryOperator::Not => {
                if self.types_equal(&operand_type, &Type::bool(Span::default()))? {
                    Ok(Type::bool(Span::default()))
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: operand.span })
                }
            }
            UnaryOperator::Negate => {
                if self.types_equal(&operand_type, &Type::integer(Span::default()))?
                    || self.types_equal(&operand_type, &Type::float(Span::default()))?
                {
                    Ok(operand_type)
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: operand.span })
                }
            }
        }
    }

    /// Infer the type of an annotated expression.
    pub fn infer_annotated(
        &mut self,
        expression: &Expr,
        type_annotation: &Type,
    ) -> AstResult<Type> {
        let inferred_type = self.infer_expression(expression)?;

        if self.types_equal(&inferred_type, type_annotation)? {
            Ok(type_annotation.clone())
        } else {
            Err(AstError::InvalidTypeAnnotation {
                span: expression.span,
            })
        }
    }

    /// Check that a type is well-formed.
    pub fn check_type(&mut self, type_: &Type) -> AstResult<()> {
        match &type_.kind {
            TypeKind::Unit
            | TypeKind::Bool
            | TypeKind::String
            | TypeKind::Integer
            | TypeKind::Float => Ok(()),
            TypeKind::Variable(_) => Ok(()),
            TypeKind::Function {
                parameter,
                return_type,
            } => {
                self.check_type(parameter)?;
                self.check_type(return_type)
            }
            TypeKind::Record { fields } => {
                for field in fields {
                    self.check_type(&field.type_)?;
                }
                Ok(())
            }
            TypeKind::Union { variants } => {
                for variant in variants {
                    if let Some(type_) = &variant.type_ {
                        self.check_type(type_)?;
                    }
                }
                Ok(())
            }
            TypeKind::List(element_type) => self.check_type(element_type),
            TypeKind::ForAll { body, .. } => self.check_type(body),
            TypeKind::Exists { body, .. } => self.check_type(body),
            TypeKind::Pi {
                parameter_type,
                return_type,
                ..
            } => {
                self.check_type(parameter_type)?;
                self.check_type(return_type)
            }
            TypeKind::Sigma {
                parameter_type,
                return_type,
                ..
            } => {
                self.check_type(parameter_type)?;
                self.check_type(return_type)
            }
            TypeKind::Application { function, argument } => {
                self.check_type(function)?;
                self.check_type(argument)
            }
            TypeKind::Module { .. } => {
                // Module types are always well-formed
                Ok(())
            }
            TypeKind::Constrained { constraint, type_ } => {
                // Check that the constraint is valid
                // Validate that the type class exists and the type arguments match
                if let Some(type_class) = self.environment.lookup_type_class(&constraint.class_name)
                {
                    // Check that the number of type arguments matches the number of type parameters
                    if constraint.type_arguments.len() != type_class.parameters.len() {
                        return Err(AstError::InvalidTypeAnnotation { span: type_.span });
                    }

                    // For now, just check that the constrained type is well-formed
                    // In a full implementation, we would also check that the type arguments
                    // satisfy the type class constraints
                    self.check_type(type_)
                } else {
                    Err(AstError::InvalidTypeAnnotation { span: type_.span })
                }
            }
            TypeKind::Refinement {
                base_type,
                predicate,
                ..
            } => {
                // Check that the base type is well-formed
                self.check_type(base_type)?;

                // Check that the predicate is well-formed
                // For now, we'll just check that it's a valid expression
                // In a full implementation, we would also check that it returns a boolean
                let _predicate_type = self.infer_expression(predicate)?;

                Ok(())
            }
            TypeKind::ConstraintType {
                base_type,
                constraints,
            } => {
                // Check that the base type is well-formed
                self.check_type(base_type)?;

                // Check that all constraints are well-formed
                for constraint in constraints {
                    match constraint {
                        Constraint::ValueConstraint(expr) => {
                            let _expr_type = self.infer_expression(expr)?;
                        }
                        Constraint::RangeConstraint { min, max, .. } => {
                            if let Some(min_expr) = min {
                                let _min_type = self.infer_expression(min_expr)?;
                            }
                            if let Some(max_expr) = max {
                                let _max_type = self.infer_expression(max_expr)?;
                            }
                        }
                        Constraint::CustomConstraint { arguments, .. } => {
                            for arg in arguments {
                                let _arg_type = self.infer_expression(arg)?;
                            }
                        }
                        Constraint::CrossFieldConstraint { predicate, .. } => {
                            let _predicate_type = self.infer_expression(predicate)?;
                        }
                        Constraint::PatternConstraint { .. } => {
                            // Pattern constraints don't need expression checking
                        }
                    }
                }

                Ok(())
            }
        }
    }

    /// Check if two types are equal.
    pub fn types_equal(&self, type1: &Type, type2: &Type) -> AstResult<bool> {
        self.types_equal_internal(type1, type2, &mut std::collections::HashMap::new(), 0)
    }

    /// Internal type equality checking with substitution tracking and depth limiting.
    #[allow(clippy::only_used_in_recursion)]
    fn types_equal_internal(
        &self,
        type1: &Type,
        type2: &Type,
        substitution: &mut std::collections::HashMap<String, Type>,
        depth: usize,
    ) -> AstResult<bool> {
        const MAX_DEPTH: usize = 50; // Prevent infinite recursion

        if depth > MAX_DEPTH {
            return Ok(false); // Return false to prevent stack overflow
        }
        match (&type1.kind, &type2.kind) {
            // Base types
            (TypeKind::Unit, TypeKind::Unit)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::String, TypeKind::String)
            | (TypeKind::Integer, TypeKind::Integer)
            | (TypeKind::Float, TypeKind::Float) => Ok(true),

            // Type variables
            (TypeKind::Variable(var1), TypeKind::Variable(var2)) => {
                if var1 == var2 {
                    Ok(true)
                } else {
                    // Check if both variables are bound to the same type
                    let t1_opt = substitution.get(var1).cloned();
                    let t2_opt = substitution.get(var2).cloned();
                    match (t1_opt, t2_opt) {
                        (Some(t1), Some(t2)) => {
                            self.types_equal_internal(&t1, &t2, substitution, depth + 1)
                        }
                        (Some(t1), None) => {
                            substitution.insert(var2.clone(), t1);
                            Ok(true)
                        }
                        (None, Some(t2)) => {
                            substitution.insert(var1.clone(), t2);
                            Ok(true)
                        }
                        (None, None) => {
                            // Both are unbound, bind them to each other
                            substitution.insert(var1.clone(), type2.clone());
                            substitution.insert(var2.clone(), type1.clone());
                            Ok(true)
                        }
                    }
                }
            }

            // One type variable, one concrete type
            (TypeKind::Variable(var), _) => {
                if let Some(bound_type) = substitution.get(var).cloned() {
                    self.types_equal_internal(&bound_type, type2, substitution, depth + 1)
                } else {
                    substitution.insert(var.clone(), type2.clone());
                    Ok(true)
                }
            }
            (_, TypeKind::Variable(var)) => {
                if let Some(bound_type) = substitution.get(var).cloned() {
                    self.types_equal_internal(type1, &bound_type, substitution, depth + 1)
                } else {
                    substitution.insert(var.clone(), type1.clone());
                    Ok(true)
                }
            }

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
                let param_equal = self.types_equal_internal(p1, p2, substitution, depth + 1)?;
                let return_equal = self.types_equal_internal(r1, r2, substitution, depth + 1)?;
                Ok(param_equal && return_equal)
            }

            // Record types
            (TypeKind::Record { fields: f1 }, TypeKind::Record { fields: f2 }) => {
                if f1.len() != f2.len() {
                    return Ok(false);
                }

                for (field1, field2) in f1.iter().zip(f2.iter()) {
                    if field1.name != field2.name {
                        return Ok(false);
                    }
                    if !self.types_equal_internal(
                        &field1.type_,
                        &field2.type_,
                        substitution,
                        depth + 1,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }

            // Union types
            (TypeKind::Union { variants: v1 }, TypeKind::Union { variants: v2 }) => {
                if v1.len() != v2.len() {
                    return Ok(false);
                }

                for (variant1, variant2) in v1.iter().zip(v2.iter()) {
                    if variant1.name != variant2.name {
                        return Ok(false);
                    }
                    match (&variant1.type_, &variant2.type_) {
                        (Some(t1), Some(t2)) => {
                            if !self.types_equal_internal(t1, t2, substitution, depth + 1)? {
                                return Ok(false);
                            }
                        }
                        (None, None) => {}
                        _ => {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }

            // List types
            (TypeKind::List(e1), TypeKind::List(e2)) => {
                self.types_equal_internal(e1, e2, substitution, depth + 1)
            }

            // Module types
            (TypeKind::Module { name: n1 }, TypeKind::Module { name: n2 }) => Ok(n1 == n2),

            // Constrained types
            (
                TypeKind::Constrained {
                    constraint: c1,
                    type_: t1,
                },
                TypeKind::Constrained {
                    constraint: c2,
                    type_: t2,
                },
            ) => {
                // Compare constraints properly
                if c1.class_name != c2.class_name {
                    return Ok(false);
                }

                // Check that type arguments match
                if c1.type_arguments.len() != c2.type_arguments.len() {
                    return Ok(false);
                }

                for (arg1, arg2) in c1.type_arguments.iter().zip(c2.type_arguments.iter()) {
                    if !self.types_equal_internal(arg1, arg2, substitution, depth + 1)? {
                        return Ok(false);
                    }
                }

                // Compare the constrained types
                self.types_equal_internal(t1, t2, substitution, depth + 1)
            }

            // Refinement types
            (
                TypeKind::Refinement {
                    base_type: b1,
                    predicate: _p1,
                    predicate_name: n1,
                },
                TypeKind::Refinement {
                    base_type: b2,
                    predicate: _p2,
                    predicate_name: n2,
                },
            ) => {
                // Compare base types
                let base_equal = self.types_equal_internal(b1, b2, substitution, depth + 1)?;

                // For now, we'll consider refinement types equal if their base types are equal
                // and their predicate names match (if both have names)
                // In a full implementation, we would also compare the predicates structurally
                let name_equal = match (n1, n2) {
                    (Some(name1), Some(name2)) => name1 == name2,
                    (None, None) => true,
                    _ => false,
                };

                Ok(base_equal && name_equal)
            }

            // Constraint types
            (
                TypeKind::ConstraintType {
                    base_type: b1,
                    constraints: c1,
                },
                TypeKind::ConstraintType {
                    base_type: b2,
                    constraints: c2,
                },
            ) => {
                // Compare base types
                let base_equal = self.types_equal_internal(b1, b2, substitution, depth + 1)?;

                // For now, we'll consider constraint types equal if their base types are equal
                // and they have the same number of constraints
                // In a full implementation, we would also compare the constraints structurally
                let constraints_equal = c1.len() == c2.len();

                Ok(base_equal && constraints_equal)
            }

            // Different types
            _ => Ok(false),
        }
    }
}
