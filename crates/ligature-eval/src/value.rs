//! Value representation for the Ligature evaluation engine.

use std::collections::HashMap;
use std::sync::Arc;

use ligature_ast::{Expr, Literal, Span};

use crate::environment::EvaluationEnvironment;

/// A value in the Ligature language.
#[derive(Debug, Clone, PartialEq)]
pub struct Value {
    /// The kind of value.
    pub kind: ValueKind,
    /// Source location information.
    pub span: Span,
}

impl Value {
    /// Create a new value with the given kind and span.
    pub fn new(kind: ValueKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Create a unit value.
    pub fn unit(span: Span) -> Self {
        Self::new(ValueKind::Unit, span)
    }

    /// Create a boolean value with interning.
    pub fn boolean(value: bool, span: Span) -> Self {
        Self::new(ValueKind::Boolean(Arc::new(value)), span)
    }

    /// Create a string value with interning.
    pub fn string(value: String, span: Span) -> Self {
        Self::new(ValueKind::String(Arc::new(value)), span)
    }

    /// Create an integer value with interning.
    pub fn integer(value: i64, span: Span) -> Self {
        Self::new(ValueKind::Integer(Arc::new(value)), span)
    }

    /// Create a float value with interning.
    pub fn float(value: f64, span: Span) -> Self {
        Self::new(ValueKind::Float(Arc::new(value)), span)
    }

    /// Create a record value with shared field storage.
    pub fn record(fields: HashMap<String, Value>, span: Span) -> Self {
        Self::new(ValueKind::Record(Arc::new(fields)), span)
    }

    /// Create a list value with shared element storage.
    pub fn list(elements: Vec<Value>, span: Span) -> Self {
        Self::new(ValueKind::List(Arc::new(elements)), span)
    }

    /// Create a function value.
    pub fn function(parameter: String, body: Expr, span: Span) -> Self {
        Self::new(
            ValueKind::Function {
                parameter: Arc::new(parameter),
                body: Arc::new(body),
            },
            span,
        )
    }

    /// Create a closure value with shared environment.
    pub fn closure(
        parameter: String,
        body: Expr,
        environment: EvaluationEnvironment,
        span: Span,
    ) -> Self {
        Self::new(
            ValueKind::Closure {
                parameter: Arc::new(parameter),
                body: Arc::new(body),
                environment: Arc::new(environment),
            },
            span,
        )
    }

    /// Create a union value with shared payload.
    pub fn union(variant: String, value: Option<Value>, span: Span) -> Self {
        Self::new(
            ValueKind::Union {
                variant: Arc::new(variant),
                value: value.map(Arc::new),
            },
            span,
        )
    }

    /// Create a module value with shared environment.
    pub fn module(name: String, environment: EvaluationEnvironment, span: Span) -> Self {
        Self::new(
            ValueKind::Module {
                name: Arc::new(name),
                environment: Arc::new(environment),
            },
            span,
        )
    }

    /// Create a boolean value using the interner.
    pub fn boolean_interned(value: bool, span: Span, interner: &mut ValueInterner) -> Self {
        Self::new(ValueKind::Boolean(interner.get_boolean(value)), span)
    }

    /// Create a string value using the interner.
    pub fn string_interned(value: String, span: Span, interner: &mut ValueInterner) -> Self {
        Self::new(ValueKind::String(interner.intern_string(value)), span)
    }

    /// Create an integer value using the interner.
    pub fn integer_interned(value: i64, span: Span, interner: &mut ValueInterner) -> Self {
        Self::new(ValueKind::Integer(interner.intern_integer(value)), span)
    }

    /// Create a float value using the interner.
    pub fn float_interned(value: f64, span: Span, interner: &mut ValueInterner) -> Self {
        Self::new(ValueKind::Float(interner.intern_float(value)), span)
    }

    /// Create a list value using the interner.
    pub fn list_interned(elements: Vec<Value>, span: Span, interner: &mut ValueInterner) -> Self {
        Self::new(ValueKind::List(interner.intern_list(elements)), span)
    }

    /// Create a record value using the interner for field names.
    pub fn record_interned(
        fields: HashMap<String, Value>,
        span: Span,
        interner: &mut ValueInterner,
    ) -> Self {
        // Intern field names for better memory efficiency
        let interned_fields = fields
            .into_iter()
            .map(|(name, value)| (interner.intern_string(name).to_string(), value))
            .collect();
        Self::new(ValueKind::Record(Arc::new(interned_fields)), span)
    }

    /// Check if this value is a unit value.
    pub fn is_unit(&self) -> bool {
        matches!(self.kind, ValueKind::Unit)
    }

    /// Check if this value is a boolean value.
    pub fn is_boolean(&self) -> bool {
        matches!(self.kind, ValueKind::Boolean(_))
    }

    /// Check if this value is a string value.
    pub fn is_string(&self) -> bool {
        matches!(self.kind, ValueKind::String(_))
    }

    /// Check if this value is an integer value.
    pub fn is_integer(&self) -> bool {
        matches!(self.kind, ValueKind::Integer(_))
    }

    /// Check if this value is a float value.
    pub fn is_float(&self) -> bool {
        matches!(self.kind, ValueKind::Float(_))
    }

    /// Check if this value is a record value.
    pub fn is_record(&self) -> bool {
        matches!(self.kind, ValueKind::Record(_))
    }

    /// Check if this value is a list value.
    pub fn is_list(&self) -> bool {
        matches!(self.kind, ValueKind::List(_))
    }

    /// Check if this value is a function value.
    pub fn is_function(&self) -> bool {
        matches!(self.kind, ValueKind::Function { .. })
    }

    /// Check if this value is a closure value.
    pub fn is_closure(&self) -> bool {
        matches!(self.kind, ValueKind::Closure { .. })
    }

    /// Check if this value is a union value.
    pub fn is_union(&self) -> bool {
        matches!(self.kind, ValueKind::Union { .. })
    }

    /// Check if this value is a module value.
    pub fn is_module(&self) -> bool {
        matches!(self.kind, ValueKind::Module { .. })
    }

    /// Convert to boolean if possible.
    pub fn as_boolean(&self) -> Option<bool> {
        match &self.kind {
            ValueKind::Boolean(value) => Some(**value),
            _ => None,
        }
    }

    /// Convert to string if possible.
    pub fn as_string(&self) -> Option<&str> {
        match &self.kind {
            ValueKind::String(value) => Some(value),
            _ => None,
        }
    }

    /// Convert to integer if possible.
    pub fn as_integer(&self) -> Option<i64> {
        match &self.kind {
            ValueKind::Integer(value) => Some(**value),
            ValueKind::Float(value) => Some(**value as i64),
            _ => None,
        }
    }

    /// Convert to float if possible.
    pub fn as_float(&self) -> Option<f64> {
        match &self.kind {
            ValueKind::Integer(value) => Some(**value as f64),
            ValueKind::Float(value) => Some(**value),
            _ => None,
        }
    }

    /// Get the record fields if this is a record.
    pub fn as_record(&self) -> Option<&HashMap<String, Value>> {
        match &self.kind {
            ValueKind::Record(fields) => Some(fields),
            _ => None,
        }
    }

    /// Get the list elements if this is a list.
    pub fn as_list(&self) -> Option<&[Value]> {
        match &self.kind {
            ValueKind::List(elements) => Some(elements),
            _ => None,
        }
    }

    /// Get the function parameter and body if this is a function.
    pub fn as_function(&self) -> Option<(&str, &Expr)> {
        match &self.kind {
            ValueKind::Function { parameter, body } => Some((parameter, body)),
            _ => None,
        }
    }

    /// Get the closure components if this is a closure value.
    #[allow(clippy::type_complexity)]
    pub fn as_closure(&self) -> Option<(&str, &Expr, &EvaluationEnvironment)> {
        match &self.kind {
            ValueKind::Closure {
                parameter,
                body,
                environment,
            } => Some((parameter, body, environment)),
            _ => None,
        }
    }

    /// Get the union components if this is a union value.
    #[allow(clippy::type_complexity)]
    pub fn as_union(&self) -> Option<(&str, Option<&Value>)> {
        match &self.kind {
            ValueKind::Union { variant, value } => {
                Some((variant, value.as_ref().map(|v| v.as_ref())))
            }
            _ => None,
        }
    }

    /// Get the module components if this is a module value.
    pub fn as_module(&self) -> Option<(&str, &EvaluationEnvironment)> {
        match &self.kind {
            ValueKind::Module { name, environment } => Some((name, environment)),
            _ => None,
        }
    }

    /// Apply a binary operator to this value and another value.
    pub fn apply_binary_op(
        &self,
        operator: &ligature_ast::BinaryOperator,
        other: &Value,
    ) -> Result<Value, String> {
        match (operator, &self.kind, &other.kind) {
            // Arithmetic operators
            (ligature_ast::BinaryOperator::Add, ValueKind::Integer(a), ValueKind::Integer(b)) => {
                Ok(Value::integer(**a + **b, self.span))
            }
            (ligature_ast::BinaryOperator::Add, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::float(**a + **b, self.span))
            }
            (ligature_ast::BinaryOperator::Add, ValueKind::Integer(a), ValueKind::Float(b)) => {
                Ok(Value::float(**a as f64 + **b, self.span))
            }
            (ligature_ast::BinaryOperator::Add, ValueKind::Float(a), ValueKind::Integer(b)) => {
                Ok(Value::float(**a + **b as f64, self.span))
            }

            (
                ligature_ast::BinaryOperator::Subtract,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::integer(**a - **b, self.span)),
            (ligature_ast::BinaryOperator::Subtract, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::float(**a - **b, self.span))
            }
            (
                ligature_ast::BinaryOperator::Subtract,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::float(**a as f64 - **b, self.span)),
            (
                ligature_ast::BinaryOperator::Subtract,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::float(**a - **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::Multiply,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::integer(**a * **b, self.span)),
            (ligature_ast::BinaryOperator::Multiply, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::float(**a * **b, self.span))
            }
            (
                ligature_ast::BinaryOperator::Multiply,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::float(**a as f64 * **b, self.span)),
            (
                ligature_ast::BinaryOperator::Multiply,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::float(**a * **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::Divide,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => {
                if **b == 0 {
                    Err("Division by zero".to_string())
                } else {
                    Ok(Value::integer(**a / **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Divide, ValueKind::Float(a), ValueKind::Float(b)) => {
                if **b == 0.0 {
                    Err("Division by zero".to_string())
                } else {
                    Ok(Value::float(**a / **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Divide, ValueKind::Integer(a), ValueKind::Float(b)) => {
                if **b == 0.0 {
                    Err("Division by zero".to_string())
                } else {
                    Ok(Value::float(**a as f64 / **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Divide, ValueKind::Float(a), ValueKind::Integer(b)) => {
                if **b == 0 {
                    Err("Division by zero".to_string())
                } else {
                    Ok(Value::float(**a / **b as f64, self.span))
                }
            }

            (
                ligature_ast::BinaryOperator::Modulo,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => {
                if **b == 0 {
                    Err("Modulo by zero".to_string())
                } else {
                    Ok(Value::integer(**a % **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Modulo, ValueKind::Float(a), ValueKind::Float(b)) => {
                if **b == 0.0 {
                    Err("Modulo by zero".to_string())
                } else {
                    Ok(Value::float(**a % **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Modulo, ValueKind::Integer(a), ValueKind::Float(b)) => {
                if **b == 0.0 {
                    Err("Modulo by zero".to_string())
                } else {
                    Ok(Value::float(**a as f64 % **b, self.span))
                }
            }
            (ligature_ast::BinaryOperator::Modulo, ValueKind::Float(a), ValueKind::Integer(b)) => {
                if **b == 0 {
                    Err("Modulo by zero".to_string())
                } else {
                    Ok(Value::float(**a % **b as f64, self.span))
                }
            }

            // Comparison operators
            (ligature_ast::BinaryOperator::Equal, ValueKind::Integer(a), ValueKind::Integer(b)) => {
                Ok(Value::boolean(a == b, self.span))
            }
            (ligature_ast::BinaryOperator::Equal, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::boolean(a == b, self.span))
            }
            (ligature_ast::BinaryOperator::Equal, ValueKind::Boolean(a), ValueKind::Boolean(b)) => {
                Ok(Value::boolean(a == b, self.span))
            }
            (ligature_ast::BinaryOperator::Equal, ValueKind::String(a), ValueKind::String(b)) => {
                Ok(Value::boolean(a == b, self.span))
            }
            (ligature_ast::BinaryOperator::Equal, ValueKind::Integer(a), ValueKind::Float(b)) => {
                Ok(Value::boolean((**a as f64) == **b, self.span))
            }
            (ligature_ast::BinaryOperator::Equal, ValueKind::Float(a), ValueKind::Integer(b)) => {
                Ok(Value::boolean(**a == **b as f64, self.span))
            }

            (
                ligature_ast::BinaryOperator::NotEqual,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a != **b, self.span)),
            (ligature_ast::BinaryOperator::NotEqual, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::boolean(**a != **b, self.span))
            }
            (
                ligature_ast::BinaryOperator::NotEqual,
                ValueKind::Boolean(a),
                ValueKind::Boolean(b),
            ) => Ok(Value::boolean(**a != **b, self.span)),
            (
                ligature_ast::BinaryOperator::NotEqual,
                ValueKind::String(a),
                ValueKind::String(b),
            ) => Ok(Value::boolean(a != b, self.span)),
            (
                ligature_ast::BinaryOperator::NotEqual,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean((**a as f64) != **b, self.span)),
            (
                ligature_ast::BinaryOperator::NotEqual,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a != **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::LessThan,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a < **b, self.span)),
            (ligature_ast::BinaryOperator::LessThan, ValueKind::Float(a), ValueKind::Float(b)) => {
                Ok(Value::boolean(**a < **b, self.span))
            }
            (
                ligature_ast::BinaryOperator::LessThan,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean((**a as f64) < **b, self.span)),
            (
                ligature_ast::BinaryOperator::LessThan,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a < **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::LessThanOrEqual,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a <= **b, self.span)),
            (
                ligature_ast::BinaryOperator::LessThanOrEqual,
                ValueKind::Float(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean(**a <= **b, self.span)),
            (
                ligature_ast::BinaryOperator::LessThanOrEqual,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean((**a as f64) <= **b, self.span)),
            (
                ligature_ast::BinaryOperator::LessThanOrEqual,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a <= **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::GreaterThan,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a > **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThan,
                ValueKind::Float(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean(**a > **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThan,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean((**a as f64) > **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThan,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a > **b as f64, self.span)),

            (
                ligature_ast::BinaryOperator::GreaterThanOrEqual,
                ValueKind::Integer(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a >= **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThanOrEqual,
                ValueKind::Float(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean(**a >= **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThanOrEqual,
                ValueKind::Integer(a),
                ValueKind::Float(b),
            ) => Ok(Value::boolean((**a as f64) >= **b, self.span)),
            (
                ligature_ast::BinaryOperator::GreaterThanOrEqual,
                ValueKind::Float(a),
                ValueKind::Integer(b),
            ) => Ok(Value::boolean(**a >= **b as f64, self.span)),

            // Logical operators
            (ligature_ast::BinaryOperator::And, ValueKind::Boolean(a), ValueKind::Boolean(b)) => {
                Ok(Value::boolean(**a && **b, self.span))
            }
            (ligature_ast::BinaryOperator::Or, ValueKind::Boolean(a), ValueKind::Boolean(b)) => {
                Ok(Value::boolean(**a || **b, self.span))
            }

            // String concatenation
            (ligature_ast::BinaryOperator::Concat, ValueKind::String(a), ValueKind::String(b)) => {
                Ok(Value::string(format!("{a}{b}"), self.span))
            }

            // Unsupported combinations
            _ => Err(format!(
                "Cannot apply operator {:?} to values {:?} and {:?}",
                operator, self.kind, other.kind
            )),
        }
    }

    /// Apply a unary operator to this value.
    pub fn apply_unary_op(&self, operator: &ligature_ast::UnaryOperator) -> Result<Value, String> {
        match (operator, &self.kind) {
            (ligature_ast::UnaryOperator::Not, ValueKind::Boolean(value)) => {
                Ok(Value::boolean(!**value, self.span))
            }
            (ligature_ast::UnaryOperator::Negate, ValueKind::Integer(value)) => {
                Ok(Value::integer(-**value, self.span))
            }
            (ligature_ast::UnaryOperator::Negate, ValueKind::Float(value)) => {
                Ok(Value::float(-**value, self.span))
            }
            _ => Err(format!(
                "Cannot apply unary operator {:?} to value {:?}",
                operator, self.kind
            )),
        }
    }
}

/// The kind of value with optimized representations.
#[derive(Debug, Clone, PartialEq)]
pub enum ValueKind {
    /// Unit value.
    Unit,

    /// Boolean value.
    Boolean(Arc<bool>),

    /// String value with shared storage.
    String(Arc<String>),

    /// Integer value.
    Integer(Arc<i64>),

    /// Floating-point value.
    Float(Arc<f64>),

    /// Record value with shared field storage.
    Record(Arc<HashMap<String, Value>>),

    /// List value with shared element storage.
    List(Arc<Vec<Value>>),

    /// Function value.
    Function {
        /// Function parameter name
        parameter: Arc<String>,
        /// Function body expression
        body: Arc<Expr>,
    },

    /// Closure value.
    Closure {
        /// Closure parameter name
        parameter: Arc<String>,
        /// Closure body expression
        body: Arc<Expr>,
        /// Captured environment
        environment: Arc<EvaluationEnvironment>,
    },

    /// Union value.
    Union {
        /// Union variant name
        variant: Arc<String>,
        /// Union variant value (if any)
        value: Option<Arc<Value>>,
    },

    /// Module value.
    Module {
        /// Module name
        name: Arc<String>,
        /// Module environment
        environment: Arc<EvaluationEnvironment>,
    },
}

impl From<Literal> for Value {
    fn from(literal: Literal) -> Self {
        match literal {
            Literal::Unit => Value::unit(Span::default()),
            Literal::Boolean(value) => Value::boolean(value, Span::default()),
            Literal::String(value) => Value::string(value, Span::default()),
            Literal::Integer(value) => Value::integer(value, Span::default()),
            Literal::Float(value) => Value::float(value, Span::default()),
            Literal::List(elements) => {
                // Convert list elements to values (they will be evaluated later)
                // For now, create a placeholder list that will be properly evaluated
                // during the evaluation phase
                let placeholder_values = elements
                    .into_iter()
                    .map(|_| Value::unit(Span::default()))
                    .collect();
                Value::list(placeholder_values, Span::default())
            }
        }
    }
}

/// Value interner for caching frequently used values.
#[derive(Debug)]
pub struct ValueInterner {
    /// Interned strings
    strings: HashMap<String, Arc<String>>,
    /// Interned integers
    integers: HashMap<i64, Arc<i64>>,
    /// Interned floats (using bit representation for NaN/infinity handling)
    floats: HashMap<u64, Arc<f64>>,
    /// Interned booleans
    booleans: HashMap<bool, Arc<bool>>,
    /// Interned lists (using structural hashing)
    #[allow(clippy::type_complexity)]
    lists: HashMap<u64, Arc<Vec<Value>>>,
    /// Statistics
    stats: ValueInternerStats,
}

impl Clone for ValueInterner {
    fn clone(&self) -> Self {
        Self {
            strings: self.strings.clone(),
            integers: self.integers.clone(),
            floats: self.floats.clone(),
            booleans: self.booleans.clone(),
            lists: self.lists.clone(),
            stats: self.stats.clone(),
        }
    }
}

impl ValueInterner {
    /// Create a new value interner.
    pub fn new() -> Self {
        Self {
            strings: HashMap::new(),
            integers: HashMap::new(),
            floats: HashMap::new(),
            booleans: HashMap::new(),
            lists: HashMap::new(),
            stats: ValueInternerStats::default(),
        }
    }

    /// Intern a string value to avoid duplication.
    pub fn intern_string(&mut self, value: String) -> Arc<String> {
        if let Some(interned) = self.strings.get(&value) {
            interned.clone()
        } else {
            let interned = Arc::new(value.clone());
            self.strings.insert(value, interned.clone());
            self.stats.string_count = self.strings.len();
            interned
        }
    }

    /// Intern an integer value.
    pub fn intern_integer(&mut self, value: i64) -> Arc<i64> {
        if let Some(interned) = self.integers.get(&value) {
            interned.clone()
        } else {
            let interned = Arc::new(value);
            self.integers.insert(value, interned.clone());
            self.stats.integer_count = self.integers.len();
            interned
        }
    }

    /// Intern a float value.
    pub fn intern_float(&mut self, value: f64) -> Arc<f64> {
        let bits = value.to_bits();
        if let Some(interned) = self.floats.get(&bits) {
            interned.clone()
        } else {
            let interned = Arc::new(value);
            self.floats.insert(bits, interned.clone());
            self.stats.float_count = self.floats.len();
            interned
        }
    }

    /// Get or create a boolean value.
    pub fn get_boolean(&mut self, value: bool) -> Arc<bool> {
        if let Some(interned) = self.booleans.get(&value) {
            interned.clone()
        } else {
            let interned = Arc::new(value);
            self.booleans.insert(value, interned.clone());
            self.stats.boolean_count = self.booleans.len();
            interned
        }
    }

    /// Intern a list value using structural hashing.
    pub fn intern_list(&mut self, elements: Vec<Value>) -> Arc<Vec<Value>> {
        let hash = self.hash_list(&elements);
        if let Some(interned) = self.lists.get(&hash) {
            interned.clone()
        } else {
            let interned = Arc::new(elements);
            self.lists.insert(hash, interned.clone());
            self.stats.list_count = self.lists.len();
            interned
        }
    }

    /// Hash a list for structural comparison.
    fn hash_list(&self, elements: &[Value]) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let mut hasher = DefaultHasher::new();
        hasher.write_usize(elements.len());
        for element in elements {
            // Hash the value kind and basic structure
            match &element.kind {
                ValueKind::Unit => hasher.write_u8(0),
                ValueKind::Boolean(b) => {
                    hasher.write_u8(1);
                    hasher.write_u8(**b as u8);
                }
                ValueKind::String(s) => {
                    hasher.write_u8(2);
                    hasher.write(s.as_bytes());
                }
                ValueKind::Integer(i) => {
                    hasher.write_u8(3);
                    hasher.write_i64(**i);
                }
                ValueKind::Float(f) => {
                    hasher.write_u8(4);
                    hasher.write_u64((**f).to_bits());
                }
                ValueKind::List(list_elements) => {
                    hasher.write_u8(5);
                    hasher.write_usize(list_elements.len());
                }
                _ => hasher.write_u8(255), // Complex types get a generic hash
            }
        }
        hasher.finish()
    }

    /// Get statistics about the interner.
    pub fn stats(&self) -> ValueInternerStats {
        self.stats.clone()
    }

    /// Clear all interned values.
    pub fn clear(&mut self) {
        self.strings.clear();
        self.integers.clear();
        self.floats.clear();
        self.booleans.clear();
        self.lists.clear();
        self.stats = ValueInternerStats::default();
    }
}

impl Default for ValueInterner {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics for the value interner.
#[derive(Debug, Clone, Default)]
pub struct ValueInternerStats {
    pub string_count: usize,
    pub integer_count: usize,
    pub float_count: usize,
    pub boolean_count: usize,
    pub list_count: usize,
}

/// Comprehensive statistics for value optimization.
#[derive(Debug, Clone)]
pub struct ValueOptimizationStats {
    /// Value interner statistics
    pub interner: ValueInternerStats,
    /// Value pool utilization rate
    pub pool_utilization: f64,
    /// Number of available values in pool
    pub pool_available: usize,
    /// Maximum pool size
    pub pool_max: usize,
    /// Whether value optimization is enabled
    pub optimization_enabled: bool,
    /// Estimated memory savings in bytes
    pub total_memory_saved: usize,
}

impl ValueOptimizationStats {
    /// Get the total number of interned values.
    pub fn total_interned_values(&self) -> usize {
        self.interner.string_count
            + self.interner.integer_count
            + self.interner.float_count
            + self.interner.boolean_count
            + self.interner.list_count
    }

    /// Get the memory savings as a percentage.
    pub fn memory_savings_percentage(&self) -> f64 {
        if self.total_memory_saved == 0 {
            0.0
        } else {
            // This is a rough estimate - in practice would need baseline measurements
            (self.total_memory_saved as f64 / (self.total_memory_saved + 1024) as f64) * 100.0
        }
    }
}

/// Value pool for frequently used values.
#[derive(Debug)]
pub struct ValuePool {
    /// Pool of available values
    available: Vec<Value>,
    /// Maximum pool size
    max_size: usize,
    /// Current pool size
    current_size: usize,
}

impl ValuePool {
    /// Create a new value pool.
    pub fn new(max_size: usize) -> Self {
        Self {
            available: Vec::new(),
            max_size,
            current_size: 0,
        }
    }

    /// Get a value from the pool or create a new one.
    pub fn acquire(&mut self) -> Option<Value> {
        self.available.pop()
    }

    /// Return a value to the pool.
    pub fn release(&mut self, value: Value) {
        if self.current_size < self.max_size {
            self.available.push(value);
            self.current_size += 1;
        }
    }

    /// Get pool statistics.
    pub fn stats(&self) -> (usize, usize) {
        (self.available.len(), self.max_size)
    }

    /// Clear the pool.
    pub fn clear(&mut self) {
        self.available.clear();
        self.current_size = 0;
    }
}

impl Default for ValuePool {
    fn default() -> Self {
        Self::new(1000)
    }
}
