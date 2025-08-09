# Next Steps Prompt: Complete Ligature Parser Migration

## 🎯 **Primary Objective**

Complete the systematic migration of the `ligature-parser` crate from the old `AstError`/`AstResult` system to the new `StandardError`/`StandardResult` system with enhanced error handling.

## 📊 **Current Status**

- **Crate**: `ligature-parser`
- **Progress**: 0% (fresh start after revert)
- **Dependencies**: Already configured correctly
- **Infrastructure**: New error types available and ready

## 🔧 **Required Actions**

### **Phase 1: Systematic Import and Type Updates (30 minutes)**

1. **Update Imports in `parser.rs`**:

   ```rust
   // Remove old imports
   use ligature_ast::{AstError, AstResult, ...};

   // Add new imports
   use ligature_error::{StandardError, StandardResult};
   use ligature_ast::{
       BinaryOperator, Declaration, Expr, ExprKind, Import, ImportItem, Literal, Program, Span, Type,
       TypeAlias, TypeConstructor, TypeKind, TypeVariant, UnaryOperator,
       decl::{ExportDeclaration, ExportItem, InstanceDeclaration, MethodImplementation, MethodSignature, TypeClassConstraint, TypeClassDeclaration},
       expr::{MatchCase, Pattern, RecordField, RecordPatternField},
       ty::TypeField,
   };
   ```

2. **Update Function Signatures**:
   - Replace all `AstResult<T>` with `StandardResult<T>`
   - Update public API functions in `lib.rs`
   - Update all internal parsing functions

### **Phase 2: Core Function Migration (45 minutes)**

3. **Migrate Main Parsing Functions**:

   - `parse_program()` - Update error handling and return type
   - `parse_expression()` - Update error handling
   - `parse_type()` - Update error handling
   - `parse_module()` - Change return type from `Module` to `Type`

4. **Update Error Construction Pattern**:

   ```rust
   // Old pattern
   AstError::ParseError {
       message: "...",
       span: Span::default(),
   }

   // New pattern
   StandardError::Ligature(ligature_ast::LigatureError::Parse {
       code: ligature_ast::ErrorCode::E1001,
       message: format!("..."),
       span: Span::default(),
       suggestions: vec!["Check for syntax errors".to_string()],
   })
   ```

### **Phase 3: Systematic Error Replacement (1 hour)**

5. **Replace All AstError::ParseError Occurrences**:
   - **Approximately 50+ locations** throughout the parser
   - **Strategy**: Work in batches of 10-15 functions
   - **Validation**: Test compilation after each batch
   - **Focus areas**:
     - Expression parsing functions
     - Type parsing functions
     - Declaration parsing functions
     - Pattern parsing functions

### **Phase 4: Type System Compatibility (15 minutes)**

6. **Fix Type System Issues**:
   - Update struct field access (e.g., remove `span` from `ImportItem`)
   - Fix expression constructors (e.g., `Expr::Literal(Literal::Integer(...))`)
   - Update `Module` struct usage to `Type::module(...)`

### **Phase 5: Testing and Validation (15 minutes)**

7. **Comprehensive Testing**:
   - `cargo check --package ligature-parser`
   - `cargo test --package ligature-parser`
   - Test with dependent crates if available

## 🎯 **Success Criteria**

The migration will be **complete** when:

1. ✅ **Zero AstError references** in the codebase
2. ✅ **Successful compilation** with no errors
3. ✅ **All tests passing** with new error handling
4. ✅ **Consistent error structure** throughout the parser
5. ✅ **Proper error codes** and suggestions in error messages

## 📋 **Execution Strategy**

### **Recommended Approach: Batch Processing**

1. **Start with imports and function signatures** (15 minutes)
2. **Migrate core functions first** (30 minutes)
3. **Systematic error replacement in batches** (1 hour)
4. **Fix any remaining type issues** (15 minutes)
5. **Final testing and validation** (15 minutes)

### **Quality Assurance**

- **Test compilation after each batch** to catch issues early
- **Preserve error message content** while enhancing structure
- **Maintain backward compatibility** where possible
- **Document any breaking changes** for dependent crates

## 🚀 **Expected Outcome**

Once complete, the `ligature-parser` crate will have:

- **Modern error handling** with structured error codes (E1001-E1008)
- **Rich error messages** with context and user-friendly suggestions
- **Type-safe error handling** with `StandardResult<T>`
- **Consistent API** with the rest of the Ligature ecosystem
- **Enhanced debugging** capabilities with detailed error information

## 📈 **Confidence Level**

**95%** - The migration path is well-defined, the infrastructure is ready, and the approach is systematic. The major challenges have been identified and solutions are available.

## 🔄 **Next Crate After Completion**

After `ligature-parser` is complete, the next logical crates to migrate would be:

1. `ligature-eval` - Evaluation engine
2. `ligature-lsp` - Language server
3. `ligature-types` - Type system

## 💡 **Key Insights**

1. **Fresh Start Advantage**: The revert provides a clean slate for systematic migration
2. **Infrastructure Ready**: All new error types and dependencies are properly configured
3. **Systematic Approach**: The batch processing strategy minimizes risk and maximizes efficiency
4. **Clear Success Criteria**: Well-defined completion requirements ensure quality

---

**Ready to proceed with the systematic migration of `ligature-parser`?**
