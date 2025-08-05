# Enhanced Error Reporting in Ligature

Ligature provides comprehensive error reporting with detailed explanations, fix suggestions, and intelligent diagnostics to help developers write better code faster.

## Overview

The enhanced error reporting system includes:

- **Detailed Error Explanations**: Clear, actionable error messages
- **Fix Suggestions**: Automatic suggestions for resolving issues
- **Error Categorization**: Errors organized by severity and type
- **Performance Warnings**: Suggestions for optimizing code
- **Style Recommendations**: Code quality improvements
- **Security Warnings**: Detection of potential security issues
- **Related Information**: Links to documentation and similar issues

## Error Categories

### Syntax Errors

Errors related to incorrect syntax, missing tokens, or malformed expressions.

**Example:**

```
Error: Missing closing parenthesis in function call
  at line 5, column 15 in main.lig

fun add(x: Int, y: Int) -> Int = x + y
let result = add(10, 20  // Missing closing parenthesis

Suggestion: Add ')' at the end of the function call
```

### Type Errors

Errors related to type mismatches, undefined types, or incorrect type usage.

**Example:**

```
Error: Type mismatch in function call
  Expected: Int -> Int -> Int
  Actual: String -> Int -> Int
  at line 8, column 10 in main.lig

fun add(x: Int, y: Int) -> Int = x + y
let result = add("hello", 20)  // String passed where Int expected

Suggestion: Convert "hello" to an integer or change the function signature
```

### Semantic Errors

Errors related to logical issues, undefined variables, or incorrect usage.

**Example:**

```
Error: Undefined identifier 'multiply'
  at line 12, column 15 in main.lig

let result = multiply(5, 3)  // Function 'multiply' not defined

Suggestion: Define the multiply function or import it from a module
```

### Import Errors

Errors related to module imports, missing dependencies, or circular imports.

**Example:**

```
Error: Module 'math' not found
  at line 1, column 8 in main.lig

import math as m  // Module 'math' not available

Suggestion: Check if the module exists in your register or add it to dependencies
```

## Enhanced Diagnostics Features

### Detailed Explanations

Every error includes a detailed explanation of what went wrong and why:

```
Error: Pattern matching is not exhaustive
  at line 15, column 5 in main.lig

match value with
  | Some(x) -> x
  // Missing case for None

Explanation: The pattern matching expression doesn't handle all possible cases.
The 'Option' type has two constructors: 'Some' and 'None', but only 'Some' is handled.

Suggestion: Add a case for 'None':
  | None -> defaultValue
```

### Fix Suggestions

Automatic suggestions for fixing common errors:

```
Error: Unused variable 'x'
  at line 7, column 5 in main.lig

let x = 42  // Variable 'x' is defined but never used

Suggestions:
1. Remove the unused variable: delete line 7
2. Use the variable: let result = x + 10
3. Prefix with underscore: let _x = 42
4. Add to exports if needed: export x
```

### Performance Warnings

Suggestions for improving code performance:

```
Warning: Inefficient list operation
  at line 20, column 10 in main.lig

let doubled = [x * 2 | x <- [1..1000]]  // Creates intermediate list

Suggestion: Use lazy evaluation or stream processing for large lists:
  let doubled = stream [1..1000] |> map (fun x -> x * 2)
```

### Style Recommendations

Suggestions for improving code style and readability:

```
Style: Consider using more descriptive variable names
  at line 5, column 5 in main.lig

let x = 42  // Variable name 'x' is not descriptive

Suggestion: Use a more descriptive name like 'answer' or 'result'
```

### Security Warnings

Detection of potential security issues:

```
Security Warning: Potential integer overflow
  at line 25, column 15 in main.lig

let result = a * b  // Multiplication may overflow

Suggestion: Use checked arithmetic or handle overflow explicitly:
  let result = checked_multiply a b
```

## Configuration

### VS Code Settings

Configure error reporting in VS Code settings:

```json
{
  "ligature.diagnostics.enabled": true,
  "ligature.diagnostics.enhanced": true,
  "ligature.diagnostics.showWarnings": true,
  "ligature.diagnostics.showInfo": true,
  "ligature.diagnostics.maxProblems": 100
}
```

### LSP Configuration

Configure the language server for enhanced diagnostics:

```json
{
  "ligature-lsp": {
    "diagnostics": {
      "enableDetailedExplanations": true,
      "enableFixSuggestions": true,
      "enablePerformanceWarnings": true,
      "enableStyleSuggestions": true,
      "enableSecurityWarnings": true,
      "maxProblems": 100,
      "includeWarnings": true,
      "includeInfo": true
    }
  }
}
```

## Error Severity Levels

### Error (1)

Critical issues that prevent code from running or compiling.

**Examples:**

- Syntax errors
- Type mismatches
- Undefined identifiers
- Missing imports

### Warning (2)

Issues that don't prevent execution but may cause problems.

**Examples:**

- Unused variables
- Deprecated functions
- Performance issues
- Style violations

### Information (3)

Informational messages about code quality or suggestions.

**Examples:**

- Documentation suggestions
- Best practice recommendations
- Alternative approaches

### Hint (4)

Minor suggestions for improvement.

**Examples:**

- Variable naming suggestions
- Code organization tips
- Import optimizations

## Error Reporting in Different Contexts

### Editor Integration

In VS Code, errors are displayed:

1. **Inline**: Red squiggly lines under problematic code
2. **Problems Panel**: Comprehensive list of all issues
3. **Hover**: Detailed information when hovering over errors
4. **Status Bar**: Quick summary of error count

### Command Line

When using the Ligature CLI:

```bash
$ ligature check main.lig

main.lig:5:15: error: Missing closing parenthesis
main.lig:8:10: warning: Unused variable 'x'
main.lig:12:5: info: Consider adding type annotation

3 issues found (1 error, 1 warning, 1 info)
```

### LSP Protocol

The language server provides structured diagnostic information:

```json
{
  "range": {
    "start": { "line": 4, "character": 14 },
    "end": { "line": 4, "character": 15 }
  },
  "severity": 1,
  "code": "E001",
  "source": "ligature",
  "message": "Missing closing parenthesis",
  "relatedInformation": [
    {
      "location": {
        "uri": "file:///path/to/main.lig",
        "range": {
          "start": { "line": 4, "character": 10 },
          "end": { "line": 4, "character": 15 }
        }
      },
      "message": "Opening parenthesis here"
    }
  ]
}
```

## Best Practices

### Writing Clear Error Messages

When contributing to Ligature, follow these guidelines for error messages:

1. **Be Specific**: Explain exactly what went wrong
2. **Be Actionable**: Provide clear steps to fix the issue
3. **Be Contextual**: Include relevant code context
4. **Be Helpful**: Suggest alternatives when appropriate

### Example Good Error Message

```
Error: Function 'calculate' expects 2 arguments but received 3
  at line 10, column 15 in main.lig

let result = calculate(1, 2, 3)  // Too many arguments

Function signature: fun calculate(x: Int, y: Int) -> Int

Suggestion: Remove the third argument or update the function signature
```

### Example Poor Error Message

```
Error: Wrong number of arguments
```

## Troubleshooting

### Common Issues

1. **No errors showing**: Check if diagnostics are enabled in settings
2. **Too many errors**: Adjust `maxProblems` setting
3. **Missing suggestions**: Ensure enhanced diagnostics are enabled
4. **Performance issues**: Disable unnecessary diagnostic features

### Debugging

Enable verbose logging to debug diagnostic issues:

```json
{
  "ligature.languageServer.trace": "verbose"
}
```

Check the Output panel for detailed diagnostic information.

## Future Enhancements

Planned improvements to error reporting:

- **Machine Learning**: AI-powered error suggestions
- **Error Patterns**: Recognition of common error patterns
- **Auto-fix**: Automatic application of suggested fixes
- **Error History**: Learning from previous errors
- **Integration**: Better integration with external tools

## Contributing

To contribute to error reporting:

1. **Add New Error Types**: Extend the diagnostic system
2. **Improve Messages**: Make error messages clearer
3. **Add Suggestions**: Provide better fix suggestions
4. **Test Coverage**: Ensure comprehensive test coverage

See the development documentation for technical details on extending the diagnostic system.
