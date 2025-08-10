//! Code generation actions for templates and boilerplate.

use std::collections::HashMap;

use ligature_ast::Program;
use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, Range, TextEdit, Url, WorkspaceEdit,
};

/// Handler for code generation actions.
pub struct CodeGenerationActions;

impl CodeGenerationActions {
    /// Create a new code generation actions handler.
    pub fn new() -> Self {
        Self
    }

    /// Create code generation actions.
    pub fn create_code_generation_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate boilerplate code
        actions.extend(self.create_boilerplate_actions(uri, range, content));

        // Generate constructors
        actions.extend(self.create_constructor_actions(uri, range, content, ast));

        // Generate pattern matching
        actions.extend(self.create_pattern_matching_actions(uri, range, content, ast));

        actions
    }

    /// Create enhanced code generation actions.
    pub fn create_enhanced_code_generation_actions(
        &self,
        uri: &str,
        range: Range,
        content: &str,
        ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Generate boilerplate code
        actions.extend(self.create_enhanced_boilerplate_actions(uri, range, content));

        // Generate constructors
        actions.extend(self.create_enhanced_constructor_actions(uri, range, content, ast));

        // Generate pattern matching
        actions.extend(self.create_enhanced_pattern_matching_actions(uri, range, content, ast));

        // Generate tests
        actions.extend(self.create_test_generation_actions(uri, range, content, ast));

        // Generate documentation
        actions.extend(self.create_documentation_generation_actions(uri, range, content, ast));

        actions
    }

    /// Create boilerplate code generation actions.
    fn create_boilerplate_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate function template
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate function template".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "fun ${1:name}(${2:params}) : ${3:return_type} = ${4:body}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate type definition
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate type definition".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "type ${1:TypeName} = ${2:definition}".to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create enhanced boilerplate actions.
    fn create_enhanced_boilerplate_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate function template
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate function template".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "fun ${1:name}(${2:params}) : ${3:return_type} = ${4:body}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate type definition
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate type definition".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "type ${1:TypeName} = ${2:definition}".to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate module template
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate module template".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "module ${1:ModuleName} {\n  ${2:// module content}\n}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create constructor generation actions.
    fn create_constructor_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate data type with constructors
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate data type with constructors".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "data ${1:TypeName} = ${2:Constructor1} | ${3:Constructor2}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create enhanced constructor actions.
    fn create_enhanced_constructor_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate data type with constructors
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate data type with constructors".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "data ${1:TypeName} = ${2:Constructor1} | ${3:Constructor2}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate type class
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate type class".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "class ${1:ClassName} a where\n  ${2:method1} :: a -> \
                                       ${3:ResultType}\n  ${4:method2} :: a -> ${5:ResultType}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create pattern matching generation actions.
    fn create_pattern_matching_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        let actions = vec![CodeActionOrCommand::CodeAction(CodeAction {
            title: "Generate match expression".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    Url::parse(uri).ok().unwrap(),
                    vec![TextEdit {
                        range,
                        new_text: "match ${1:expression} of\n  ${2:pattern1} => ${3:result1}\n  \
                                   ${4:pattern2} => ${5:result2}"
                            .to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        })];

        actions
    }

    /// Create enhanced pattern matching actions.
    fn create_enhanced_pattern_matching_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate match expression
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate match expression".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "match ${1:expression} of\n  ${2:pattern1} => \
                                       ${3:result1}\n  ${4:pattern2} => ${5:result2}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate if-else expression
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate if-else expression".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "if ${1:condition} then\n  ${2:then_branch}\nelse\n  \
                                       ${3:else_branch}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create test generation actions.
    fn create_test_generation_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate unit test
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate unit test".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "test \"${1:test_name}\" = ${2:test_expression}".to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate property test
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate property test".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "property \"${1:property_name}\" = forAll ${2:generator} \
                                       ${3:property}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    /// Create documentation generation actions.
    fn create_documentation_generation_actions(
        &self,
        uri: &str,
        range: Range,
        _content: &str,
        _ast: Option<&Program>,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Generate function documentation
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate function documentation".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "/// ${1:Function description}\n/// @param ${2:param_name} \
                                       ${3:param_description}\n/// @return ${4:return_description}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Generate module documentation
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Generate module documentation".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::from([(
                        Url::parse(uri).ok().unwrap(),
                        vec![TextEdit {
                            range,
                            new_text: "/// ${1:Module description}\n/// @author \
                                       ${2:author_name}\n/// @version ${3:version}"
                                .to_string(),
                        }],
                    )])),
                    document_changes: None,
                    change_annotations: None,
                }),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }
}

impl Default for CodeGenerationActions {
    fn default() -> Self {
        Self::new()
    }
}
