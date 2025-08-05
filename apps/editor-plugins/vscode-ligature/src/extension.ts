import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
  RevealOutputChannelOn,
  State
} from 'vscode-languageclient/node';

let client: LanguageClient;
let semanticTokensProvider: vscode.DocumentSemanticTokensProvider;
let inlayHintsProvider: vscode.InlayHintsProvider;

// Configuration interface
interface LigatureConfig {
  languageServer: {
    enabled: boolean;
    path: string;
    args: string[];
    trace: 'off' | 'messages' | 'verbose';
  };
  diagnostics: {
    enabled: boolean;
    enhanced: boolean;
  };
  completion: {
    enabled: boolean;
    enhanced: boolean;
    enableSnippets: boolean;
    enableAutoImport: boolean;
    enableFuzzyMatching: boolean;
    enableContextAware: boolean;
  };
  formatting: {
    enabled: boolean;
    indentSize: number;
    maxLineLength: number;
    enableOnSave: boolean;
    enableOnPaste: boolean;
  };
  hover: {
    enabled: boolean;
    enableTypeInfo: boolean;
    enableDocumentation: boolean;
  };
  symbols: {
    enabled: boolean;
  };
  references: {
    enabled: boolean;
  };
  rename: {
    enabled: boolean;
  };
  codeActions: {
    enabled: boolean;
    enableQuickFixes: boolean;
    enableRefactoring: boolean;
    enableCodeGeneration: boolean;
  };
  inlayHints: {
    enabled: boolean;
    enableTypeHints: boolean;
    enableParameterHints: boolean;
  };
  semanticHighlighting: {
    enabled: boolean;
    enableTypeHighlighting: boolean;
    enableFunctionHighlighting: boolean;
  };
  workspace: {
    enableWorkspaceSymbols: boolean;
    maxFiles: number;
    includePatterns: string[];
    excludePatterns: string[];
  };
  performance: {
    enableIncrementalParsing: boolean;
    enableCaching: boolean;
    maxCacheSize: number;
  };
}

// Get configuration from VS Code settings
function getConfiguration(): LigatureConfig {
  const config = vscode.workspace.getConfiguration('ligature');
  
  return {
    languageServer: {
      enabled: config.get('languageServer.enabled', true),
      path: config.get('languageServer.path', 'ligature-lsp'),
      args: config.get('languageServer.args', ['--enhanced']),
      trace: config.get('languageServer.trace', 'off')
    },
    diagnostics: {
      enabled: config.get('diagnostics.enabled', true),
      enhanced: config.get('diagnostics.enhanced', true)
    },
    completion: {
      enabled: config.get('completion.enabled', true),
      enhanced: config.get('completion.enhanced', true),
      enableSnippets: config.get('completion.enableSnippets', true),
      enableAutoImport: config.get('completion.enableAutoImport', true),
      enableFuzzyMatching: config.get('completion.enableFuzzyMatching', true),
      enableContextAware: config.get('completion.enableContextAware', true)
    },
    formatting: {
      enabled: config.get('formatting.enabled', true),
      indentSize: config.get('formatting.indentSize', 2),
      maxLineLength: config.get('formatting.maxLineLength', 80),
      enableOnSave: config.get('formatting.enableOnSave', true),
      enableOnPaste: config.get('formatting.enableOnPaste', true)
    },
    hover: {
      enabled: config.get('hover.enabled', true),
      enableTypeInfo: config.get('hover.enableTypeInfo', true),
      enableDocumentation: config.get('hover.enableDocumentation', true)
    },
    symbols: {
      enabled: config.get('symbols.enabled', true)
    },
    references: {
      enabled: config.get('references.enabled', true)
    },
    rename: {
      enabled: config.get('rename.enabled', true)
    },
    codeActions: {
      enabled: config.get('codeActions.enabled', true),
      enableQuickFixes: config.get('codeActions.enableQuickFixes', true),
      enableRefactoring: config.get('codeActions.enableRefactoring', true),
      enableCodeGeneration: config.get('codeActions.enableCodeGeneration', true)
    },
    inlayHints: {
      enabled: config.get('inlayHints.enabled', true),
      enableTypeHints: config.get('inlayHints.enableTypeHints', true),
      enableParameterHints: config.get('inlayHints.enableParameterHints', true)
    },
    semanticHighlighting: {
      enabled: config.get('semanticHighlighting.enabled', true),
      enableTypeHighlighting: config.get('semanticHighlighting.enableTypeHighlighting', true),
      enableFunctionHighlighting: config.get('semanticHighlighting.enableFunctionHighlighting', true)
    },
    workspace: {
      enableWorkspaceSymbols: config.get('workspace.enableWorkspaceSymbols', true),
      maxFiles: config.get('workspace.maxFiles', 1000),
      includePatterns: config.get('workspace.includePatterns', ['**/*.lig']),
      excludePatterns: config.get('workspace.excludePatterns', ['**/target/**', '**/node_modules/**'])
    },
    performance: {
      enableIncrementalParsing: config.get('performance.enableIncrementalParsing', true),
      enableCaching: config.get('performance.enableCaching', true),
      maxCacheSize: config.get('performance.maxCacheSize', 100)
    }
  };
}

// Find the language server executable
function findLanguageServer(config: LigatureConfig): string {
  const serverPath = config.languageServer.path;
  
  // If it's an absolute path, use it directly
  if (path.isAbsolute(serverPath)) {
    return serverPath;
  }
  
  // Check if it's in PATH
  if (serverPath === 'ligature-lsp') {
    // Try to find in common locations
    const commonPaths = [
      path.join(__dirname, '..', '..', '..', 'target', 'release', 'ligature-lsp'),
      path.join(__dirname, '..', '..', '..', 'target', 'debug', 'ligature-lsp'),
      path.join(__dirname, '..', '..', '..', 'crates', 'ligature-lsp', 'target', 'release', 'ligature-lsp'),
      path.join(__dirname, '..', '..', '..', 'crates', 'ligature-lsp', 'target', 'debug', 'ligature-lsp')
    ];
    
    for (const commonPath of commonPaths) {
      if (fs.existsSync(commonPath)) {
        return commonPath;
      }
    }
  }
  
  // Return the original path (will be looked up in PATH)
  return serverPath;
}

// Custom error handler for better error reporting
class LigatureErrorHandler {
  private restarts: number = 0;
  private readonly maxRestarts: number = 5;
  
  error(_error: Error, _message: any, count: number): any {
    if (count && count <= 3) {
      return { action: 1 }; // Continue
    }
    return { action: 2 }; // Shutdown
  }
  
  closed(): any {
    this.restarts++;
    if (this.restarts <= this.maxRestarts) {
      vscode.window.showInformationMessage(
        `Ligature language server connection lost. Attempting to restart (${this.restarts}/${this.maxRestarts})...`
      );
      return { action: 1 }; // Restart
    }
    
    vscode.window.showErrorMessage(
      'Ligature language server failed to start after multiple attempts. Please check your configuration.'
    );
    return { action: 2 }; // DoNotRestart
  }
}

// Create server options
function createServerOptions(config: LigatureConfig): ServerOptions {
  const serverPath = findLanguageServer(config);
  
  // Check if the server executable exists
  if (!fs.existsSync(serverPath) && !path.isAbsolute(serverPath)) {
    vscode.window.showWarningMessage(
      `Ligature language server not found at: ${serverPath}. Please build the server or update the path in settings.`
    );
  }
  
  return {
    run: {
      command: serverPath,
      args: config.languageServer.args,
      transport: TransportKind.stdio,
      options: {
        cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath
      }
    },
    debug: {
      command: serverPath,
      args: [...config.languageServer.args, '--debug'],
      transport: TransportKind.stdio,
      options: {
        cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath
      }
    }
  };
}

// Create client options
function createClientOptions(config: LigatureConfig): LanguageClientOptions {
  return {
    documentSelector: [
      { scheme: 'file', language: 'ligature' },
      { scheme: 'untitled', language: 'ligature' }
    ],
    synchronize: {
      fileEvents: [
        vscode.workspace.createFileSystemWatcher('**/*.lig'),
        vscode.workspace.createFileSystemWatcher('**/register.toml')
      ]
    },
    diagnosticCollectionName: 'ligature',
    revealOutputChannelOn: RevealOutputChannelOn.Never,
    errorHandler: new LigatureErrorHandler(),
    middleware: {
      // Enhanced hover information
      provideHover: async (document, position, token, next) => {
        if (!config.hover.enabled) {
          return null;
        }
        const hover = await next(document, position, token);
        if (hover && config.hover.enableTypeInfo) {
          // Enhance hover with additional type information
          return enhanceHoverWithTypeInfo(hover, document, position);
        }
        return hover;
      },
      
      // Enhanced completion with context awareness
      provideCompletionItem: async (document, position, context, token, next) => {
        if (!config.completion.enabled) {
          return null;
        }
        const completion = await next(document, position, context, token);
        if (completion && config.completion.enableContextAware) {
          return enhanceCompletionWithContext(completion, document, position, context);
        }
        return completion;
      }
    },
    outputChannel: vscode.window.createOutputChannel('Ligature Language Server'),
    traceOutputChannel: vscode.window.createOutputChannel('Ligature Language Server Trace')
  };
}

// Enhanced hover with type information
function enhanceHoverWithTypeInfo(hover: any, document: vscode.TextDocument, position: vscode.Position): any {
  // Add type information to hover if available
  const wordRange = document.getWordRangeAtPosition(position);
  if (wordRange) {
    // This would be enhanced by the language server
    return hover;
  }
  return hover;
}

// Enhanced completion with context awareness
function enhanceCompletionWithContext(completion: any, document: vscode.TextDocument, position: vscode.Position, _context: any): any {
  // Add context-aware suggestions
  const linePrefix = document.lineAt(position).text.substring(0, position.character);
  
  // Detect context and enhance completion accordingly
  if (linePrefix.includes('fun ') && !linePrefix.includes('->')) {
    // Function definition context
    return addFunctionContextCompletions(completion);
  } else if (linePrefix.includes('type ') && !linePrefix.includes('=')) {
    // Type definition context
    return addTypeContextCompletions(completion);
  } else if (linePrefix.includes('import ')) {
    // Import context
    return addImportContextCompletions(completion);
  }
  
  return completion;
}

// Add function context completions
function addFunctionContextCompletions(completion: any): any {
  if (completion && completion.items) {
    // Filter and enhance function-related completions
    completion.items = completion.items.filter((item: any) => 
      item.kind === vscode.CompletionItemKind.Function ||
      item.kind === vscode.CompletionItemKind.Keyword
    );
  }
  return completion;
}

// Add type context completions
function addTypeContextCompletions(completion: any): any {
  if (completion && completion.items) {
    // Filter and enhance type-related completions
    completion.items = completion.items.filter((item: any) => 
      item.kind === vscode.CompletionItemKind.Class ||
      item.kind === vscode.CompletionItemKind.TypeParameter
    );
  }
  return completion;
}

// Add import context completions
function addImportContextCompletions(completion: any): any {
  if (completion && completion.items) {
    // Filter and enhance import-related completions
    completion.items = completion.items.filter((item: any) => 
      item.kind === vscode.CompletionItemKind.Module ||
      item.kind === vscode.CompletionItemKind.File
    );
  }
  return completion;
}

// Cache for diagnostics (placeholder for future use)
const diagnosticsCache = new Map<string, any[]>();

// Start the language client
async function startLanguageClient(): Promise<void> {
  const config = getConfiguration();
  
  if (!config.languageServer.enabled) {
    vscode.window.showInformationMessage('Ligature language server is disabled in settings.');
    return;
  }
  
  const serverOptions = createServerOptions(config);
  const clientOptions = createClientOptions(config);
  
  client = new LanguageClient(
    'ligature',
    'Ligature Language Server',
    serverOptions,
    clientOptions
  );
  
  // Register status bar item
  const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
  statusBarItem.text = '$(light-bulb) Ligature';
  statusBarItem.tooltip = 'Ligature Language Server';
  
  // Update status bar based on client state
  client.onDidChangeState((state) => {
    if (state.newState === State.Starting) {
      statusBarItem.text = '$(sync~spin) Ligature';
      statusBarItem.tooltip = 'Ligature Language Server - Starting...';
      statusBarItem.show();
    } else if (state.newState === State.Running) {
      statusBarItem.text = '$(check) Ligature';
      statusBarItem.tooltip = 'Ligature Language Server - Running';
      statusBarItem.show();
    } else if (state.newState === State.Stopped) {
      statusBarItem.text = '$(error) Ligature';
      statusBarItem.tooltip = 'Ligature Language Server - Stopped';
      statusBarItem.show();
    }
  });
  
  try {
    await client.start();
    vscode.window.showInformationMessage('Ligature language server started successfully.');
  } catch (error) {
    vscode.window.showErrorMessage(`Failed to start Ligature language server: ${error}`);
    statusBarItem.dispose();
  }
}

// Stop the language client
async function stopLanguageClient(): Promise<void> {
  if (client) {
    await client.stop();
    client.dispose();
  }
}

// Restart the language server
async function restartLanguageServer(): Promise<void> {
  await stopLanguageClient();
  await startLanguageClient();
}

// Show diagnostics in a new tab
async function showDiagnostics(): Promise<void> {
  const config = getConfiguration();
  if (!config.diagnostics.enabled) {
    vscode.window.showWarningMessage('Diagnostics are disabled in settings.');
    return;
  }
  
  const document = vscode.window.activeTextEditor?.document;
  if (!document || document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  // Trigger diagnostics refresh
  await vscode.commands.executeCommand('workbench.action.problems.focus');
}

// Format document
async function formatDocument(): Promise<void> {
  const config = getConfiguration();
  if (!config.formatting.enabled) {
    vscode.window.showWarningMessage('Formatting is disabled in settings.');
    return;
  }
  
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.formatDocument');
}

// Show hover information
async function showHover(): Promise<void> {
  const config = getConfiguration();
  if (!config.hover.enabled) {
    vscode.window.showWarningMessage('Hover information is disabled in settings.');
    return;
  }
  
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.showHover');
}

// Go to definition
async function goToDefinition(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.revealDefinition');
}

// Find all references
async function findReferences(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.findReferences');
}

// Rename symbol
async function renameSymbol(): Promise<void> {
  const config = getConfiguration();
  if (!config.rename.enabled) {
    vscode.window.showWarningMessage('Symbol renaming is disabled in settings.');
    return;
  }
  
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.rename');
}

// Organize imports
async function organizeImports(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file first.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.organizeImports');
}

// Show document symbols
async function showSymbols(): Promise<void> {
  const config = getConfiguration();
  if (!config.symbols.enabled) {
    vscode.window.showWarningMessage('Symbol navigation is disabled in settings.');
    return;
  }
  
  await vscode.commands.executeCommand('workbench.action.gotoSymbol');
}

// Show workspace symbols
async function showWorkspaceSymbols(): Promise<void> {
  const config = getConfiguration();
  if (!config.workspace.enableWorkspaceSymbols) {
    vscode.window.showWarningMessage('Workspace symbols are disabled in settings.');
    return;
  }
  
  await vscode.commands.executeCommand('workbench.action.showAllSymbols');
}

// Enhanced semantic tokens provider
function provideEnhancedSemanticTokens(document: vscode.TextDocument, token: vscode.CancellationToken): vscode.SemanticTokens {
  const tokensBuilder = new vscode.SemanticTokensBuilder();
  const text = document.getText();
  const lines = text.split('\n');
  
  for (let lineIndex = 0; lineIndex < lines.length; lineIndex++) {
    const line = lines[lineIndex];
    const words = line.split(/\s+/);
    let charOffset = 0;
    
    for (const word of words) {
      if (token.isCancellationRequested) break;
      
      const startPos = line.indexOf(word, charOffset);
      if (startPos !== -1) {
        // Determine token type based on word content and context
        const tokenType = getSemanticTokenType(word, line);
        if (tokenType !== null) {
          tokensBuilder.push(
            new vscode.Range(lineIndex, startPos, lineIndex, startPos + word.length),
            tokenType,
            []
          );
        }
        charOffset = startPos + word.length;
      }
    }
  }
  
  return tokensBuilder.build();
}

// Get semantic token type for a word
function getSemanticTokenType(word: string, line: string): string | null {
  // Keywords
  const keywords = ['fun', 'let', 'in', 'type', 'data', 'match', 'case', 'of', 'when', 'if', 'then', 'else', 'import', 'export', 'module', 'class', 'instance', 'where'];
  if (keywords.includes(word)) {
    return 'keyword';
  }
  
  // Function names (after 'fun' keyword)
  if (line.includes('fun ') && line.indexOf('fun ') < line.indexOf(word)) {
    return 'function';
  }
  
  // Type names (after 'type' keyword)
  if (line.includes('type ') && line.indexOf('type ') < line.indexOf(word)) {
    return 'type';
  }
  
  // Variables (after 'let' keyword)
  if (line.includes('let ') && line.indexOf('let ') < line.indexOf(word)) {
    return 'variable';
  }
  
  // Strings
  if (word.startsWith('"') && word.endsWith('"')) {
    return 'string';
  }
  
  // Numbers
  if (/^\d+$/.test(word)) {
    return 'number';
  }
  
  // Comments
  if (line.trim().startsWith('//') || line.trim().startsWith('/*')) {
    return 'comment';
  }
  
  return null;
}

// Enhanced inlay hints provider
function provideEnhancedInlayHints(document: vscode.TextDocument, range: vscode.Range, token: vscode.CancellationToken): vscode.InlayHint[] {
  const hints: vscode.InlayHint[] = [];
  const config = getConfiguration();
  
  if (!config.inlayHints.enabled) {
    return hints;
  }
  
  const text = document.getText();
  const lines = text.split('\n');
  
  for (let lineIndex = range.start.line; lineIndex <= range.end.line; lineIndex++) {
    if (token.isCancellationRequested) break;
    
    const line = lines[lineIndex];
    
    // Add type hints for function parameters
    if (config.inlayHints.enableTypeHints) {
      const functionMatches = line.match(/fun\s+(\w+)\s*\(([^)]*)\)/);
      if (functionMatches) {
        const params = functionMatches[2].split(',').map(p => p.trim());
        let paramStart = line.indexOf('(') + 1;
        
        for (const param of params) {
          if (param) {
            const hint = new vscode.InlayHint(
              new vscode.Position(lineIndex, paramStart + param.length),
              `: ${inferParameterType(param)}`,
              vscode.InlayHintKind.Type
            );
            hints.push(hint);
          }
          paramStart += param.length + 2; // +2 for ", "
        }
      }
    }
    
    // Add parameter name hints
    if (config.inlayHints.enableParameterHints) {
      const functionCallMatches = line.match(/(\w+)\s*\(([^)]*)\)/);
      if (functionCallMatches && !line.includes('fun ')) {
        const functionName = functionCallMatches[1];
        const args = functionCallMatches[2].split(',').map(a => a.trim());
        let argStart = line.indexOf('(') + 1;
        
        for (const arg of args) {
          if (arg) {
            const paramName = inferParameterName(functionName);
            if (paramName) {
              const hint = new vscode.InlayHint(
                new vscode.Position(lineIndex, argStart),
                `${paramName}: `,
                vscode.InlayHintKind.Parameter
              );
              hints.push(hint);
            }
          }
          argStart += arg.length + 2; // +2 for ", "
        }
      }
    }
  }
  
  return hints;
}

// Infer parameter type based on value
function inferParameterType(param: string): string {
  if (/^\d+$/.test(param)) return 'Int';
  if (/^\d+\.\d+$/.test(param)) return 'Float';
  if (param.startsWith('"') && param.endsWith('"')) return 'String';
  if (param === 'true' || param === 'false') return 'Bool';
  if (param.startsWith('[') && param.endsWith(']')) return 'List';
  return 'Any';
}

// Infer parameter name based on function and argument
function inferParameterName(functionName: string): string | null {
  // Common parameter names for standard functions
  const commonParams: { [key: string]: string[] } = {
    'add': ['a', 'b'],
    'sub': ['a', 'b'],
    'mul': ['a', 'b'],
    'div': ['a', 'b'],
    'map': ['f', 'list'],
    'filter': ['pred', 'list'],
    'fold': ['f', 'init', 'list']
  };
  
  if (commonParams[functionName]) {
    const argIndex = 0; // Simplified - would need more context
    return commonParams[functionName][argIndex] || null;
  }
  
  return null;
}

// Format document on save
async function formatDocumentOnSave(_document: vscode.TextDocument): Promise<void> {
  const config = getConfiguration();
  if (!config.formatting.enabled) return;
  
  try {
    await vscode.commands.executeCommand('editor.action.formatDocument');
  } catch (error) {
    console.error('Failed to format document on save:', error);
  }
}

// Format document on paste
async function formatDocumentOnPaste(_document: vscode.TextDocument, _change: vscode.TextDocumentContentChangeEvent): Promise<void> {
  const config = getConfiguration();
  if (!config.formatting.enabled) return;
  
  try {
    // Format the pasted content
    await vscode.commands.executeCommand('editor.action.formatSelection');
  } catch (error) {
    console.error('Failed to format pasted content:', error);
  }
}

// Advanced refactoring commands
async function refactorExtractFunction(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please select code in a Ligature file to extract.');
    return;
  }
  
  if (editor.selection.isEmpty) {
    vscode.window.showWarningMessage('Please select code to extract into a function.');
    return;
  }
  
  const functionName = await vscode.window.showInputBox({
    prompt: 'Enter function name:',
    placeHolder: 'extractedFunction'
  });
  
  if (functionName) {
    await vscode.commands.executeCommand('editor.action.refactor.extract.function');
  }
}

async function refactorInlineVariable(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please select a variable in a Ligature file to inline.');
    return;
  }
  
  await vscode.commands.executeCommand('editor.action.inline');
}

async function refactorExtractConstant(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please select a value in a Ligature file to extract.');
    return;
  }
  
  if (editor.selection.isEmpty) {
    vscode.window.showWarningMessage('Please select a value to extract into a constant.');
    return;
  }
  
  const constantName = await vscode.window.showInputBox({
    prompt: 'Enter constant name:',
    placeHolder: 'EXTRACTED_CONSTANT'
  });
  
  if (constantName) {
    await vscode.commands.executeCommand('editor.action.refactor.extract.constant');
  }
}

async function generateTests(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file to generate tests.');
    return;
  }
  
  const functionName = await vscode.window.showInputBox({
    prompt: 'Enter function name to generate tests for:',
    placeHolder: 'functionName'
  });
  
  if (functionName) {
    // Generate test template
    const testTemplate = `test "${functionName}_basic" =
  ${functionName} ${generateTestInputs(functionName)}
  where
    expected = ${generateExpectedOutput(functionName)}
    actual = ${functionName} ${generateTestInputs(functionName)}`;
    
    const testDocument = await vscode.workspace.openTextDocument({
      content: testTemplate,
      language: 'ligature'
    });
    
    await vscode.window.showTextDocument(testDocument);
  }
}

async function generateDocumentation(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'ligature') {
    vscode.window.showWarningMessage('Please open a Ligature file to generate documentation.');
    return;
  }
  
  const selection = editor.selection;
  if (selection.isEmpty) {
    vscode.window.showWarningMessage('Please select a function to generate documentation for.');
    return;
  }
  
  const functionName = await vscode.window.showInputBox({
    prompt: 'Enter function name to document:',
    placeHolder: 'functionName'
  });
  
  if (functionName) {
    const docTemplate = `/**
 * ${functionName} - Brief description
 *
 * @param param1 Description of parameter 1
 * @param param2 Description of parameter 2
 * @returns Description of return value
 */`;
    
    // Insert documentation above the function
    await editor.edit(editBuilder => {
      editBuilder.insert(selection.start, docTemplate + '\n\n');
    });
  }
}

// Helper functions for test generation
function generateTestInputs(functionName: string): string {
  // Generate appropriate test inputs based on function name
  const commonInputs: { [key: string]: string } = {
    'add': '1 2',
    'sub': '5 3',
    'mul': '4 6',
    'div': '10 2',
    'map': 'fun x -> x + 1 [1, 2, 3]',
    'filter': 'fun x -> x > 0 [1, -2, 3, -4]',
    'fold': 'fun acc x -> acc + x 0 [1, 2, 3, 4]'
  };
  
  return commonInputs[functionName] || 'input1 input2';
}

function generateExpectedOutput(functionName: string): string {
  // Generate expected output based on function name
  const commonOutputs: { [key: string]: string } = {
    'add': '3',
    'sub': '2',
    'mul': '24',
    'div': '5',
    'map': '[2, 3, 4]',
    'filter': '[1, 3]',
    'fold': '10'
  };
  
  return commonOutputs[functionName] || 'expectedResult';
}

// Extension activation
export async function activate(context: vscode.ExtensionContext): Promise<void> {
  console.log('Ligature extension is now active!');
  
  const config = getConfiguration();
  
  // Register commands
  context.subscriptions.push(
    vscode.commands.registerCommand('ligature.restartLanguageServer', restartLanguageServer),
    vscode.commands.registerCommand('ligature.showDiagnostics', showDiagnostics),
    vscode.commands.registerCommand('ligature.formatDocument', formatDocument),
    vscode.commands.registerCommand('ligature.showHover', showHover),
    vscode.commands.registerCommand('ligature.goToDefinition', goToDefinition),
    vscode.commands.registerCommand('ligature.findReferences', findReferences),
    vscode.commands.registerCommand('ligature.renameSymbol', renameSymbol),
    vscode.commands.registerCommand('ligature.organizeImports', organizeImports),
    vscode.commands.registerCommand('ligature.showSymbols', showSymbols),
    vscode.commands.registerCommand('ligature.showWorkspaceSymbols', showWorkspaceSymbols),
    vscode.commands.registerCommand('ligature.refactorExtractFunction', refactorExtractFunction),
    vscode.commands.registerCommand('ligature.refactorInlineVariable', refactorInlineVariable),
    vscode.commands.registerCommand('ligature.refactorExtractConstant', refactorExtractConstant),
    vscode.commands.registerCommand('ligature.generateTests', generateTests),
    vscode.commands.registerCommand('ligature.generateDocumentation', generateDocumentation)
  );
  
  // Register semantic tokens provider for enhanced syntax highlighting
  if (config.semanticHighlighting.enabled) {
    const semanticTokensLegend = new vscode.SemanticTokensLegend(
      ['function', 'variable', 'type', 'keyword', 'string', 'number', 'comment', 'operator'],
      ['declaration', 'definition', 'readonly', 'static', 'deprecated', 'abstract', 'async', 'modification', 'documentation', 'defaultLibrary']
    );
    
    semanticTokensProvider = {
      provideDocumentSemanticTokens(document: vscode.TextDocument, token: vscode.CancellationToken): vscode.ProviderResult<vscode.SemanticTokens> {
        if (document.languageId !== 'ligature') {
          return null;
        }
        return provideEnhancedSemanticTokens(document, token);
      }
    };
    
    context.subscriptions.push(
      vscode.languages.registerDocumentSemanticTokensProvider(
        { language: 'ligature' },
        semanticTokensProvider,
        semanticTokensLegend
      )
    );
  }
  
  // Register inlay hints provider
  if (config.inlayHints.enabled) {
    inlayHintsProvider = {
      provideInlayHints(document: vscode.TextDocument, range: vscode.Range, token: vscode.CancellationToken): vscode.ProviderResult<vscode.InlayHint[]> {
        if (document.languageId !== 'ligature') {
          return [];
        }
        return provideEnhancedInlayHints(document, range, token);
      }
    };
    
    context.subscriptions.push(
      vscode.languages.registerInlayHintsProvider(
        { language: 'ligature' },
        inlayHintsProvider
      )
    );
  }
  
  // Register format on save and paste
  if (config.formatting.enableOnSave) {
    context.subscriptions.push(
      vscode.workspace.onWillSaveTextDocument(async (event) => {
        if (event.document.languageId === 'ligature' && event.reason === vscode.TextDocumentSaveReason.Manual) {
          event.waitUntil(formatDocumentOnSave(event.document));
        }
      })
    );
  }
  
  if (config.formatting.enableOnPaste) {
    context.subscriptions.push(
      vscode.workspace.onDidChangeTextDocument(async (event) => {
        if (event.document.languageId === 'ligature' && event.contentChanges.length > 0) {
          // Check if this was a paste operation
          const change = event.contentChanges[0];
          if (change.text.length > 10) { // Likely a paste
            await formatDocumentOnPaste(event.document, change);
          }
        }
      })
    );
  }
  
  // Start the language client
  await startLanguageClient();
  
  // Register configuration change listener
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(async (event) => {
      if (event.affectsConfiguration('ligature')) {
        vscode.window.showInformationMessage('Ligature configuration changed. Restarting language server...');
        await restartLanguageServer();
      }
    })
  );
  
  // Show welcome message
  if (config.languageServer.enabled) {
    vscode.window.showInformationMessage(
      'Ligature language support activated! Enhanced features are enabled.',
      'Show Commands',
      'Open Settings'
    ).then(selection => {
      if (selection === 'Show Commands') {
        vscode.commands.executeCommand('workbench.action.showCommands');
      } else if (selection === 'Open Settings') {
        vscode.commands.executeCommand('workbench.action.openSettings', 'ligature');
      }
    });
  }
}

// Extension deactivation
export async function deactivate(): Promise<void> {
  console.log('Ligature extension is deactivating...');
  await stopLanguageClient();
} 