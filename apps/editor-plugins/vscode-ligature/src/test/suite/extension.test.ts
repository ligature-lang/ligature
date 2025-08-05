import * as assert from 'assert';
import * as vscode from 'vscode';

suite('Extension Test Suite', () => {
  vscode.window.showInformationMessage('Start all tests.');

  test('Extension should be present', () => {
    assert.ok(vscode.extensions.getExtension('ligature-lang.vscode-ligature'));
  });

  test('Should activate', async () => {
    const ext = vscode.extensions.getExtension('ligature-lang.vscode-ligature');
    if (ext) {
      await ext.activate();
      assert.ok(ext.isActive);
    }
  });

  test('Should register Ligature commands', async () => {
    const commands = await vscode.commands.getCommands();
    const ligatureCommands = commands.filter(cmd => cmd.startsWith('ligature.'));
    
    assert.ok(ligatureCommands.length > 0, 'No Ligature commands found');
    assert.ok(ligatureCommands.includes('ligature.restartLanguageServer'));
    assert.ok(ligatureCommands.includes('ligature.showDiagnostics'));
    assert.ok(ligatureCommands.includes('ligature.formatDocument'));
  });

  test('Should provide Ligature language support', () => {
    const languages = vscode.languages.getLanguages();
    assert.ok(languages.includes('ligature'), 'Ligature language not registered');
  });
}); 