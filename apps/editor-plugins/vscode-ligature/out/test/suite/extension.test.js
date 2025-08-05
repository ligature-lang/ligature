"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
const assert = __importStar(require("assert"));
const vscode = __importStar(require("vscode"));
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
//# sourceMappingURL=extension.test.js.map