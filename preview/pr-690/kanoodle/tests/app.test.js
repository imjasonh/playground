/**
 * Smoke test: app.js must import all runtime dependencies.
 * A missing import causes init() to throw ReferenceError in the browser,
 * leaving the board and tray empty on GitHub Pages preview deploys.
 */
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const appSource = readFileSync(join(here, '../src/app.js'), 'utf8');

const requiredSymbols = [
  ['createGameState', './puzzle.js'],
  ['listLibraryPuzzles', './puzzleLibrary.js'],
  ['KanoodleGame', './game.js'],
];

describe('app.js module wiring', () => {
  test('imports every symbol used at runtime', () => {
    for (const [symbol, modulePath] of requiredSymbols) {
      expect(appSource).toMatch(new RegExp(`import\\s*\\{[^}]*\\b${symbol}\\b[^}]*\\}\\s*from\\s*['"]${modulePath.replace('.', '\\.')}['"]`));
    }
  });
});
