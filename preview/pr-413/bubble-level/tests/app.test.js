/**
 * Smoke test: app.js must import every runtime symbol it uses from level.js.
 * A missing import throws at module load in the browser, leaving the level
 * frozen on the deployed page.
 */
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const appSource = readFileSync(join(here, '../src/app.js'), 'utf8');
const indexSource = readFileSync(join(here, '../index.html'), 'utf8');

const requiredSymbols = [
  'applyCalibration',
  'axisOffsets',
  'bubbleOffset',
  'clamp',
  'isLevel',
  'tiltComponents',
];

describe('app.js module wiring', () => {
  test('imports every symbol used at runtime from ./level.js', () => {
    for (const symbol of requiredSymbols) {
      expect(appSource).toMatch(
        new RegExp(`import[\\s\\S]*\\b${symbol}\\b[\\s\\S]*from\\s*['"]\\./level\\.js['"]`),
      );
    }
  });

  test('index.html loads the app as an ES module', () => {
    expect(indexSource).toMatch(/<script[^>]*type="module"[^>]*src="src\/app\.js"/);
  });
});
