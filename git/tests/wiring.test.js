/**
 * Static wiring checks that catch breakage the pure unit tests can't:
 *   - app.js imports every symbol it uses at runtime (a missing import would
 *     throw a ReferenceError only in the browser, leaving a blank page).
 *   - every DOM id app.js looks up actually exists in index.html.
 *   - the vendored git bundles exist where gitClient.js expects them, so the
 *     deployed static site can lazy-load them.
 */
import { readFileSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const read = (rel) => readFileSync(join(root, rel), 'utf8');

const appSource = read('src/app.js');
const indexHtml = read('index.html');
const gitClientSource = read('src/gitClient.js');

describe('app.js imports', () => {
  const requiredSymbols = [
    ['buildFileTree', './fileTree.js'],
    ['flattenVisible', './fileTree.js'],
    ['fuzzyFilter', './fuzzy.js'],
    ['highlightSegments', './fuzzy.js'],
    ['parseRepoUrl', './repoUrl.js'],
    ['languageForPath', './language.js'],
    ['createDemoSource', './demoRepo.js'],
    ['formatBytes', './format.js'],
  ];

  test.each(requiredSymbols)('imports %s from %s', (symbol, modulePath) => {
    const escaped = modulePath.replace(/[.]/g, '\\$&');
    const re = new RegExp(`import[\\s\\S]*?\\b${symbol}\\b[\\s\\S]*?from\\s*['"]${escaped}['"]`);
    expect(appSource).toMatch(re);
  });
});

describe('DOM wiring', () => {
  test('every id cached by app.js exists in index.html', () => {
    const match = appSource.match(/const ids = \[([\s\S]*?)\];/);
    expect(match).not.toBeNull();
    const ids = [...match[1].matchAll(/'([^']+)'/g)].map((m) => m[1]);
    expect(ids.length).toBeGreaterThan(10);
    const missing = ids.filter((id) => !indexHtml.includes(`id="${id}"`));
    expect(missing).toEqual([]);
  });

  test('index.html loads the app entry module', () => {
    expect(indexHtml).toMatch(/<script[^>]*type="module"[^>]*src="src\/app\.js"/);
  });
});

describe('vendored bundles', () => {
  const vendorFiles = [
    'vendor/polyfills/node-globals.js',
    'vendor/lightning-fs/lightning-fs.min.js',
    'vendor/isomorphic-git/index.umd.min.js',
    'vendor/isomorphic-git/http-web.umd.js',
  ];

  test.each(vendorFiles)('%s exists', (rel) => {
    expect(existsSync(join(root, rel))).toBe(true);
  });

  test.each(vendorFiles)('gitClient.js references %s', (rel) => {
    expect(gitClientSource).toContain(rel);
  });
});
