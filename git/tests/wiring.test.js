/**
 * Static wiring checks that catch breakage the pure unit tests can't:
 *   - the app modules import every symbol they use at runtime (a missing import
 *     would throw a ReferenceError only in the browser, leaving a blank page).
 *   - every DOM id the controller looks up actually exists in index.html.
 *   - the entry module boots the controller.
 *   - the vendored git bundles exist where gitClient.js expects them, so the
 *     deployed static site can lazy-load them.
 */
import { readFileSync, existsSync, readdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join, basename } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const read = (rel) => readFileSync(join(root, rel), 'utf8');

const indexHtml = read('index.html');
const appSource = read('src/app.js');
const controllerSource = read('src/controller.js');
const gitClientSource = read('src/gitClient.js');
const searchClientSource = read('src/searchClient.js');
const contentSearchClientSource = read('src/contentSearchClient.js');

/** Every .js file under src/, recursively. */
function srcFiles() {
  return readdirSync(join(root, 'src'), { recursive: true })
    .map(String)
    .filter((p) => p.endsWith('.js'))
    .map((p) => join('src', p));
}

/**
 * Collect (importedSymbol, moduleBasename) pairs across all source files, so
 * the check is agnostic to whether a module imports via './' or '../'.
 */
function collectImports() {
  const pairs = new Set();
  const importRe =
    /import\s+(?:([A-Za-z_$][\w$]*)\s*,\s*)?(?:\{([^}]*)\})?\s*from\s*['"]([^'"]+)['"]/g;
  for (const rel of srcFiles()) {
    const source = read(rel);
    for (const match of source.matchAll(importRe)) {
      const mod = basename(match[3]);
      if (match[1]) pairs.add(`${match[1]}@${mod}`); // default import
      const named = match[2] || '';
      for (const raw of named.split(',')) {
        const name = raw.trim().split(/\s+as\s+/)[0].trim();
        if (name) pairs.add(`${name}@${mod}`);
      }
    }
  }
  return pairs;
}

describe('module imports', () => {
  const imports = collectImports();
  const requiredSymbols = [
    ['buildFileTree', 'fileTree.js'],
    ['flattenVisible', 'fileTree.js'],
    ['buildIndex', 'fuzzy.js'],
    ['fuzzyFilterIndex', 'fuzzy.js'],
    ['highlightSegments', 'fuzzy.js'],
    ['createSearchClient', 'searchClient.js'],
    ['createContentSearchClient', 'contentSearchClient.js'],
    ['createContentSearch', 'contentSearch.js'],
    ['buildPattern', 'contentSearch.js'],
    ['searchContent', 'contentSearch.js'],
    ['parseRepoUrl', 'repoUrl.js'],
    ['fileWebUrl', 'hostUrl.js'],
    ['parseLfsPointer', 'lfs.js'],
    ['renderMarkdown', 'markdown.js'],
    ['classifyGitMode', 'specialEntry.js'],
    ['parseGitmodules', 'specialEntry.js'],
    ['symlinkTarget', 'specialEntry.js'],
    ['blameLines', 'blame.js'],
    ['languageForPath', 'language.js'],
    ['createDemoSource', 'demoRepo.js'],
    ['formatBytes', 'format.js'],
    ['createStore', 'store.js'],
    ['createLoadController', 'store.js'],
    ['capabilitiesOf', 'repoSource.js'],
    ['normalizeRef', 'repoSource.js'],
    ['refValue', 'repoSource.js'],
    ['diffLines', 'diff.js'],
    ['cloneErrorMessage', 'cloneError.js'],
    ['storageEstimate', 'quota.js'],
    ['rememberToken', 'auth.js'],
    ['makeOnAuth', 'auth.js'],
    ['parseHash', 'hashState.js'],
    ['encodeHashState', 'hashState.js'],
    ['highlight', 'highlightCode.js'],
    ['grammarForPath', 'highlightCode.js'],
    ['withinHighlightBudget', 'highlightCode.js'],
  ];

  test.each(requiredSymbols)('some module imports %s from %s', (symbol, mod) => {
    expect(imports.has(`${symbol}@${mod}`)).toBe(true);
  });
});

describe('entry / module layout', () => {
  const expectedFiles = [
    'src/controller.js',
    'src/store.js',
    'src/searchClient.js',
    'src/searchWorker.js',
    'src/contentSearchClient.js',
    'src/contentSearchWorker.js',
    'src/contentSearch.js',
    'src/ui/dom.js',
    'src/ui/viewer.js',
    'src/ui/tree.js',
    'src/ui/palette.js',
    'src/ui/contentSearch.js',
    'src/ui/history.js',
    'src/ui/recent.js',
    'src/ui/highlight.js',
    'src/ui/virtualList.js',
    'src/lfs.js',
    'src/hostUrl.js',
    'src/markdown.js',
    'src/specialEntry.js',
    'src/blame.js',
  ];

  test.each(expectedFiles)('%s exists', (rel) => {
    expect(existsSync(join(root, rel))).toBe(true);
  });

  test('the entry module boots the controller', () => {
    expect(appSource).toMatch(/import\s*\{\s*init\s*\}\s*from\s*['"]\.\/controller\.js['"]/);
    expect(appSource).toMatch(/\binit\b/);
  });
});

describe('DOM wiring', () => {
  test('every id the controller caches exists in index.html', () => {
    const match = controllerSource.match(/const DOM_IDS = \[([\s\S]*?)\];/);
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

describe('worker references', () => {
  // Workers are spawned via `new URL('./xWorker.js', import.meta.url)`, not an
  // import, so collectImports() can't see them. Guard the filename so renaming a
  // worker can't silently break the browser while every unit test still passes.
  test('searchClient references its worker', () => {
    expect(searchClientSource).toContain('searchWorker.js');
  });

  test('contentSearchClient references its worker', () => {
    expect(contentSearchClientSource).toContain('contentSearchWorker.js');
  });
});
