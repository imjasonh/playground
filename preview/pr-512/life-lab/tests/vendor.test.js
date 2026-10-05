// Guard against missing vendored files: every relative import inside a
// vendored module must itself be vendored (three's module build re-exports
// from ./three.core.min.js, which is easy to forget).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, existsSync, readdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const vendor = fileURLToPath(new URL('../vendor', import.meta.url));

function relativeImports(source) {
  const specs = new Set();
  const patterns = [
    /from\s*["'](\.{1,2}\/[^"']+)["']/g,
    /import\s*["'](\.{1,2}\/[^"']+)["']/g,
    /import\(\s*["'](\.{1,2}\/[^"']+)["']\s*\)/g,
  ];
  for (const re of patterns) {
    for (const m of source.matchAll(re)) specs.add(m[1]);
  }
  return [...specs];
}

test('all relative imports of vendored modules resolve', () => {
  const stack = [vendor];
  const jsFiles = [];
  while (stack.length) {
    const dir = stack.pop();
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const p = join(dir, entry.name);
      if (entry.isDirectory()) stack.push(p);
      else if (entry.name.endsWith('.js')) jsFiles.push(p);
    }
  }
  assert.ok(jsFiles.length >= 3, 'expected vendored JS modules');
  for (const file of jsFiles) {
    for (const spec of relativeImports(readFileSync(file, 'utf8'))) {
      const target = join(dirname(file), spec);
      assert.ok(existsSync(target), `${file} imports missing ${spec}`);
    }
  }
});

test('app entry imports resolve against the repo tree', () => {
  const appDir = fileURLToPath(new URL('..', import.meta.url));
  const app = readFileSync(join(appDir, 'src/app.js'), 'utf8');
  for (const spec of relativeImports(app)) {
    const target = join(appDir, 'src', spec);
    assert.ok(existsSync(target), `src/app.js imports missing ${spec}`);
  }
});
