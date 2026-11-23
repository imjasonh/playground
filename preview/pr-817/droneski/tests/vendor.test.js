// Guard against missing vendored files: three.module.min.js re-exports from
// ./three.core.min.js, which is easy to forget when bumping three.
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

test('vendored three.js modules are present', () => {
  assert.ok(existsSync(join(vendor, 'three.module.min.js')));
  assert.ok(existsSync(join(vendor, 'three.core.min.js')));
});

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
  assert.ok(jsFiles.length >= 2, 'expected vendored JS modules');
  for (const file of jsFiles) {
    for (const spec of relativeImports(readFileSync(file, 'utf8'))) {
      const target = join(dirname(file), spec);
      assert.ok(existsSync(target), `${file} imports missing ${spec}`);
    }
  }
});
