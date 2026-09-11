#!/usr/bin/env node
/**
 * Prepare the static, no-CDN runtime assets under ./vendor so the deployed app
 * has no runtime dependency on a package CDN. Re-run with `npm run vendor`
 * after bumping versions in package.json.
 *
 * Outputs (each registers a browser global, loaded in this order):
 *   - vendor/polyfills/node-globals.js       -> globalThis.Buffer + process shim
 *   - vendor/lightning-fs/lightning-fs.min.js-> window.LightningFS
 *   - vendor/isomorphic-git/index.umd.min.js -> window.git
 *   - vendor/isomorphic-git/http-web.umd.js  -> window.GitHttp
 *
 * The isomorphic-git UMD bundle expects Node's `Buffer` and `process` globals,
 * so we bundle a tiny shim (the npm `buffer` package + a minimal process) with
 * esbuild and load it first.
 */
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { copyFileSync, mkdirSync, readFileSync } from 'node:fs';
import { build } from 'esbuild';

const here = dirname(fileURLToPath(import.meta.url));
const appRoot = join(here, '..');
const modules = join(appRoot, 'node_modules');

function pkgVersion(name) {
  return JSON.parse(readFileSync(join(modules, name, 'package.json'), 'utf8')).version;
}

function rel(p) {
  return p.replace(`${appRoot}/`, '');
}

function report(to) {
  const bytes = readFileSync(to).length;
  console.log(`vendored ${rel(to)} (${(bytes / 1024).toFixed(0)} KiB)`);
}

const isoRoot = join(modules, 'isomorphic-git');
const lfsRoot = join(modules, '@isomorphic-git', 'lightning-fs');

const copies = [
  {
    from: join(isoRoot, 'index.umd.min.js'),
    to: join(appRoot, 'vendor', 'isomorphic-git', 'index.umd.min.js'),
  },
  {
    from: join(isoRoot, 'http', 'web', 'index.umd.js'),
    to: join(appRoot, 'vendor', 'isomorphic-git', 'http-web.umd.js'),
  },
  {
    from: join(lfsRoot, 'dist', 'lightning-fs.min.js'),
    to: join(appRoot, 'vendor', 'lightning-fs', 'lightning-fs.min.js'),
  },
];

for (const { from, to } of copies) {
  mkdirSync(dirname(to), { recursive: true });
  copyFileSync(from, to);
  report(to);
}

// Bundle the Buffer + process globals the isomorphic-git UMD relies on.
const polyfillSource = `
import { Buffer } from 'buffer';
if (typeof globalThis.Buffer === 'undefined') globalThis.Buffer = Buffer;
if (typeof globalThis.process === 'undefined') {
  globalThis.process = {
    env: {},
    argv: [],
    platform: '',
    browser: true,
    version: '',
    versions: {},
    nextTick: (fn, ...args) => queueMicrotask(() => fn(...args)),
    cwd: () => '/',
    domain: null,
  };
}
`;

const polyfillOut = join(appRoot, 'vendor', 'polyfills', 'node-globals.js');
mkdirSync(dirname(polyfillOut), { recursive: true });
await build({
  stdin: { contents: polyfillSource, resolveDir: appRoot, loader: 'js' },
  outfile: polyfillOut,
  bundle: true,
  format: 'iife',
  platform: 'browser',
  minify: true,
  legalComments: 'none',
});
report(polyfillOut);

const manifest = {
  generatedBy: 'npm run vendor',
  isomorphicGit: pkgVersion('isomorphic-git'),
  lightningFs: pkgVersion('@isomorphic-git/lightning-fs'),
  buffer: pkgVersion('buffer'),
};
console.log('versions:', JSON.stringify(manifest));
