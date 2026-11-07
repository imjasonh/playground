/**
 * Bundle Marp Core into vendor/marp.js so GitHub Pages can serve the app
 * without a bundler or npm install.
 *
 * Math is left out: KaTeX loads its fonts from a CDN and MathJax is 1.7 MB.
 * highlight.js keeps the languages in KEEP_LANGUAGES; a fence in any other
 * language renders as plain text.
 *
 * Re-run with `npm run vendor` after bumping @marp-team/marp-core.
 */
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {dirname, join} from 'node:path';
import {fileURLToPath} from 'node:url';

import {build} from 'esbuild';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');

const KEEP_LANGUAGES = new Set([
  'bash',
  'c',
  'cpp',
  'csharp',
  'css',
  'diff',
  'dockerfile',
  'go',
  'graphql',
  'http',
  'ini',
  'java',
  'javascript',
  'json',
  'kotlin',
  'lua',
  'makefile',
  'markdown',
  'plaintext',
  'protobuf',
  'python',
  'ruby',
  'rust',
  'scss',
  'shell',
  'sql',
  'swift',
  'typescript',
  'xml',
  'yaml',
]);

const stubs = {
  name: 'marptalk-stubs',
  setup(b) {
    b.onResolve({filter: /^(mathjax-full|katex)(\/|$)/}, (args) => ({
      path: args.path,
      namespace: 'stub-math',
    }));
    b.onLoad({filter: /.*/, namespace: 'stub-math'}, (args) => ({
      contents: args.path.endsWith('package.json')
        ? 'module.exports = {version: "0.0.0"};'
        : 'module.exports = {};',
      loader: 'js',
    }));
    b.onResolve({filter: /^highlight\.js\/lib\/languages\//}, (args) => {
      const lang = args.path.split('/').pop().replace(/\.js$/, '');
      if (KEEP_LANGUAGES.has(lang)) return undefined;
      return {path: lang, namespace: 'stub-hljs'};
    });
    b.onLoad({filter: /.*/, namespace: 'stub-hljs'}, () => ({
      contents: 'module.exports = () => ({contains: []});',
      loader: 'js',
    }));
  },
};

const version = JSON.parse(
  readFileSync(
    join(root, 'node_modules/@marp-team/marp-core/package.json'),
    'utf8',
  ),
).version;

const bundles = [
  ['@marp-team/marp-core', 'Marp', 'marp.js'],
  ['@marp-team/marp-core/browser', 'browser', 'marp-browser.js'],
];

mkdirSync(join(root, 'vendor'), {recursive: true});
for (const [entry, name, file] of bundles) {
  const result = await build({
    stdin: {contents: `export {${name}} from '${entry}';`, resolveDir: root},
    bundle: true,
    format: 'esm',
    platform: 'browser',
    target: 'es2022',
    minify: true,
    legalComments: 'none',
    write: false,
    plugins: [stubs],
  });
  const banner =
    `/* ${entry} ${version} (MIT), bundled by ` +
    'marptalk/scripts/vendor.js. Do not edit. */\n';
  const text = result.outputFiles[0].text;
  writeFileSync(join(root, 'vendor', file), banner + text);
  console.log(`vendored ${entry} ${version} -> vendor/${file}`);
}
