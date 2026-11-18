/**
 * Copy the ES module builds of marked and DOMPurify into ./vendor so GitHub
 * Pages can serve the app without a bundler or npm install.
 *
 * Re-run with `npm run vendor` after bumping either package.
 */
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {dirname, join} from 'node:path';
import {fileURLToPath} from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const vendor = join(root, 'vendor');
mkdirSync(vendor, {recursive: true});

const files = [
  ['marked/lib/marked.esm.js', 'marked.esm.js'],
  ['dompurify/dist/purify.es.mjs', 'purify.es.mjs'],
];

for (const [from, to] of files) {
  const text = readFileSync(join(root, 'node_modules', from), 'utf8').replace(
    /\n*\/\/# sourceMappingURL=.*\s*$/,
    '',
  );
  writeFileSync(join(vendor, to), `${text}\n`);
  console.log(`vendored ${from} -> vendor/${to}`);
}
