#!/usr/bin/env node
/**
 * Copy three.js browser ESM builds into ./vendor so the app deploys with no
 * package CDN. Re-run with `npm run vendor` after bumping three in package.json.
 */
import { copyFileSync, mkdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const build = join(root, 'node_modules', 'three', 'build');
const vendor = join(root, 'vendor');

mkdirSync(vendor, { recursive: true });
for (const [fromName, toName] of [
  ['three.module.js', 'three.module.min.js'],
  ['three.core.js', 'three.core.min.js'],
  ['three.core.js', 'three.core.js'],
]) {
  copyFileSync(join(build, fromName), join(vendor, toName));
  console.log(`vendored ${toName}`);
}
