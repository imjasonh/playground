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
for (const name of ['three.module.min.js', 'three.core.min.js']) {
  copyFileSync(join(build, name), join(vendor, name));
  console.log(`vendored ${name}`); // pasta:ignore console_noise
}
