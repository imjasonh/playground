// Copy the pako ESM build into vendor/ so the browser app loads it without a
// bundler. Run via `npm run vendor` after `npm install`.

import { copyFileSync, mkdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "..");

const sources = [
  {
    from: join(root, "node_modules", "pako", "dist", "pako.esm.mjs"),
    to: join(root, "vendor", "pako", "pako.esm.mjs"),
  },
];

for (const { from, to } of sources) {
  mkdirSync(dirname(to), { recursive: true });
  copyFileSync(from, to);
  console.log(`vendored ${to}`);
}
