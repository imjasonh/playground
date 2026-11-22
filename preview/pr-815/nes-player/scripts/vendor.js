/**
 * Copy the jsnes browser bundle into ./vendor so GitHub Pages can serve the
 * app without a bundler or npm install.
 *
 * Re-run with `npm run vendor` after bumping jsnes.
 */
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const vendor = join(root, "vendor");
mkdirSync(vendor, { recursive: true });

const src = join(root, "node_modules", "jsnes", "dist", "jsnes.min.js");
const text = readFileSync(src, "utf8").replace(/\n?\/\/# sourceMappingURL=.*$/, "");
writeFileSync(join(vendor, "jsnes.min.js"), `${text}\n`);
console.log("vendored jsnes/dist/jsnes.min.js -> vendor/jsnes.min.js");
