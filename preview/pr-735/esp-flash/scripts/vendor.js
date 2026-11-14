/**
 * Copy esptool-js and web-serial-polyfill into ./vendor so GitHub Pages can
 * serve the app without a bundler or npm install.
 *
 * Re-run with `npm run vendor` after bumping those packages.
 */
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const vendor = join(root, "vendor");
mkdirSync(vendor, { recursive: true });

function copyFirst(candidates, destName) {
  for (const rel of candidates) {
    const src = join(root, "node_modules", rel);
    if (existsSync(src)) {
      const dest = join(vendor, destName);
      const text = readFileSync(src, "utf8").replace(
        /\n\/\/# sourceMappingURL=.*$/,
        "",
      );
      writeFileSync(dest, text);
      console.log(`vendored ${rel} -> vendor/${destName}`);
      return dest;
    }
  }
  throw new Error(`none of ${candidates.join(", ")} exist; run npm install`);
}

copyFirst(
  ["esptool-js/bundle.js"],
  "esptool-js.js",
);

const polyfillDest = copyFirst(
  ["web-serial-polyfill/dist/serial.js"],
  "web-serial-polyfill.js",
);

const polyfill = readFileSync(polyfillDest, "utf8");
if (!polyfill.includes("export")) {
  console.warn("web-serial-polyfill.js has no ESM export; serial.js import may fail");
}
