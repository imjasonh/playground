#!/usr/bin/env node

import {
  copyFileSync,
  mkdirSync,
  readFileSync,
  writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "..");
const packageRoot = join(root, "node_modules", "@seydx", "jsmpeg");
const vendorRoot = join(root, "vendor");
const packageJson = JSON.parse(
  readFileSync(join(packageRoot, "package.json"), "utf8"),
);

mkdirSync(vendorRoot, { recursive: true });
copyFileSync(join(packageRoot, "lib", "index.js"), join(vendorRoot, "jsmpeg.min.js"));
copyFileSync(join(packageRoot, "LICENSE"), join(vendorRoot, "JSMpeg-LICENSE.txt"));
writeFileSync(
  join(vendorRoot, "manifest.json"),
  `${JSON.stringify(
    {
      package: "@seydx/jsmpeg",
      version: packageJson.version,
      upstream: "https://github.com/phoboslab/jsmpeg",
      generatedBy: "npm run vendor",
    },
    null,
    2,
  )}\n`,
);

const bytes = readFileSync(join(vendorRoot, "jsmpeg.min.js")).byteLength;
console.log(
  `Vendored JSMpeg ${packageJson.version} (${Math.round(bytes / 1024)} KiB).`,
);
