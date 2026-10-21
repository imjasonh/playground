import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const vendor = fileURLToPath(new URL("../vendor", import.meta.url));

test("vendored esptool-js and web-serial-polyfill are present ESM files", () => {
  const esptool = `${vendor}/esptool-js.js`;
  const polyfill = `${vendor}/web-serial-polyfill.js`;
  assert.ok(existsSync(esptool), "vendor/esptool-js.js missing; run npm run vendor");
  assert.ok(existsSync(polyfill), "vendor/web-serial-polyfill.js missing; run npm run vendor");
  const esptoolSrc = readFileSync(esptool, "utf8");
  assert.match(esptoolSrc, /export\{/);
  assert.match(esptoolSrc, /ESPLoader/);
  const polyfillSrc = readFileSync(polyfill, "utf8");
  assert.match(polyfillSrc, /export const serial/);
});

test("vendored bundles export the constructors the flasher imports", async () => {
  const esptool = await import("../vendor/esptool-js.js");
  assert.equal(typeof esptool.ESPLoader, "function");
  assert.equal(typeof esptool.Transport, "function");
  const polyfill = await import("../vendor/web-serial-polyfill.js");
  assert.equal(typeof polyfill.serial.requestPort, "function");
});
