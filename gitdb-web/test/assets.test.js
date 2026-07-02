import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";

const read = (name) => readFile(new URL(`../${name}`, import.meta.url), "utf8");

test("app assets use preview-safe relative URLs", async () => {
  const [html, main, worker] = await Promise.all([
    read("index.html"),
    read("main.js"),
    read("worker.js"),
  ]);

  assert.match(html, /src="\.\/main\.js"/);
  assert.match(html, /href="\.\/styles\.css"/);
  assert.match(main, /new URL\("\.\/worker\.js", import\.meta\.url\)/);
  assert.match(worker, /new URL\("\.\/generated\/gitdb\.wasm\.gz"/);
  assert.match(worker, /new URL\("\.\/generated\/wasm_exec\.js"/);
  assert.match(worker, /new DecompressionStream\("gzip"\)/);
  assert.doesNotMatch(`${html}\n${main}\n${worker}`, /\/playground\//);
});

test("UI documents the backend compatibility boundary", async () => {
  const html = await read("index.html");
  assert.match(html, /go-sqlite-fdw/);
  assert.match(html, /ncruces SQLite backend/);
  assert.match(html, /modernc\.org\/sqlite/);
  assert.match(html, /id="repository-url"/);
  assert.match(html, /id="cors-proxy"/);
  assert.match(html, /id="clone-depth"/);
});
