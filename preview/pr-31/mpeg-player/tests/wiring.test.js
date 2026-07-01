import test from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { findTransportStreamOffset } from "../src/media.js";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "..");
const read = (path) => readFileSync(join(root, path), "utf8");

const html = read("index.html");
const app = read("src/app.js");
const controller = read("src/player-controller.js");
const worker = read("src/decoder-worker.js");
const worklet = read("src/audio-worklet.js");

test("every DOM id cached by app.js exists", () => {
  const match = app.match(/const DOM_IDS = \[([\s\S]*?)\];/);
  assert.ok(match);
  const ids = [...match[1].matchAll(/"([^"]+)"/g)].map((entry) => entry[1]);
  assert.ok(ids.length > 20);
  assert.deepEqual(
    ids.filter((id) => !html.includes(`id="${id}"`)),
    [],
  );
});

test("the page loads the module entry point", () => {
  assert.match(html, /<script type="module" src="src\/app\.js"><\/script>/);
});

test("worker and worklet paths are wired from the controller", () => {
  assert.match(controller, /new URL\("\.\/decoder-worker\.js", import\.meta\.url\)/);
  assert.match(controller, /new URL\("\.\/audio-worklet\.js", import\.meta\.url\)/);
  assert.match(controller, /new MessageChannel\(\)/);
});

test("the decoder imports the vendored WASM build and uses OffscreenCanvas", () => {
  assert.match(worker, /importScripts\("\.\.\/vendor\/jsmpeg\.min\.js"\)/);
  assert.match(worker, /JSMpeg\.Decoder|new JSMpeg\.Player/);
  assert.match(worker, /OffscreenCanvas/);
  assert.ok(existsSync(join(root, "vendor", "jsmpeg.min.js")));
  assert.ok(existsSync(join(root, "vendor", "JSMpeg-LICENSE.txt")));
});

test("PCM moves directly over a MessagePort into the AudioWorklet", () => {
  assert.match(worker, /audioPort\?\.postMessage/);
  assert.match(worklet, /data\?\.type === "attach"/);
  assert.match(worklet, /registerProcessor\("mpeg-pcm-output"/);
});

test("the demo fixture is a real MPEG transport stream", () => {
  const demo = readFileSync(join(root, "assets", "demo.ts"));
  assert.equal(findTransportStreamOffset(demo), 0);
  assert.equal(demo.byteLength % 188, 0);
});
