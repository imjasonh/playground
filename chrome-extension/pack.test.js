import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import test from "node:test";
import { inflateRawSync } from "node:zlib";

const root = path.dirname(new URL(import.meta.url).pathname);
const pngSignature = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);

// pack.sh writes a zip. Read its central directory and inflate each entry.
function readZip(buffer) {
  let eocd = -1;
  const earliest = Math.max(0, buffer.length - 22 - 65535);
  for (let index = buffer.length - 22; index >= earliest; index -= 1) {
    if (buffer.readUInt32LE(index) === 0x06054b50) {
      eocd = index;
      break;
    }
  }
  assert.notEqual(eocd, -1, "zip has no end of central directory");
  const count = buffer.readUInt16LE(eocd + 10);
  let offset = buffer.readUInt32LE(eocd + 16);
  const files = new Map();
  for (let entry = 0; entry < count; entry += 1) {
    assert.equal(buffer.readUInt32LE(offset), 0x02014b50);
    const flags = buffer.readUInt16LE(offset + 8);
    const method = buffer.readUInt16LE(offset + 10);
    const compressedSize = buffer.readUInt32LE(offset + 20);
    const nameLength = buffer.readUInt16LE(offset + 28);
    const extraLength = buffer.readUInt16LE(offset + 30);
    const commentLength = buffer.readUInt16LE(offset + 32);
    const localOffset = buffer.readUInt32LE(offset + 42);
    const name = buffer.subarray(offset + 46, offset + 46 + nameLength).toString("utf8");
    assert.equal(flags & 0x08, 0, `${name} uses a data descriptor`);
    const localNameLength = buffer.readUInt16LE(localOffset + 26);
    const localExtraLength = buffer.readUInt16LE(localOffset + 28);
    const dataStart = localOffset + 30 + localNameLength + localExtraLength;
    const compressed = buffer.subarray(dataStart, dataStart + compressedSize);
    let data = compressed;
    if (method === 8) {
      data = inflateRawSync(compressed);
    } else {
      assert.equal(method, 0, `${name} uses compression method ${method}`);
    }
    files.set(name, Buffer.from(data));
    offset += 46 + nameLength + extraLength + commentLength;
  }
  return files;
}

function pngInfo(blob) {
  assert.ok(blob.subarray(0, 8).equals(pngSignature), "not a png");
  return {
    width: blob.readUInt32BE(16),
    height: blob.readUInt32BE(20),
    bitDepth: blob[24],
    color: blob[25],
  };
}

function run(command, args) {
  return new Promise((resolve, reject) => {
    execFile(command, args, { cwd: root }, (error) => {
      if (error) {
        reject(error);
        return;
      }
      resolve();
    });
  });
}

test("the store zip is the extension package and the listing images match the store sizes", async (t) => {
  const dir = await mkdtemp(path.join(tmpdir(), "chrome-extension-pack-"));
  t.after(() => rm(dir, { recursive: true, force: true }));
  const zipPath = path.join(dir, "chrome-extension.zip");
  await run("bash", ["pack.sh", zipPath]);
  const files = readZip(await readFile(zipPath));
  const names = [...files.keys()].sort();
  assert.deepEqual(names, [
    "background.js",
    "base64.js",
    "clipboard.js",
    "controller.js",
    "duplicates.js",
    "icons/128.png",
    "icons/16.png",
    "icons/32.png",
    "icons/48.png",
    "manifest.json",
    "offscreen.html",
    "offscreen.js",
    "selection.js",
  ]);

  const manifest = JSON.parse(files.get("manifest.json").toString("utf8"));
  assert.equal(manifest.manifest_version, 3);
  assert.equal(manifest.version, "0.1.3");
  assert.equal(manifest.name, "Close Duplicate Tabs");
  assert.ok(manifest.description.length <= 132);
  assert.match(manifest.description, /badge/);
  assert.match(manifest.description, /URL/);
  assert.match(manifest.description, /base64/);
  assert.deepEqual(manifest.permissions, ["clipboardWrite", "contextMenus", "offscreen", "tabs"]);
  assert.equal("host_permissions" in manifest, false);
  assert.equal("optional_permissions" in manifest, false);
  assert.equal(manifest.content_scripts.length, 1);
  assert.deepEqual(manifest.content_scripts[0].matches, ["http://*/*", "https://*/*"]);
  assert.deepEqual(manifest.content_scripts[0].js, ["selection.js"]);
  assert.equal(manifest.content_scripts[0].all_frames, true);
  assert.equal(manifest.content_scripts[0].run_at, "document_start");
  assert.equal("default_popup" in manifest.action, false);
  assert.equal(manifest.background.service_worker, "background.js");
  assert.equal(manifest.background.type, "module");

  const background = files.get("background.js").toString("utf8");
  assert.match(background, /start\(chrome\)/);
  assert.equal(background.includes("onClicked"), false);

  for (const size of [16, 32, 48, 128]) {
    const info = pngInfo(files.get(`icons/${size}.png`));
    assert.deepEqual([info.width, info.height], [size, size]);
  }

  const icon = pngInfo(await readFile(path.join(root, "store/icon-128.png")));
  assert.deepEqual([icon.width, icon.height, icon.bitDepth, icon.color], [128, 128, 8, 6]);
  for (const name of ["store/screenshot.png", "store/screenshot-closed.png"]) {
    const shot = pngInfo(await readFile(path.join(root, name)));
    assert.deepEqual([shot.width, shot.height, shot.bitDepth, shot.color], [1280, 800, 8, 2]);
  }
});
