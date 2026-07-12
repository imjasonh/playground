import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { describe, it } from "node:test";
import { fileURLToPath } from "node:url";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

describe("Yard Crane web export", () => {
  it("ships the Godot web runtime artifacts at the app root", () => {
    for (const name of [
      "index.html",
      "index.js",
      "index.wasm",
      "index.pck",
      "index.png",
    ]) {
      const full = path.join(root, name);
      assert.ok(fs.existsSync(full), `missing ${name}`);
      assert.ok(fs.statSync(full).size > 0, `${name} is empty`);
    }
  });

  it("uses a single-threaded shell suitable for GitHub Pages", () => {
    const html = fs.readFileSync(path.join(root, "index.html"), "utf8");
    assert.match(html, /Yard Crane/);
    assert.match(html, /index\.js/);
    // Threaded builds spawn Workers + need COOP/COEP; nothreads shells do not.
    const js = fs.readFileSync(path.join(root, "index.js"), "utf8");
    assert.equal(
      /new Worker\s*\(/.test(js),
      false,
      "export looks multithreaded; re-export with variant/thread_support=false"
    );
  });

  it("keeps Godot source next to the export", () => {
    assert.ok(fs.existsSync(path.join(root, "src", "project.godot")));
    assert.ok(fs.existsSync(path.join(root, "src", "export_presets.cfg")));
    assert.ok(fs.existsSync(path.join(root, "src", "scenes", "main.tscn")));
    const presets = fs.readFileSync(
      path.join(root, "src", "export_presets.cfg"),
      "utf8"
    );
    assert.match(presets, /variant\/thread_support=false/);
    assert.match(presets, /platform="Web"/);
  });

  it("wasm payload is present and sized like a Godot web build", () => {
    const wasm = fs.statSync(path.join(root, "index.wasm"));
    // Godot 4 web templates are tens of MB; guard against accidental empty stubs.
    assert.ok(wasm.size > 1_000_000, `index.wasm unexpectedly small (${wasm.size})`);
  });
});
