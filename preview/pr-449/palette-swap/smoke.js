"use strict";

const fs = require("fs");
const path = require("path");

require("./wasm/wasm_exec.js");

function same(a, b) {
  if (a.length !== b.length) {
    return false;
  }
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) {
      return false;
    }
  }
  return true;
}

async function main() {
  const go = new globalThis.Go();
  const bytes = fs.readFileSync(path.join(__dirname, "wasm", "palette.wasm"));
  const compiled = await WebAssembly.instantiate(bytes, go.importObject);
  go.run(compiled.instance);
  const api = globalThis.paletteSwap;
  if (!api) {
    throw new Error("paletteSwap was not registered");
  }
  if (api.lanes !== 4) {
    throw new Error("expected 4 lanes on wasm, got " + api.lanes);
  }
  if (api.emulated) {
    throw new Error("wasm simd is emulated");
  }

  const width = 20;
  const height = 13;
  const rgba = new Uint8Array(width * height * 4);
  for (let i = 0; i < width * height; i++) {
    rgba[i * 4] = (i * 17) % 256;
    rgba[i * 4 + 1] = (i * 29) % 256;
    rgba[i * 4 + 2] = (i * 53) % 256;
    rgba[i * 4 + 3] = 255;
  }
  const loaded = api.load(rgba);
  if (loaded.error) {
    throw new Error(loaded.error);
  }
  if (loaded.pixels !== width * height) {
    throw new Error("pixel count " + loaded.pixels);
  }

  const list = api.list();
  const want = { grey: 16, nes: 54, perler: 103, floss: 456 };
  if (list.length !== 4) {
    throw new Error("palette count " + list.length);
  }
  for (const item of list) {
    if (item.count !== want[item.id]) {
      throw new Error(item.id + " count " + item.count);
    }
    const outs = [];
    for (const which of ["scalar", "portable", "arch"]) {
      const indices = new Uint8Array(width * height * 2);
      const stat = api.run(item.id, which, indices);
      if (stat.error) {
        throw new Error(which + " " + stat.error);
      }
      outs.push(indices);
    }
    if (!same(outs[0], outs[1]) || !same(outs[0], outs[2])) {
      throw new Error("index mismatch on " + item.id);
    }
  }

  const bench = api.bench("floss", "portable", 30);
  if (bench.error) {
    throw new Error(bench.error);
  }
  if (bench.iters < 1 || bench.ms <= 0) {
    throw new Error("benchmark did not record a run");
  }
  console.log(
    "smoke ok lanes=" + api.lanes + " floss portable " + bench.ms.toFixed(1) + " ms over " + bench.iters + " iters",
  );
  process.exit(0);
}

main().catch(function (err) {
  console.error(err);
  process.exit(1);
});
