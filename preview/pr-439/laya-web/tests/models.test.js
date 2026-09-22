import test from "node:test";
import assert from "node:assert/strict";

import { pickOnnxFiles } from "../src/compile.js";
import {
  bundleUrls,
  formatBytes,
  getModel,
  hubFileUrl,
  listModels,
  parseLayaConfig,
} from "../src/models.js";
import { preferWebGpu } from "../src/webgpu.js";
import { detectWebGPU } from "../src/webgpu.js";
import { concat, fetchBundle, fetchFile, memoryCache } from "../src/fetch-bundle.js";

test("catalog lists the Laya ONNX checkpoints", () => {
  const ids = listModels().map((model) => model.id);
  assert.deepEqual(ids, ["laya-en", "laya-ml"]);
  assert.equal(getModel("laya-en").engine, "ort");
  assert.throws(() => getModel("kev-0.5b"), /Unknown model/);
});

test("hubFileUrl encodes repo paths", () => {
  assert.equal(
    hubFileUrl("receptron/laya-onnx", "main", "tokenizer/tokenizer.json"),
    "https://huggingface.co/receptron/laya-onnx/resolve/main/tokenizer/tokenizer.json",
  );
  assert.ok(bundleUrls(getModel("laya-en")).length >= 5);
});

test("formatBytes and config defaults", () => {
  assert.equal(formatBytes(0), "0 B");
  assert.match(formatBytes(1_700_000_000), /GB/);
  const config = parseLayaConfig({ max_len: 1024, temperature_by_options: { "choice:2": 1.2 } });
  assert.equal(config.max_len, 1024);
  assert.equal(config.temperature_by_options["choice:2"], 1.2);
});

test("pickOnnxFiles finds graph, weights, and tokenizer", () => {
  const picked = pickOnnxFiles({
    "laya.onnx": 1,
    "laya.onnx.data": 2,
    "laya_config.json": 3,
    "tokenizer/tokenizer.json": 4,
    "tokenizer/tokenizer_config.json": 5,
  });
  assert.equal(picked.graph, "laya.onnx");
  assert.equal(picked.weights, "laya.onnx.data");
  assert.equal(picked.tokenizer, "tokenizer/tokenizer.json");
});

test("pickOnnxFiles prefers rl_agent_config over onnx_config", () => {
  const picked = pickOnnxFiles({
    "model.onnx": 1,
    "onnx_config.json": 2,
    "rl_agent_config.json": 3,
  });
  assert.equal(picked.config, "rl_agent_config.json");
});

test("preferWebGpu follows the user's backend choice", () => {
  assert.equal(preferWebGpu("wasm", { available: true }), false);
  assert.equal(preferWebGpu("webgpu", { available: false }), true);
  assert.equal(preferWebGpu("auto", { available: true }), true);
  assert.equal(preferWebGpu("auto", { available: false }), false);
});

test("detectWebGPU reports missing navigator.gpu", async () => {
  const result = await detectWebGPU(undefined);
  assert.equal(result.available, false);
});

test("fetchFile uses the cache and reports progress", async () => {
  const cache = memoryCache();
  const url = "https://example.test/weights.bin";
  let fetches = 0;
  const fetchImpl = async () => {
    fetches += 1;
    return {
      ok: true,
      status: 200,
      statusText: "OK",
      headers: new Headers({ "content-length": "4" }),
      arrayBuffer: async () => new Uint8Array([1, 2, 3, 4]).buffer,
    };
  };
  const first = await fetchFile(url, { cache, fetchImpl });
  const second = await fetchFile(url, { cache, fetchImpl });
  assert.equal(first.byteLength, 4);
  assert.equal(second.byteLength, 4);
  assert.equal(fetches, 1);
});

test("fetchFile throws on HTTP error", async () => {
  await assert.rejects(
    () =>
      fetchFile("https://example.test/missing.bin", {
        fetchImpl: async () => ({ ok: false, status: 404, statusText: "Not Found" }),
      }),
    /failed to download/,
  );
});

test("fetchBundle throws when a model has no files", async () => {
  await assert.rejects(
    () => fetchBundle({ title: "Empty", repo: null, files: [] }),
    /no files to fetch/,
  );
});

test("concat joins streamed chunks", () => {
  const buffer = concat([new Uint8Array([1, 2]), new Uint8Array([3])], 3);
  assert.deepEqual([...new Uint8Array(buffer)], [1, 2, 3]);
});
