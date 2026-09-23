/**
 * In-process Laya. Loads the ONNX graph with onnxruntime-node and answers
 * System One questions through the same packer as laya-web.
 */
import { existsSync } from "node:fs";
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseLayaConfig } from "../../laya-web/src/models.js";
import { systemOne } from "../../laya-web/src/systemone.js";
import { createWordPieceTokenizer } from "../../laya-web/src/tokenizer.js";

const DEFAULT_CACHE = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", ".laya-cache");

let cached = null;

export function defaultLayaDir() {
  return process.env.LAYA_MODEL_DIR || DEFAULT_CACHE;
}

export function layaBundleReady(dir = defaultLayaDir()) {
  return existsSync(path.join(dir, "model.onnx")) && existsSync(path.join(dir, "tokenizer", "tokenizer.json"));
}

export async function loadLayaOrt(options = {}) {
  if (cached && !options.force) {
    return cached;
  }
  const dir = options.modelDir ?? defaultLayaDir();
  const graphPath = path.join(dir, "model.onnx");
  const tokenizerPath = path.join(dir, "tokenizer", "tokenizer.json");
  const tokenizerConfigPath = path.join(dir, "tokenizer", "tokenizer_config.json");
  const configPath = path.join(dir, "rl_agent_config.json");
  await fs.access(graphPath);
  await fs.access(tokenizerPath);

  const ort = await import("onnxruntime-node");
  const session = await ort.InferenceSession.create(graphPath, {
    executionProviders: options.executionProviders ?? ["cpu"],
    intraOpNumThreads: options.threads ?? 4,
  });
  const tokenizerJson = JSON.parse(await fs.readFile(tokenizerPath, "utf8"));
  const tokenizerConfig = JSON.parse(await fs.readFile(tokenizerConfigPath, "utf8"));
  const rawConfig = JSON.parse(await fs.readFile(configPath, "utf8"));
  const tokenizer = createWordPieceTokenizer(tokenizerJson, tokenizerConfig);
  const config = parseLayaConfig(rawConfig);
  const wrapped = createCpuSession(ort, session);
  const model = options.modelName ?? "laya-multilingual-int8";

  cached = {
    model,
    backend: "laya",
    dir,
    config,
    async ask(state, questions) {
      const result = await systemOne({
        session: wrapped,
        family: "laya",
        encode: (text) => tokenizer.encode(text),
        specialIds: tokenizer.ids,
        config,
        state,
        questions,
      });
      return {
        ...result,
        model,
        backend: "laya",
      };
    },
    async close() {
      await wrapped.release();
      cached = null;
    },
  };
  return cached;
}

export async function askLayaOrt(state, questions, options = {}) {
  const runtime = options.runtime ?? (await loadLayaOrt(options));
  return runtime.ask(state, questions);
}

export function resetLayaOrt() {
  cached = null;
}

function createCpuSession(ort, session) {
  return {
    backend: "cpu",
    engine: "ort",
    async runKev() {
      throw new Error("This ONNX session is a Laya graph.");
    },
    async runLaya(batch) {
      const feeds = {
        input_ids: new ort.Tensor("int64", batch.inputIds, [batch.n, batch.length]),
        attention_mask: new ort.Tensor("int64", batch.attention, [batch.n, batch.length]),
        marker_pos: new ort.Tensor("int64", batch.markerPos, [batch.n, batch.maxOptions]),
        marker_mask: new ort.Tensor("bool", batch.markerMask, [batch.n, batch.maxOptions]),
        qtype: new ort.Tensor("int64", batch.qtype, [batch.n]),
      };
      const out = await session.run(feeds);
      const logits = asFloat32(out.logits);
      const action = asFloat32(out.act_probs ?? out.act_logits);
      const actionWidth = Math.max(1, Math.floor(action.length / batch.n));
      const rows = [];
      for (let row = 0; row < batch.n; row += 1) {
        const start = row * batch.maxOptions;
        rows.push({
          logits: logits.subarray(start, start + batch.maxOptions),
          action: action.subarray(row * actionWidth, (row + 1) * actionWidth),
        });
      }
      return rows;
    },
    async release() {
      await session.release();
    },
  };
}

function asFloat32(tensor) {
  if (!tensor) {
    return new Float32Array([1, 0]);
  }
  const data = tensor.data;
  return data instanceof Float32Array ? data : Float32Array.from(data);
}
