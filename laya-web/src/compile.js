import { ORT_CDN, parseLayaConfig } from "./models.js";
import { jsonFromBuffer } from "./fetch-bundle.js";
import { createWordPieceTokenizer, kevSpecialIdsFromBundle } from "./tokenizer.js";
import { preferWebGpu } from "./webgpu.js";

export async function loadOrt(importOrt) {
  if (importOrt) {
    return importOrt();
  }
  const mod = await import(`${ORT_CDN}ort.webgpu.min.mjs`);
  const ort = mod.default ?? mod;
  if (ort.env?.wasm) {
    ort.env.wasm.wasmPaths = ORT_CDN;
  }
  return ort;
}

export function pickOnnxFiles(files) {
  const names = Object.keys(files);
  const graph =
    names.find((name) => name.endsWith(".onnx") && !name.endsWith(".onnx.data")) ??
    names.find((name) => name.endsWith(".onnx"));
  const weights = names.find((name) => name.endsWith(".onnx.data"));
  const config =
    names.find((name) => name.endsWith("laya_config.json")) ??
    names.find((name) => name.endsWith("rl_agent_config.json")) ??
    names.find((name) => name.endsWith("onnx_config.json"));
  const tokenizer = names.find((name) => name.endsWith("tokenizer.json"));
  const tokenizerConfig = names.find((name) => name.endsWith("tokenizer_config.json"));
  return { graph, weights, config, tokenizer, tokenizerConfig };
}

export async function compileModel({
  model,
  files = {},
  backendChoice = "auto",
  detected,
  importOrt,
} = {}) {
  const started = now();
  const wantGpu = preferWebGpu(backendChoice, detected);
  const picked = pickOnnxFiles(files);
  if (!picked.graph) {
    throw new Error(
      `${model?.title ?? "This checkpoint"} has no ONNX graph to compile.`,
    );
  }
  const ort = await loadOrt(importOrt);
  const providers = wantGpu ? ["webgpu", "wasm"] : ["wasm"];
  const sessionOptions = {
    executionProviders: providers,
    graphOptimizationLevel: model.webgpuGraphOpt ?? "basic",
  };
  if (picked.weights && files[picked.weights]) {
    sessionOptions.externalData = [
      { path: picked.weights.split("/").pop(), data: files[picked.weights] },
    ];
  }
  const onnxSession = await ort.InferenceSession.create(files[picked.graph], sessionOptions);
  const backend = inferOrtBackend(onnxSession, wantGpu);
  const config = parseLayaConfig(picked.config ? jsonFromBuffer(files[picked.config]) : null);
  const tokenizer = picked.tokenizer
    ? createWordPieceTokenizer(
        jsonFromBuffer(files[picked.tokenizer]),
        picked.tokenizerConfig ? jsonFromBuffer(files[picked.tokenizerConfig]) : {},
      )
    : null;
  const session = createOrtSession(ort, onnxSession, backend);
  return {
    session,
    tokenizer,
    kevSpecialIds: kevSpecialIdsFromBundle(parsedJsonFiles(files)),
    config,
    backend,
    compileMs: now() - started,
  };
}

export function inferOrtBackend(session, wantedGpu) {
  const providers = session.sessionOptions?.executionProviders;
  if (Array.isArray(providers) && providers.some((p) => String(p).includes("webgpu"))) {
    return "webgpu";
  }
  return wantedGpu ? "webgpu" : "wasm";
}

export function createOrtSession(ort, session, backend) {
  return {
    backend,
    engine: "ort",
    async runKev() {
      throw new Error("This ONNX session is a Laya graph. Kev needs a Kev ONNX export.");
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

function parsedJsonFiles(files) {
  const parsed = {};
  for (const [name, buffer] of Object.entries(files)) {
    if (typeof name === "string" && name.endsWith(".json")) {
      parsed[name] = jsonFromBuffer(buffer);
    }
  }
  return parsed;
}

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}
