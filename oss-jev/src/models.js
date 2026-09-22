/** Published Laya / Kev bundles the tab can fetch and compile. */

export const CACHE_NAME = "oss-jev-v1";

export const ORT_VERSION = "1.23.0";

export const ORT_CDN = `https://cdn.jsdelivr.net/npm/onnxruntime-web@${ORT_VERSION}/dist/`;

export const MODELS = {
  fixture: {
    id: "fixture",
    title: "Fixture",
    family: "laya",
    engine: "fixture",
    runnable: true,
    bytes: 0,
    description:
      "Bundled WebGPU kernel. Scores each option by token overlap with the state so the compile path works without a Hub download.",
    files: [],
  },
  "laya-en": {
    id: "laya-en",
    title: "Laya English",
    family: "laya",
    engine: "ort",
    runnable: true,
    repo: "receptron/laya-onnx",
    revision: "main",
    bytes: 1_700_000_000,
    description: "convaiinnovations/laya exported to ONNX (ModernBERT-large, 421M, ~1.7 GB fp32).",
    files: [
      "laya.onnx",
      "laya.onnx.data",
      "laya_config.json",
      "tokenizer/tokenizer.json",
      "tokenizer/tokenizer_config.json",
    ],
    graph: "laya.onnx",
    weights: "laya.onnx.data",
    config: "laya_config.json",
    tokenizer: "tokenizer/tokenizer.json",
    tokenizerConfig: "tokenizer/tokenizer_config.json",
    webgpuGraphOpt: "all",
  },
  "laya-ml": {
    id: "laya-ml",
    title: "Laya multilingual",
    family: "laya",
    engine: "ort",
    runnable: true,
    repo: "mizchi/laya-multilingual-onnx",
    revision: "main",
    bytes: 650_000_000,
    description: "convaiinnovations/laya-multilingual ONNX (mmBERT-base, 322M, float16).",
    files: [
      "model.onnx",
      "onnx_config.json",
      "rl_agent_config.json",
      "tokenizer/tokenizer.json",
      "tokenizer/tokenizer_config.json",
    ],
    graph: "model.onnx",
    weights: null,
    config: "rl_agent_config.json",
    tokenizer: "tokenizer/tokenizer.json",
    tokenizerConfig: "tokenizer/tokenizer_config.json",
    webgpuGraphOpt: "basic",
  },
  "kev-0.5b": {
    id: "kev-0.5b",
    title: "Kev 0.5B",
    family: "kev",
    engine: "fixture",
    runnable: true,
    repo: "jaredpalmer/kev-0.5b",
    revision: "main",
    bytes: 7_000,
    description:
      "Fetches Kev's published tokenizer specials. There is no ONNX graph for the Qwen backbone, so compile uses the fixture kernel on Kev-packed tokens.",
    files: [
      "adapter_config.json",
      "added_tokens.json",
      "tokenizer_config.json",
      "special_tokens_map.json",
    ],
    graph: null,
    config: null,
  },
};

export function listModels() {
  return Object.values(MODELS);
}

export function getModel(id) {
  const model = MODELS[id];
  if (!model) {
    throw new Error(`Unknown model ${id}`);
  }
  return model;
}

export function hubFileUrl(repo, revision, file) {
  const rev = encodeURIComponent(revision || "main");
  const path = file
    .split("/")
    .map((part) => encodeURIComponent(part))
    .join("/");
  return `https://huggingface.co/${repo}/resolve/${rev}/${path}`;
}

export function bundleUrls(model) {
  if (!model.repo) {
    return [];
  }
  return model.files.map((file) => ({
    file,
    url: hubFileUrl(model.repo, model.revision, file),
  }));
}

export function formatBytes(bytes) {
  if (!bytes) {
    return "bundled";
  }
  if (bytes >= 1_000_000_000) {
    return `${(bytes / 1_000_000_000).toFixed(1)} GB`;
  }
  if (bytes >= 1_000_000) {
    return `${Math.round(bytes / 1_000_000)} MB`;
  }
  if (bytes >= 1_000) {
    return `${Math.round(bytes / 1_000)} KB`;
  }
  return `${bytes} B`;
}

export function defaultCalibration() {
  return {
    max_len: 512,
    head_max_len: 192,
    temperature: [1, 1, 1],
    temperature_by_options: {},
  };
}

export function parseLayaConfig(raw) {
  const defaults = defaultCalibration();
  if (!raw || typeof raw !== "object") {
    return defaults;
  }
  return {
    max_len: Number(raw.max_len ?? raw.maxLength ?? defaults.max_len),
    head_max_len: Number(raw.head_max_len ?? raw.headMaxLength ?? defaults.head_max_len),
    temperature: Array.isArray(raw.temperature) ? raw.temperature.map(Number) : defaults.temperature,
    temperature_by_options: raw.temperature_by_options ?? raw.temperatureByOptions ?? {},
  };
}
