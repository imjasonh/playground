import { createWriteStream } from "node:fs";
import { mkdir, rename, stat } from "node:fs/promises";
import path from "node:path";
import { Readable } from "node:stream";
import { pipeline } from "node:stream/promises";
import { defaultLayaDir, layaBundleReady } from "./laya-ort.js";

const DEFAULT_BASE = "https://raw.githubusercontent.com/koteitan/laya-int8/main";
const DEFAULT_SIZE = 324_983_479;
const PARTS = ["model.onnx.000", "model.onnx.001", "model.onnx.002", "model.onnx.003"];
const SIDE_FILES = [
  "onnx_config.json",
  "rl_agent_config.json",
  "tokenizer/tokenizer.json",
  "tokenizer/tokenizer_config.json",
];

export async function ensureLayaBundle(options = {}) {
  const dir = options.modelDir ?? defaultLayaDir();
  const expected = options.size ?? DEFAULT_SIZE;
  if (layaBundleReady(dir) && (await fileSize(path.join(dir, "model.onnx"))) === expected) {
    return dir;
  }
  const base = (options.base ?? process.env.LAYA_BUNDLE_BASE ?? DEFAULT_BASE).replace(/\/$/, "");
  await mkdir(path.join(dir, "tokenizer"), { recursive: true });
  for (const part of PARTS) {
    const dest = path.join(dir, part);
    if (!(await fileExists(dest))) {
      await download(`${base}/${part}`, dest);
    }
  }
  const assembled = path.join(dir, "model.onnx");
  if (!(await fileExists(assembled)) || (await fileSize(assembled)) !== expected) {
    await concatFiles(
      PARTS.map((part) => path.join(dir, part)),
      assembled,
    );
  }
  if ((await fileSize(assembled)) !== expected) {
    throw new Error(`Laya bundle size ${(await fileSize(assembled))}, expected ${expected}`);
  }
  for (const rel of SIDE_FILES) {
    const dest = path.join(dir, rel);
    if (!(await fileExists(dest))) {
      await download(`${base}/${rel}`, dest);
    }
  }
  return dir;
}

async function download(url, dest) {
  const tmp = `${dest}.part`;
  const response = await fetch(url, { signal: AbortSignal.timeout(120_000) });
  if (!response.ok) {
    throw new Error(`GET ${url} ${response.status}`);
  }
  await pipeline(Readable.fromWeb(response.body), createWriteStream(tmp));
  await rename(tmp, dest);
}

async function concatFiles(sources, dest) {
  const tmp = `${dest}.part`;
  const out = createWriteStream(tmp);
  for (const source of sources) {
    const { createReadStream } = await import("node:fs");
    await pipeline(createReadStream(source), out, { end: false });
  }
  await new Promise((resolve, reject) => {
    out.end((err) => (err ? reject(err) : resolve()));
  });
  await rename(tmp, dest);
}

async function fileExists(filePath) {
  try {
    await stat(filePath);
    return true;
  } catch {
    return false;
  }
}

async function fileSize(filePath) {
  try {
    return (await stat(filePath)).size;
  } catch {
    return 0;
  }
}
