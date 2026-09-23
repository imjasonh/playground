import { spawn } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { defaultLayaDir } from "./laya-ort.js";

const SCRIPT = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "scripts", "laya_serve.py");

export async function startLayaServer(options = {}) {
  const port = Number(options.port ?? process.env.LAYA_PORT ?? 8091);
  const host = options.host ?? "127.0.0.1";
  const url = `http://${host}:${port}`;
  if (await probe(url)) {
    return { url, child: null };
  }
  const child = spawn(
    options.python ?? process.env.LAYA_PYTHON ?? "python3",
    [SCRIPT, "--dir", options.modelDir ?? defaultLayaDir(), "--host", host, "--port", String(port)],
    { stdio: ["ignore", "pipe", "pipe"] },
  );
  let stderr = "";
  child.stderr.on("data", (chunk) => {
    stderr += chunk.toString();
  });
  child.stdout.on("data", (chunk) => {
    process.stdout.write(chunk);
  });
  const started = Date.now();
  while (Date.now() - started < (options.timeout_ms ?? 120_000)) {
    if (child.exitCode != null) {
      throw new Error(`Laya server exited ${child.exitCode}: ${stderr.slice(0, 400)}`);
    }
    if (await probe(url)) {
      return { url, child };
    }
    await sleep(250);
  }
  child.kill();
  throw new Error(`Laya server did not start: ${stderr.slice(0, 400)}`);
}

async function probe(url) {
  try {
    const response = await fetch(`${url}/health`, { signal: AbortSignal.timeout(1000) });
    return response.ok;
  } catch {
    return false;
  }
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
