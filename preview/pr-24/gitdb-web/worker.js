/* global Go */

function fatal(error) {
  self.postMessage(JSON.stringify({
    type: "fatal",
    error: error instanceof Error ? error.message : String(error),
  }));
}

async function instantiate(url, imports) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Unable to load ${url.pathname}: HTTP ${response.status}`);
  }
  if (WebAssembly.instantiateStreaming) {
    try {
      return await WebAssembly.instantiateStreaming(response.clone(), imports);
    } catch (error) {
      console.warn("Streaming WASM initialization failed; using ArrayBuffer fallback", error);
    }
  }
  return WebAssembly.instantiate(await response.arrayBuffer(), imports);
}

try {
  const runtimeURL = new URL("./generated/wasm_exec.js", self.location.href);
  const wasmURL = new URL("./generated/gitdb.wasm", self.location.href);
  importScripts(runtimeURL.href);

  const go = new Go();
  instantiate(wasmURL, go.importObject)
    .then(({ instance }) => go.run(instance))
    .catch(fatal);
} catch (error) {
  fatal(error);
}
