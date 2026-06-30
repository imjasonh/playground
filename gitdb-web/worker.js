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
  if (!response.body || typeof DecompressionStream !== "function") {
    throw new Error("This browser cannot decompress the WebAssembly runtime");
  }
  const wasmResponse = new Response(
    response.body.pipeThrough(new DecompressionStream("gzip")),
    { headers: { "Content-Type": "application/wasm" } },
  );
  if (WebAssembly.instantiateStreaming) {
    try {
      return await WebAssembly.instantiateStreaming(wasmResponse.clone(), imports);
    } catch (error) {
      console.warn("Streaming WASM initialization failed; using ArrayBuffer fallback", error);
    }
  }
  return WebAssembly.instantiate(await wasmResponse.arrayBuffer(), imports);
}

try {
  const runtimeURL = new URL("./generated/wasm_exec.js", self.location.href);
  const wasmURL = new URL("./generated/gitdb.wasm.gz", self.location.href);
  importScripts(runtimeURL.href);

  const go = new Go();
  instantiate(wasmURL, go.importObject)
    .then(({ instance }) => go.run(instance))
    .catch(fatal);
} catch (error) {
  fatal(error);
}
