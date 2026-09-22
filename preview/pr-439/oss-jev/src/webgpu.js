export async function detectWebGPU(gpu = globalThis.navigator?.gpu) {
  if (!gpu?.requestAdapter) {
    return { available: false, reason: "This browser does not expose navigator.gpu." };
  }
  try {
    const adapter = await gpu.requestAdapter();
    if (!adapter) {
      return { available: false, reason: "No WebGPU adapter." };
    }
    const info = adapter.info ?? {};
    return {
      available: true,
      info: {
        vendor: info.vendor ?? "",
        architecture: info.architecture ?? "",
        device: info.device ?? "",
        description: info.description ?? adapter.name ?? "",
      },
    };
  } catch (error) {
    return { available: false, reason: error.message };
  }
}

export function preferWebGpu(choice, detected) {
  if (choice === "wasm" || choice === "cpu") {
    return false;
  }
  if (choice === "webgpu") {
    return true;
  }
  return Boolean(detected?.available);
}
