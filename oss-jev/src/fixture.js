/**
 * Tiny decision kernel used when no ONNX graph is available.
 *
 * Each option's logit is the sum of shared tokens between the state ids and
 * the tokens that follow that option's marker, plus a small bias from the
 * marker position. The WebGPU shader and the CPU path must stay identical.
 */

export const FIXTURE_WGSL = `struct Counts {
  tokens: u32,
  options: u32,
}

@group(0) @binding(0) var<storage, read> ids: array<u32>;
@group(0) @binding(1) var<storage, read> markers: array<u32>;
@group(0) @binding(2) var<uniform> counts: Counts;
@group(0) @binding(3) var<storage, read_write> logits: array<f32>;

fn option_end(start: u32, option: u32) -> u32 {
  if (option + 1u < counts.options) {
    return markers[option + 1u];
  }
  return counts.tokens;
}

@compute @workgroup_size(32)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let k = gid.x;
  if (k >= counts.options) {
    return;
  }
  let start = markers[k];
  let end = option_end(start, k);
  var score = f32(k) * 0.01;
  var t = start;
  loop {
    if (t >= end) {
      break;
    }
    let token = ids[t];
    var i = 0u;
    loop {
      if (i >= counts.tokens) {
        break;
      }
      if (i < start && ids[i] == token) {
        score = score + 1.0;
      }
      i = i + 1u;
    }
    t = t + 1u;
  }
  logits[k] = score;
}
`;

export function fixtureLogitsCpu(ids, markers) {
  const logits = new Float32Array(markers.length);
  for (let k = 0; k < markers.length; k += 1) {
    const start = markers[k];
    const end = k + 1 < markers.length ? markers[k + 1] : ids.length;
    let score = k * 0.01;
    for (let t = start; t < end; t += 1) {
      const token = ids[t];
      for (let i = 0; i < start; i += 1) {
        if (ids[i] === token) {
          score += 1;
        }
      }
    }
    logits[k] = score;
  }
  return logits;
}

export function fixtureAction() {
  return new Float32Array([2, 0]);
}

export async function compileFixtureWebGpu(gpu = globalThis.navigator?.gpu) {
  if (!gpu?.requestAdapter) {
    return null;
  }
  const adapter = await gpu.requestAdapter();
  if (!adapter) {
    return null;
  }
  const device = await adapter.requestDevice();
  const module = device.createShaderModule({ code: FIXTURE_WGSL });
  const pipeline = device.createComputePipeline({
    layout: "auto",
    compute: { module, entryPoint: "main" },
  });
  return { device, pipeline };
}

export async function runFixtureWebGpu(compiled, ids, markers) {
  const { device, pipeline } = compiled;
  const idData = new Uint32Array(ids);
  const markerData = new Uint32Array(markers);
  const counts = new Uint32Array([ids.length, markers.length]);
  const logits = new Float32Array(markers.length);

  const idBuffer = writeBuffer(device, idData, GPUBufferUsage.STORAGE);
  const markerBuffer = writeBuffer(device, markerData, GPUBufferUsage.STORAGE);
  const countBuffer = writeBuffer(device, counts, GPUBufferUsage.UNIFORM);
  const logitBuffer = device.createBuffer({
    size: Math.max(4, logits.byteLength),
    usage: GPUBufferUsage.STORAGE + GPUBufferUsage.COPY_SRC,
  });
  const readBuffer = device.createBuffer({
    size: Math.max(4, logits.byteLength),
    usage: GPUBufferUsage.COPY_DST + GPUBufferUsage.MAP_READ,
  });

  const bindGroup = device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: [
      { binding: 0, resource: { buffer: idBuffer } },
      { binding: 1, resource: { buffer: markerBuffer } },
      { binding: 2, resource: { buffer: countBuffer } },
      { binding: 3, resource: { buffer: logitBuffer } },
    ],
  });

  const encoder = device.createCommandEncoder();
  const pass = encoder.beginComputePass();
  pass.setPipeline(pipeline);
  pass.setBindGroup(0, bindGroup);
  pass.dispatchWorkgroups(Math.ceil(markers.length / 32));
  pass.end();
  encoder.copyBufferToBuffer(logitBuffer, 0, readBuffer, 0, logits.byteLength);
  device.queue.submit([encoder.finish()]);
  await readBuffer.mapAsync(GPUMapMode.READ);
  logits.set(new Float32Array(readBuffer.getMappedRange().slice(0, logits.byteLength)));
  readBuffer.unmap();
  idBuffer.destroy();
  markerBuffer.destroy();
  countBuffer.destroy();
  logitBuffer.destroy();
  readBuffer.destroy();
  return logits;
}

function writeBuffer(device, data, usage) {
  const buffer = device.createBuffer({
    size: Math.max(4, data.byteLength),
    usage: usage + GPUBufferUsage.COPY_DST,
  });
  device.queue.writeBuffer(buffer, 0, data);
  return buffer;
}

export function createFixtureSession({ webgpu = null, backend = "cpu" } = {}) {
  return {
    backend,
    engine: "fixture",
    async runLaya(batch) {
      const rows = [];
      for (let row = 0; row < batch.n; row += 1) {
        const length = batch.length;
        const ids = [];
        for (let i = 0; i < length; i += 1) {
          if (batch.attention[row * length + i] === 0n) {
            break;
          }
          ids.push(Number(batch.inputIds[row * length + i]));
        }
        const markers = [];
        for (let k = 0; k < batch.maxOptions; k += 1) {
          if (!batch.markerMask[row * batch.maxOptions + k]) {
            break;
          }
          markers.push(Number(batch.markerPos[row * batch.maxOptions + k]));
        }
        const logits = webgpu
          ? await runFixtureWebGpu(webgpu, ids, markers)
          : fixtureLogitsCpu(ids, markers);
        rows.push({ logits, action: fixtureAction() });
      }
      return rows;
    },
    async runKev(encoding) {
      const rows = [];
      for (const markers of encoding.optIdx) {
        const logits = webgpu
          ? await runFixtureWebGpu(webgpu, encoding.ids, markers)
          : fixtureLogitsCpu(encoding.ids, markers);
        rows.push({ logits, action: fixtureAction() });
      }
      return rows;
    },
    async release() {
      webgpu?.device?.destroy?.();
    },
  };
}
