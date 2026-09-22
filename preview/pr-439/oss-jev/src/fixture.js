/**
 * Tiny decision kernel used when no ONNX graph is available.
 *
 * Each option's logit is how often its tokens (the words after the marker,
 * up to the next marker or the options SEP) appear in the state span. The
 * last option must not include the state. The WebGPU shader and the CPU
 * path must stay identical.
 */

export const FIXTURE_WGSL = `struct Counts {
  tokens: u32,
  options: u32,
  state_start: u32,
  state_end: u32,
}

@group(0) @binding(0) var<storage, read> ids: array<u32>;
@group(0) @binding(1) var<storage, read> spans: array<u32>;
@group(0) @binding(2) var<uniform> counts: Counts;
@group(0) @binding(3) var<storage, read_write> logits: array<f32>;

fn option_start(option: u32) -> u32 {
  return spans[option * 2u];
}

fn option_end(option: u32) -> u32 {
  return spans[option * 2u + 1u];
}

@compute @workgroup_size(32)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let k = gid.x;
  if (k >= counts.options) {
    return;
  }
  let start = option_start(k);
  let end = option_end(k);
  var score = 0.0;
  var t = start;
  loop {
    if (t >= end) {
      break;
    }
    let token = ids[t];
    var i = counts.state_start;
    loop {
      if (i >= counts.state_end) {
        break;
      }
      if (ids[i] == token) {
        score = score + 1.0;
      }
      i = i + 1u;
    }
    t = t + 1u;
  }
  logits[k] = score;
}
`;

/** Exclusive option spans and the state range for a Laya-packed sequence. */
export function layaFixtureSpans(ids, markers, sep) {
  const spans = [];
  for (let k = 0; k < markers.length; k += 1) {
    const start = markers[k] + 1;
    let end = ids.length;
    if (k + 1 < markers.length) {
      end = markers[k + 1];
    } else {
      for (let i = start; i < ids.length; i += 1) {
        if (ids[i] === sep) {
          end = i;
          break;
        }
      }
    }
    spans.push(start, end);
  }
  let stateStart = 0;
  let stateEnd = 0;
  if (spans.length > 0) {
    const lastEnd = spans[spans.length - 1];
    stateStart = Math.min(ids.length, lastEnd + 1);
    stateEnd = ids.length;
    if (stateEnd > stateStart && ids[stateEnd - 1] === sep) {
      stateEnd -= 1;
    }
  }
  return { spans, stateStart, stateEnd };
}

export function fixtureLogitsCpu(ids, spans, stateStart, stateEnd) {
  const options = Math.floor(spans.length / 2);
  const logits = new Float32Array(options);
  for (let k = 0; k < options; k += 1) {
    const start = spans[k * 2];
    const end = spans[k * 2 + 1];
    let score = 0;
    for (let t = start; t < end; t += 1) {
      const token = ids[t];
      for (let i = stateStart; i < stateEnd; i += 1) {
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

export async function runFixtureWebGpu(compiled, ids, spans, stateStart, stateEnd) {
  const { device, pipeline } = compiled;
  const options = Math.floor(spans.length / 2);
  const idData = new Uint32Array(ids);
  const spanData = new Uint32Array(spans.length ? spans : [0, 0]);
  const counts = new Uint32Array([ids.length, options, stateStart, stateEnd]);
  const logits = new Float32Array(Math.max(1, options));

  const idBuffer = writeBuffer(device, idData, GPUBufferUsage.STORAGE);
  const spanBuffer = writeBuffer(device, spanData, GPUBufferUsage.STORAGE);
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
      { binding: 1, resource: { buffer: spanBuffer } },
      { binding: 2, resource: { buffer: countBuffer } },
      { binding: 3, resource: { buffer: logitBuffer } },
    ],
  });

  const encoder = device.createCommandEncoder();
  const pass = encoder.beginComputePass();
  pass.setPipeline(pipeline);
  pass.setBindGroup(0, bindGroup);
  pass.dispatchWorkgroups(Math.ceil(Math.max(1, options) / 32));
  pass.end();
  const copyBytes = options * 4;
  if (copyBytes > 0) {
    encoder.copyBufferToBuffer(logitBuffer, 0, readBuffer, 0, copyBytes);
  }
  device.queue.submit([encoder.finish()]);
  if (copyBytes > 0) {
    await readBuffer.mapAsync(GPUMapMode.READ);
    const out = new Float32Array(options);
    out.set(new Float32Array(readBuffer.getMappedRange().slice(0, copyBytes)));
    readBuffer.unmap();
    idBuffer.destroy();
    spanBuffer.destroy();
    countBuffer.destroy();
    logitBuffer.destroy();
    readBuffer.destroy();
    return out;
  }
  idBuffer.destroy();
  spanBuffer.destroy();
  countBuffer.destroy();
  logitBuffer.destroy();
  readBuffer.destroy();
  return new Float32Array();
}

function writeBuffer(device, data, usage) {
  const buffer = device.createBuffer({
    size: Math.max(4, data.byteLength),
    usage: usage + GPUBufferUsage.COPY_DST,
  });
  device.queue.writeBuffer(buffer, 0, data);
  return buffer;
}

async function runFixture(webgpu, ids, spans, stateStart, stateEnd) {
  if (webgpu) {
    return runFixtureWebGpu(webgpu, ids, spans, stateStart, stateEnd);
  }
  return fixtureLogitsCpu(ids, spans, stateStart, stateEnd);
}

export function createFixtureSession({ webgpu = null, backend = "cpu", sep = 2 } = {}) {
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
        const { spans, stateStart, stateEnd } = layaFixtureSpans(ids, markers, sep);
        const logits = await runFixture(webgpu, ids, spans, stateStart, stateEnd);
        rows.push({ logits, action: fixtureAction() });
      }
      return rows;
    },
    async runKev(encoding) {
      const stateEnd = encoding.seg.filter((value) => value === 0).length;
      const rows = [];
      const opens = encoding.optOpenIdx ?? [];
      for (let index = 0; index < encoding.optIdx.length; index += 1) {
        const closes = encoding.optIdx[index];
        const starts = opens[index] ?? closes;
        const spans = [];
        starts.forEach((start, option) => {
          spans.push(start + 1, closes[option]);
        });
        const logits = await runFixture(webgpu, encoding.ids, spans, 0, stateEnd);
        rows.push({ logits, action: fixtureAction() });
      }
      return rows;
    },
    async release() {
      webgpu?.device?.destroy?.();
    },
  };
}
