// WebGPU image-source + occlusion solver. Each candidate (order-1 face or
// order-2 pair) runs as one compute thread against uploaded AABBs/faces.
// WebGPU is required for the live app; there is no CPU runtime fallback.

import { BUILDINGS, SPEED_OF_SOUND, buildingFaces } from './city.js';
import {
  groundFace,
  order2PairList,
  order3TripleList,
  order3Reflection,
} from './reflections.js';
import { enclosureAt } from './enclosure.js';
import { computeDiffraction } from './diffraction.js';
import {
  materialForFace,
  bounceBands,
  unitBands,
  cutoffFromBands,
  gainFromBands,
  meanPressureReflection,
  sphericalPressureGain,
} from './materials.js';
import { applyAirToBands } from './airAbsorption.js';
import { occlusionAmount } from './occlusion.js';
import { traceEnergyBins } from './stochasticIr.js';

const MAX_OUT = 96;

const SHADER = /* wgsl */ `
struct Uniforms {
  listener: vec3f,
  _pad0: f32,
  source: vec3f,
  speedOfSound: f32,
  buildingCount: u32,
  faceCount: u32,
  jobCount: u32,
  _pad1: u32,
}

struct Building {
  bmin: vec3f,
  _pad0: f32,
  bmax: vec3f,
  _pad1: f32,
}

// axis: 0=x 1=y 2=z; kind: 0=facade 1=ground
struct Face {
  axis: f32,
  value: f32,
  outward: f32,
  u0: f32,
  u1: f32,
  v0: f32,
  v1: f32,
  reflectivity: f32,
  kind: f32,
  _p0: f32,
  _p1: f32,
  _p2: f32,
}

struct Job {
  kind: u32, // 0=order1 1=order2
  faceA: u32,
  faceB: u32,
  _pad: u32,
}

struct ReflectionOut {
  valid: f32,
  order: f32,
  gain: f32,
  delaySec: f32,
  pathLength: f32,
  imageX: f32,
  imageY: f32,
  imageZ: f32,
  hit0X: f32,
  hit0Y: f32,
  hit0Z: f32,
  hit1X: f32,
  hit1Y: f32,
  hit1Z: f32,
  faceA: f32,
  faceB: f32,
}

@group(0) @binding(0) var<uniform> u: Uniforms;
@group(0) @binding(1) var<storage, read> buildings: array<Building>;
@group(0) @binding(2) var<storage, read> faces: array<Face>;
@group(0) @binding(3) var<storage, read> jobs: array<Job>;
@group(0) @binding(4) var<storage, read_write> outs: array<ReflectionOut>;
@group(0) @binding(5) var<storage, read_write> occlusion: array<f32>;

fn mirror_point(p: vec3f, axis: i32, value: f32) -> vec3f {
  var out = p;
  if (axis == 0) { out.x = 2.0 * value - p.x; }
  else if (axis == 1) { out.y = 2.0 * value - p.y; }
  else { out.z = 2.0 * value - p.z; }
  return out;
}

fn axis_i(axis: f32) -> i32 {
  return i32(axis + 0.5);
}

fn component(p: vec3f, axis: i32) -> f32 {
  if (axis == 0) { return p.x; }
  if (axis == 1) { return p.y; }
  return p.z;
}

fn on_reflector(hit: vec3f, f: Face) -> bool {
  if (f.kind > 0.5) {
    return abs(hit.y - f.value) < 1e-3;
  }
  let ai = axis_i(f.axis);
  let uu = select(hit.x, hit.z, ai == 0);
  let vv = hit.y;
  return uu >= f.u0 - 1e-4 && uu <= f.u1 + 1e-4 && vv >= f.v0 - 1e-4 && vv <= f.v1 + 1e-4;
}

fn source_outward(source: vec3f, f: Face) -> bool {
  if (f.kind > 0.5) {
    return source.y > f.value + 0.05;
  }
  let ai = axis_i(f.axis);
  let s = component(source, ai);
  return (s - f.value) * f.outward > 0.05;
}

fn ray_aabb(origin: vec3f, dir: vec3f, b: Building) -> f32 {
  var tmin = 0.0;
  var tmax = 1e30;
  for (var i = 0; i < 3; i++) {
    let o = component(origin, i);
    let d = component(dir, i);
    let mn = component(b.bmin, i);
    let mx = component(b.bmax, i);
    if (abs(d) < 1e-12) {
      if (o < mn || o > mx) { return -1.0; }
      continue;
    }
    var t1 = (mn - o) / d;
    var t2 = (mx - o) / d;
    if (t1 > t2) {
      let tmp = t1; t1 = t2; t2 = tmp;
    }
    tmin = max(tmin, t1);
    tmax = min(tmax, t2);
    if (tmin > tmax) { return -1.0; }
  }
  if (tmax < 0.0) { return -1.0; }
  let t = select(tmax, tmin, tmin >= 0.0);
  return select(-1.0, t, t >= 0.0);
}

fn is_occluded(a: vec3f, b: vec3f) -> bool {
  let delta = b - a;
  let dist = length(delta);
  if (dist < 1e-6) { return false; }
  let dir = delta / dist;
  let eps = 0.05;
  for (var i = 0u; i < u.buildingCount; i++) {
    let t = ray_aabb(a, dir, buildings[i]);
    if (t > eps && t < dist - eps) { return true; }
  }
  return false;
}

fn clear_out(i: u32) {
  outs[i].valid = 0.0;
  outs[i].order = 0.0;
  outs[i].gain = 0.0;
  outs[i].delaySec = 0.0;
  outs[i].pathLength = 0.0;
}

fn write_out(
  i: u32,
  order: f32,
  gain: f32,
  pathLen: f32,
  image: vec3f,
  hit0: vec3f,
  hit1: vec3f,
  faceA: f32,
  faceB: f32,
) {
  outs[i].valid = 1.0;
  outs[i].order = order;
  outs[i].gain = gain;
  outs[i].delaySec = pathLen / u.speedOfSound;
  outs[i].pathLength = pathLen;
  outs[i].imageX = image.x;
  outs[i].imageY = image.y;
  outs[i].imageZ = image.z;
  outs[i].hit0X = hit0.x;
  outs[i].hit0Y = hit0.y;
  outs[i].hit0Z = hit0.z;
  outs[i].hit1X = hit1.x;
  outs[i].hit1Y = hit1.y;
  outs[i].hit1Z = hit1.z;
  outs[i].faceA = faceA;
  outs[i].faceB = faceB;
}

fn eval_order1(i: u32, faceIdx: u32) {
  let f = faces[faceIdx];
  let source = u.source;
  let listener = u.listener;
  if (!source_outward(source, f)) { clear_out(i); return; }
  let ai = axis_i(f.axis);
  let image = mirror_point(source, ai, f.value);
  let toImage = image - listener;
  let pathLen = length(toImage);
  if (pathLen < 1e-3) { clear_out(i); return; }
  let dir = toImage / pathLen;
  let dComp = component(dir, ai);
  if (abs(dComp) < 1e-9) { clear_out(i); return; }
  let tHit = (f.value - component(listener, ai)) / dComp;
  if (tHit <= 1e-4 || tHit >= pathLen - 1e-4) { clear_out(i); return; }
  let hit = listener + dir * tHit;
  if (!on_reflector(hit, f)) { clear_out(i); return; }
  if (is_occluded(source, hit) || is_occluded(hit, listener)) { clear_out(i); return; }
  let gain = f.reflectivity / max(pathLen, 1.0);
  write_out(i, 1.0, gain, pathLen, image, hit, hit, f32(faceIdx), -1.0);
}

fn eval_order2(i: u32, idxA: u32, idxB: u32) {
  let faceA = faces[idxA];
  let faceB = faces[idxB];
  if (idxA == idxB) { clear_out(i); return; }
  let ai = axis_i(faceA.axis);
  let bi = axis_i(faceB.axis);
  if (ai == bi && abs(faceA.value - faceB.value) < 1e-6) { clear_out(i); return; }
  let source = u.source;
  let listener = u.listener;
  if (!source_outward(source, faceA)) { clear_out(i); return; }
  let image1 = mirror_point(source, ai, faceA.value);
  if (!source_outward(image1, faceB)) { clear_out(i); return; }
  let image2 = mirror_point(image1, bi, faceB.value);
  let toImage = image2 - listener;
  let pathLen = length(toImage);
  if (pathLen < 1e-3) { clear_out(i); return; }
  let dir = toImage / pathLen;
  let dB = component(dir, bi);
  if (abs(dB) < 1e-9) { clear_out(i); return; }
  let tB = (faceB.value - component(listener, bi)) / dB;
  if (tB <= 1e-4 || tB >= pathLen - 1e-4) { clear_out(i); return; }
  let hitB = listener + dir * tB;
  if (!on_reflector(hitB, faceB)) { clear_out(i); return; }
  let toI1 = image1 - hitB;
  let lenI1 = length(toI1);
  if (lenI1 < 1e-3) { clear_out(i); return; }
  let dirA = toI1 / lenI1;
  let dA = component(dirA, ai);
  if (abs(dA) < 1e-9) { clear_out(i); return; }
  let tA = (faceA.value - component(hitB, ai)) / dA;
  if (tA <= 1e-4 || tA >= lenI1 - 1e-4) { clear_out(i); return; }
  let hitA = hitB + dirA * tA;
  if (!on_reflector(hitA, faceA)) { clear_out(i); return; }
  if (is_occluded(source, hitA) || is_occluded(hitA, hitB) || is_occluded(hitB, listener)) {
    clear_out(i); return;
  }
  let gain = (faceA.reflectivity * faceB.reflectivity) / max(pathLen, 1.0);
  write_out(i, 2.0, gain, pathLen, image2, hitA, hitB, f32(idxA), f32(idxB));
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3u) {
  let i = gid.x;
  // Thread 0 also writes direct-path occlusion.
  if (i == 0u) {
    occlusion[0] = select(0.0, 1.0, is_occluded(u.listener, u.source));
  }
  if (i >= u.jobCount) { return; }
  let job = jobs[i];
  if (job.kind == 0u) {
    eval_order1(i, job.faceA);
  } else {
    eval_order2(i, job.faceA, job.faceB);
  }
}
`;

function packBuildings(buildings) {
  const data = new Float32Array(buildings.length * 8);
  buildings.forEach((b, i) => {
    const o = i * 8;
    data[o] = b.min[0];
    data[o + 1] = b.min[1];
    data[o + 2] = b.min[2];
    data[o + 4] = b.max[0];
    data[o + 5] = b.max[1];
    data[o + 6] = b.max[2];
  });
  return data;
}

function packFace(face, reflectivity, kind) {
  const axis = face.axis === 'x' ? 0 : face.axis === 'y' ? 1 : 2;
  return [
    axis,
    face.value,
    face.outward,
    face.u0,
    face.u1,
    face.v0,
    face.v1,
    reflectivity,
    kind,
    0,
    0,
    0,
  ];
}

function buildFaceTable(buildings) {
  const facades = buildingFaces(buildings);
  const faces = [...facades, groundFace()];
  const ids = faces.map((f) => f.id);
  const packed = new Float32Array(faces.length * 12);
  faces.forEach((f, i) => {
    const kind = f.kind === 'ground' ? 1 : 0;
    const mat = materialForFace(f);
    packed.set(packFace(f, meanPressureReflection(mat), kind), i * 12);
  });
  return { faces, ids, packed, facadeCount: facades.length };
}

function enrichSpecular(r, faces) {
  if (r.bands && r.cutoffHz != null && r._airApplied) return r;
  const parts = String(r.faceId).split('>');
  let bands = unitBands();
  for (const id of parts) {
    const face = faces.find((f) => f.id === id) || groundFace();
    bands = bounceBands(bands, materialForFace(face));
  }
  const pathLen = r.pathLength || 1;
  bands = applyAirToBands(bands, pathLen);
  return {
    ...r,
    bands,
    gain: gainFromBands(bands) * sphericalPressureGain(pathLen),
    cutoffHz: cutoffFromBands(bands, pathLen),
    _airApplied: true,
  };
}

function finalizeEarly(listener, source, buildings, specular, limit) {
  const faceList = [...buildingFaces(buildings), groundFace()];
  const withBands = specular.map((r) => enrichSpecular(r, faceList));
  const diffracted = computeDiffraction(listener, source, buildings, { limit: 8 });
  const all = [...withBands, ...diffracted].sort((a, b) => b.gain - a.gain);
  return {
    reflections: all.slice(0, limit),
    diffractionCount: diffracted.length,
    order3Count: withBands.filter((r) => r.order === 3).length,
  };
}

function buildJobs(faceTable, order2Limit = 80) {
  const jobs = [];
  // Order-1: every facade + ground.
  for (let i = 0; i < faceTable.faces.length; i++) {
    jobs.push({ kind: 0, faceA: i, faceB: 0 });
  }
  const pairs = order2PairList(faceTable.faces.slice(0, faceTable.facadeCount), {
    limit: order2Limit,
  });
  const idToIndex = new Map(faceTable.ids.map((id, i) => [id, i]));
  for (const [a, b] of pairs) {
    const ia = idToIndex.get(a.id);
    const ib = idToIndex.get(b.id);
    if (ia === undefined || ib === undefined) continue;
    jobs.push({ kind: 1, faceA: ia, faceB: ib });
  }
  const packed = new Uint32Array(jobs.length * 4);
  jobs.forEach((j, i) => {
    const o = i * 4;
    packed[o] = j.kind;
    packed[o + 1] = j.faceA;
    packed[o + 2] = j.faceB;
  });
  return { jobs, packed };
}

/**
 * WebGPU acoustics engine. Call `init()` once, then `compute()` each frame.
 * Specular order-1/2 run on GPU; order-3, diffraction, and stochastic IR bins
 * are merged on the CPU (still cheap at this city size).
 * Init fails hard if WebGPU is missing — no silent CPU substitute.
 */
export class GpuAcoustics {
  constructor({ buildings = BUILDINGS, limit = 16 } = {}) {
    this.buildings = buildings;
    this.limit = limit;
    this.backend = 'uninit';
    this.device = null;
    this.ready = false;
    this.faceTable = buildFaceTable(buildings);
    this.jobTable = buildJobs(this.faceTable);
    this._frame = 0;
    this._irBins = null;
    this._irListener = null;
  }

  async init() {
    if (!globalThis.navigator?.gpu) {
      throw new Error('WebGPU is required (navigator.gpu is missing)');
    }
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) {
      throw new Error('WebGPU is required (no GPU adapter)');
    }
    this.device = await adapter.requestDevice();
    this.device.lost.then((info) => {
      this.backend = 'lost';
      this.ready = false;
      this.device = null;
      console.error('WebGPU device lost:', info?.message || info);
    });

    const buildingData = packBuildings(this.buildings);
    this.buildingBuf = this.device.createBuffer({
      size: buildingData.byteLength,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });
    this.device.queue.writeBuffer(this.buildingBuf, 0, buildingData);

    this.faceBuf = this.device.createBuffer({
      size: this.faceTable.packed.byteLength,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });
    this.device.queue.writeBuffer(this.faceBuf, 0, this.faceTable.packed);

    this.jobBuf = this.device.createBuffer({
      size: this.jobTable.packed.byteLength,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });
    this.device.queue.writeBuffer(this.jobBuf, 0, this.jobTable.packed);

    this.uniformBuf = this.device.createBuffer({
      size: 48,
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
    });

    const outFloats = MAX_OUT * 16;
    this.outBuf = this.device.createBuffer({
      size: outFloats * 4,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC,
    });
    this.occBuf = this.device.createBuffer({
      size: 16,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC,
    });
    this.outRead = this.device.createBuffer({
      size: outFloats * 4,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });
    this.occRead = this.device.createBuffer({
      size: 16,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });

    const module = this.device.createShaderModule({ code: SHADER });
    this.pipeline = this.device.createComputePipeline({
      layout: 'auto',
      compute: { module, entryPoint: 'main' },
    });
    this.bindGroup = this.device.createBindGroup({
      layout: this.pipeline.getBindGroupLayout(0),
      entries: [
        { binding: 0, resource: { buffer: this.uniformBuf } },
        { binding: 1, resource: { buffer: this.buildingBuf } },
        { binding: 2, resource: { buffer: this.faceBuf } },
        { binding: 3, resource: { buffer: this.jobBuf } },
        { binding: 4, resource: { buffer: this.outBuf } },
        { binding: 5, resource: { buffer: this.occBuf } },
      ],
    });

    this.backend = 'webgpu';
    this.ready = true;
    return this;
  }

  /**
   * @param {number[]} listener
   * @param {number[]} source
   * @returns {Promise<{ occlusion: number, reflections: Array, enclosure: object, backend: string }>}
   */
  async compute(listener, source) {
    if (!this.ready) await this.init();
    if (this.backend !== 'webgpu' || !this.device) {
      throw new Error('WebGPU acoustics device is not available');
    }
    this._frame++;
    const movedFar =
      !this._irListener ||
      Math.hypot(
        listener[0] - this._irListener[0],
        listener[1] - this._irListener[1],
        listener[2] - this._irListener[2],
      ) > 8;
    if (!this._irBins || this._frame % 12 === 0 || movedFar) {
      this._irBins = traceEnergyBins(listener, source, this.buildings, {
        rays: 160,
        bounces: 5,
        seed: (this._frame % 97) + 1,
      });
      this._irListener = listener.slice();
    }

    const jobCount = Math.min(this.jobTable.jobs.length, MAX_OUT);
    const uniforms = new ArrayBuffer(48);
    const f32 = new Float32Array(uniforms);
    const u32 = new Uint32Array(uniforms);
    f32[0] = listener[0];
    f32[1] = listener[1];
    f32[2] = listener[2];
    f32[4] = source[0];
    f32[5] = source[1];
    f32[6] = source[2];
    f32[7] = SPEED_OF_SOUND;
    u32[8] = this.buildings.length;
    u32[9] = this.faceTable.faces.length;
    u32[10] = jobCount;
    this.device.queue.writeBuffer(this.uniformBuf, 0, uniforms);

    const encoder = this.device.createCommandEncoder();
    const pass = encoder.beginComputePass();
    pass.setPipeline(this.pipeline);
    pass.setBindGroup(0, this.bindGroup);
    pass.dispatchWorkgroups(Math.ceil(jobCount / 64));
    pass.end();
    encoder.copyBufferToBuffer(this.outBuf, 0, this.outRead, 0, jobCount * 16 * 4);
    encoder.copyBufferToBuffer(this.occBuf, 0, this.occRead, 0, 16);
    this.device.queue.submit([encoder.finish()]);

    await Promise.all([this.outRead.mapAsync(GPUMapMode.READ), this.occRead.mapAsync(GPUMapMode.READ)]);
    const outData = new Float32Array(this.outRead.getMappedRange().slice(0));
    const occData = new Float32Array(this.occRead.getMappedRange().slice(0));
    this.outRead.unmap();
    this.occRead.unmap();

    const gpuSpecular = [];
    for (let i = 0; i < jobCount; i++) {
      const o = i * 16;
      if (outData[o] < 0.5) continue;
      const order = outData[o + 1] > 1.5 ? 2 : 1;
      const hit0 = [outData[o + 8], outData[o + 9], outData[o + 10]];
      const hit1 = [outData[o + 11], outData[o + 12], outData[o + 13]];
      const faceA = outData[o + 14];
      const faceB = outData[o + 15];
      const idA = this.faceTable.ids[faceA] || `f${faceA}`;
      const idB = faceB >= 0 ? this.faceTable.ids[faceB] : null;
      gpuSpecular.push({
        kind:
          order === 2
            ? idA === 'ground' || idB === 'ground'
              ? 'order2-ground'
              : 'order2'
            : idA === 'ground'
              ? 'ground'
              : 'facade',
        order,
        faceId: order === 2 ? `${idA}>${idB}` : idA,
        hit: order === 2 ? hit1 : hit0,
        hits: order === 2 ? [hit0, hit1] : [hit0],
        image: [outData[o + 5], outData[o + 6], outData[o + 7]],
        pathLength: outData[o + 4],
        delaySec: outData[o + 3],
        gain: outData[o + 2],
      });
    }

    // Order-3 on CPU; diffraction on CPU; material bands on merge.
    const faceList = buildingFaces(this.buildings);
    const order3 = [];
    for (const [a, b, c] of order3TripleList(faceList, { limit: 48 })) {
      const r = order3Reflection(listener, source, a, b, c, this.buildings);
      if (r) order3.push(r);
    }
    const early = finalizeEarly(
      listener,
      source,
      this.buildings,
      [...gpuSpecular, ...order3],
      this.limit,
    );
    const enclosure = enclosureAt(listener, this.buildings);
    // Soft Maekawa occlusion on CPU (GPU LOS is binary for visibility only).
    const softOcc = occlusionAmount(listener, source, this.buildings);
    return {
      occlusion: softOcc,
      reflections: early.reflections,
      enclosure,
      irBins: this._irBins,
      diffractionCount: early.diffractionCount,
      order3Count: early.order3Count,
      backend: 'webgpu',
    };
  }
}
