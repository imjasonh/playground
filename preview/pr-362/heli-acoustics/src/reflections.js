import { add, sub, scale, length } from './geometry.js';
import { isOccluded } from './occlusion.js';
import { SPEED_OF_SOUND, GROUND, buildingFaces } from './city.js';

const REFLECTIVITY = {
  facade: 0.55,
  ground: 0.35,
};

// Reflect a point across an axis-aligned plane (constant x or z or y).
export function mirrorPoint(p, axis, value) {
  const out = [p[0], p[1], p[2]];
  const i = axis === 'x' ? 0 : axis === 'y' ? 1 : 2;
  out[i] = 2 * value - p[i];
  return out;
}

function onFace(hit, face) {
  const u = face.axis === 'x' ? hit[2] : hit[0];
  const v = hit[1];
  return u >= face.u0 - 1e-6 && u <= face.u1 + 1e-6 && v >= face.v0 - 1e-6 && v <= face.v1 + 1e-6;
}

function axisIndex(axis) {
  return axis === 'x' ? 0 : axis === 'y' ? 1 : 2;
}

function faceReflectivity(face) {
  return face.kind === 'ground' ? REFLECTIVITY.ground : REFLECTIVITY.facade;
}

export function groundFace(groundY = GROUND.y) {
  return {
    id: 'ground',
    kind: 'ground',
    building: 'ground',
    axis: 'y',
    value: groundY,
    outward: 1,
    // Huge horizontal extent; onFace for ground uses u=x, v=y so v must be ~0.
    // Ground hits are validated by y ≈ groundY instead of the v band.
    u0: -1e6,
    u1: 1e6,
    v0: -1e6,
    v1: 1e6,
  };
}

function onReflector(hit, face) {
  if (face.kind === 'ground') {
    return Math.abs(hit[1] - face.value) < 1e-4;
  }
  return onFace(hit, face);
}

// Source must sit on the outward side of a vertical facade. Ground accepts any
// source above the plane.
function sourceOnOutwardSide(source, face) {
  if (face.kind === 'ground') return source[1] > face.value + 0.05;
  const si = face.axis === 'x' ? source[0] : source[2];
  return (si - face.value) * face.outward > 0.05;
}

// Intersection of listener→image ray with a finite reflector. Returns null when
// the hit misses the face or is degenerate.
function hitOnFace(listener, image, face) {
  const toImage = sub(image, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;
  const dir = scale(toImage, 1 / pathLen);
  const ai = axisIndex(face.axis);
  if (Math.abs(dir[ai]) < 1e-9) return null;
  const tHit = (face.value - listener[ai]) / dir[ai];
  if (tHit <= 1e-4 || tHit >= pathLen - 1e-4) return null;
  const hit = add(listener, scale(dir, tHit));
  if (!onReflector(hit, face)) return null;
  return { hit, pathLen, image };
}

// Order-1 image-source reflection against one finite facade. Returns null when
// the hit misses the face, the path is degenerate, or another building blocks
// source→hit or hit→listener.
export function facadeReflection(listener, source, face, buildings) {
  if (!sourceOnOutwardSide(source, face)) return null;
  const image = mirrorPoint(source, face.axis, face.value);
  const found = hitOnFace(listener, image, face);
  if (!found) return null;
  const { hit, pathLen } = found;
  if (isOccluded(source, hit, buildings) || isOccluded(hit, listener, buildings)) return null;
  return {
    kind: 'facade',
    order: 1,
    faceId: face.id,
    hit,
    hits: [hit],
    image,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: REFLECTIVITY.facade / Math.max(pathLen, 1),
  };
}

export function groundReflection(listener, source, groundY = GROUND.y) {
  if (source[1] <= groundY + 0.05) return null;
  const image = mirrorPoint(source, 'y', groundY);
  const pathLen = length(sub(image, listener));
  if (pathLen < 1e-3) return null;
  const tHit = (groundY - listener[1]) / (image[1] - listener[1]);
  if (tHit <= 0 || tHit >= 1) return null;
  const hit = add(listener, scale(sub(image, listener), tHit));
  return {
    kind: 'ground',
    order: 1,
    faceId: 'ground',
    hit,
    hits: [hit],
    image,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: REFLECTIVITY.ground / Math.max(pathLen, 1),
  };
}

/**
 * Order-2 image source: source → faceA → faceB → listener.
 * Mirrors source across A then across B; walks the listener→image ray back
 * through both planes and rejects occluded or off-face hits.
 */
export function order2Reflection(listener, source, faceA, faceB, buildings) {
  if (faceA.id === faceB.id) return null;
  // Parallel coplanar faces cannot form a bounce sequence.
  if (faceA.axis === faceB.axis && Math.abs(faceA.value - faceB.value) < 1e-6) return null;
  if (!sourceOnOutwardSide(source, faceA)) return null;

  const image1 = mirrorPoint(source, faceA.axis, faceA.value);
  // Image1 must be on the outward side of B as if it were a real source for B.
  if (!sourceOnOutwardSide(image1, faceB)) return null;
  const image2 = mirrorPoint(image1, faceB.axis, faceB.value);

  const toImage = sub(image2, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;
  const dir = scale(toImage, 1 / pathLen);

  // First intersection from the listener is on face B (last bounce chronologically).
  const bi = axisIndex(faceB.axis);
  if (Math.abs(dir[bi]) < 1e-9) return null;
  const tB = (faceB.value - listener[bi]) / dir[bi];
  if (tB <= 1e-4 || tB >= pathLen - 1e-4) return null;
  const hitB = add(listener, scale(dir, tB));
  if (!onReflector(hitB, faceB)) return null;

  // From hitB toward image1; intersect face A.
  const toI1 = sub(image1, hitB);
  const lenI1 = length(toI1);
  if (lenI1 < 1e-3) return null;
  const dirA = scale(toI1, 1 / lenI1);
  const ai = axisIndex(faceA.axis);
  if (Math.abs(dirA[ai]) < 1e-9) return null;
  const tA = (faceA.value - hitB[ai]) / dirA[ai];
  if (tA <= 1e-4 || tA >= lenI1 - 1e-4) return null;
  const hitA = add(hitB, scale(dirA, tA));
  if (!onReflector(hitA, faceA)) return null;

  // Three clear legs: source→A, A→B, B→listener.
  if (
    isOccluded(source, hitA, buildings) ||
    isOccluded(hitA, hitB, buildings) ||
    isOccluded(hitB, listener, buildings)
  ) {
    return null;
  }

  const reflectivity = faceReflectivity(faceA) * faceReflectivity(faceB);
  return {
    kind: faceA.kind === 'ground' || faceB.kind === 'ground' ? 'order2-ground' : 'order2',
    order: 2,
    faceId: `${faceA.id}>${faceB.id}`,
    hit: hitB,
    hits: [hitA, hitB],
    image: image2,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: reflectivity / Math.max(pathLen, 1),
  };
}

/**
 * Prioritize order-2 pairs that matter in a street canyon: facade↔ground first
 * (heli in the sky), then opposite parallel facades on different buildings.
 * Same-building opposite faces are skipped; those paths go through the mass.
 */
export function order2PairList(faceList, { limit = 80 } = {}) {
  const pairs = [];
  const ground = groundFace();
  for (const f of faceList) {
    pairs.push([f, ground], [ground, f]);
  }
  for (let i = 0; i < faceList.length; i++) {
    for (let j = i + 1; j < faceList.length; j++) {
      const a = faceList[i];
      const b = faceList[j];
      if (a.building === b.building) continue;
      if (a.axis !== b.axis) continue;
      if (a.outward === b.outward) continue;
      if (Math.abs(a.value - b.value) < 1) continue;
      pairs.push([a, b], [b, a]);
    }
  }
  return pairs.slice(0, limit);
}

/**
 * Strongest early reflections up to `limit`, mixing order-1 and optional order-2.
 * Faces are cached by the caller when possible; order-2 uses a prioritized,
 * capped pair list so the CPU path stays fast without WebGPU.
 */
export function computeReflections(
  listener,
  source,
  buildings,
  {
    limit = 12,
    faces = null,
    maxOrder = 2,
    order2CandidateLimit = 80,
  } = {},
) {
  const faceList = faces || buildingFaces(buildings);
  const candidates = [];

  for (const face of faceList) {
    const r = facadeReflection(listener, source, face, buildings);
    if (r) candidates.push(r);
  }
  const g = groundReflection(listener, source);
  if (g) candidates.push(g);

  if (maxOrder >= 2) {
    const pairs = order2PairList(faceList, { limit: order2CandidateLimit });
    for (const [a, b] of pairs) {
      const r = order2Reflection(listener, source, a, b, buildings);
      if (r) candidates.push(r);
    }
  }

  candidates.sort((a, b) => b.gain - a.gain);
  return candidates.slice(0, limit);
}

// Extra path length beyond the direct path, useful for HUD / tests.
export function excessDelaySec(reflection, listener, source) {
  const direct = length(sub(source, listener));
  return reflection.delaySec - direct / SPEED_OF_SOUND;
}
