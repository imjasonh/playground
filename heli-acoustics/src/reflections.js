import { add, sub, scale, length } from './geometry.js';
import { isOccluded } from './occlusion.js';
import { SPEED_OF_SOUND, GROUND, buildingFaces } from './city.js';
import {
  materialForFace,
  bounceBands,
  unitBands,
  cutoffFromBands,
  gainFromBands,
  sphericalPressureGain,
} from './materials.js';
import { applyAirToBands } from './airAbsorption.js';

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

export function groundFace(groundY = GROUND.y) {
  return {
    id: 'ground',
    kind: 'ground',
    building: 'ground',
    axis: 'y',
    value: groundY,
    outward: 1,
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

function sourceOnOutwardSide(source, face) {
  if (face.kind === 'ground') return source[1] > face.value + 0.05;
  const si = face.axis === 'x' ? source[0] : source[2];
  return (si - face.value) * face.outward > 0.05;
}

function finishSpecular(order, kind, faceId, hit, hits, image, pathLen, bands) {
  const withAir = applyAirToBands(bands, pathLen);
  return {
    kind,
    order,
    faceId,
    hit,
    hits,
    image,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    bands: withAir,
    // Allen & Berkley: pressure ~ β / R (bands already include β product).
    gain: gainFromBands(withAir) * sphericalPressureGain(pathLen),
    cutoffHz: cutoffFromBands(withAir, pathLen),
  };
}

export function facadeReflection(listener, source, face, buildings) {
  if (!sourceOnOutwardSide(source, face)) return null;
  const image = mirrorPoint(source, face.axis, face.value);
  const toImage = sub(image, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;
  const dir = scale(toImage, 1 / pathLen);
  const ai = face.axis === 'x' ? 0 : 2;
  if (Math.abs(dir[ai]) < 1e-9) return null;
  const tHit = (face.value - listener[ai]) / dir[ai];
  if (tHit <= 1e-4 || tHit >= pathLen - 1e-4) return null;
  const hit = add(listener, scale(dir, tHit));
  if (!onFace(hit, face)) return null;
  if (isOccluded(source, hit, buildings) || isOccluded(hit, listener, buildings)) return null;
  const bands = bounceBands(unitBands(), materialForFace(face));
  return finishSpecular(1, 'facade', face.id, hit, [hit], image, pathLen, bands);
}

export function groundReflection(listener, source, groundY = GROUND.y) {
  if (source[1] <= groundY + 0.05) return null;
  const image = mirrorPoint(source, 'y', groundY);
  const pathLen = length(sub(image, listener));
  if (pathLen < 1e-3) return null;
  const tHit = (groundY - listener[1]) / (image[1] - listener[1]);
  if (tHit <= 0 || tHit >= 1) return null;
  const hit = add(listener, scale(sub(image, listener), tHit));
  const face = groundFace(groundY);
  const bands = bounceBands(unitBands(), materialForFace(face));
  return finishSpecular(1, 'ground', 'ground', hit, [hit], image, pathLen, bands);
}

export function order2Reflection(listener, source, faceA, faceB, buildings) {
  if (faceA.id === faceB.id) return null;
  if (faceA.axis === faceB.axis && Math.abs(faceA.value - faceB.value) < 1e-6) return null;
  if (!sourceOnOutwardSide(source, faceA)) return null;

  const image1 = mirrorPoint(source, faceA.axis, faceA.value);
  if (!sourceOnOutwardSide(image1, faceB)) return null;
  const image2 = mirrorPoint(image1, faceB.axis, faceB.value);

  const toImage = sub(image2, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;
  const dir = scale(toImage, 1 / pathLen);

  const bi = axisIndex(faceB.axis);
  if (Math.abs(dir[bi]) < 1e-9) return null;
  const tB = (faceB.value - listener[bi]) / dir[bi];
  if (tB <= 1e-4 || tB >= pathLen - 1e-4) return null;
  const hitB = add(listener, scale(dir, tB));
  if (!onReflector(hitB, faceB)) return null;

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

  if (
    isOccluded(source, hitA, buildings) ||
    isOccluded(hitA, hitB, buildings) ||
    isOccluded(hitB, listener, buildings)
  ) {
    return null;
  }

  let bands = bounceBands(unitBands(), materialForFace(faceA));
  bands = bounceBands(bands, materialForFace(faceB));
  const kind = faceA.kind === 'ground' || faceB.kind === 'ground' ? 'order2-ground' : 'order2';
  return finishSpecular(2, kind, `${faceA.id}>${faceB.id}`, hitB, [hitA, hitB], image2, pathLen, bands);
}

/** Order-3: source → A → B → C → listener. */
export function order3Reflection(listener, source, faceA, faceB, faceC, buildings) {
  if (faceA.id === faceB.id || faceB.id === faceC.id || faceA.id === faceC.id) return null;
  if (!sourceOnOutwardSide(source, faceA)) return null;
  const image1 = mirrorPoint(source, faceA.axis, faceA.value);
  if (!sourceOnOutwardSide(image1, faceB)) return null;
  const image2 = mirrorPoint(image1, faceB.axis, faceB.value);
  if (!sourceOnOutwardSide(image2, faceC)) return null;
  const image3 = mirrorPoint(image2, faceC.axis, faceC.value);

  const toImage = sub(image3, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;
  const dir = scale(toImage, 1 / pathLen);

  const ci = axisIndex(faceC.axis);
  if (Math.abs(dir[ci]) < 1e-9) return null;
  const tC = (faceC.value - listener[ci]) / dir[ci];
  if (tC <= 1e-4 || tC >= pathLen - 1e-4) return null;
  const hitC = add(listener, scale(dir, tC));
  if (!onReflector(hitC, faceC)) return null;

  const toI2 = sub(image2, hitC);
  const len2 = length(toI2);
  if (len2 < 1e-3) return null;
  const dir2 = scale(toI2, 1 / len2);
  const bi = axisIndex(faceB.axis);
  if (Math.abs(dir2[bi]) < 1e-9) return null;
  const tB = (faceB.value - hitC[bi]) / dir2[bi];
  if (tB <= 1e-4 || tB >= len2 - 1e-4) return null;
  const hitB = add(hitC, scale(dir2, tB));
  if (!onReflector(hitB, faceB)) return null;

  const toI1 = sub(image1, hitB);
  const len1 = length(toI1);
  if (len1 < 1e-3) return null;
  const dir1 = scale(toI1, 1 / len1);
  const ai = axisIndex(faceA.axis);
  if (Math.abs(dir1[ai]) < 1e-9) return null;
  const tA = (faceA.value - hitB[ai]) / dir1[ai];
  if (tA <= 1e-4 || tA >= len1 - 1e-4) return null;
  const hitA = add(hitB, scale(dir1, tA));
  if (!onReflector(hitA, faceA)) return null;

  if (
    isOccluded(source, hitA, buildings) ||
    isOccluded(hitA, hitB, buildings) ||
    isOccluded(hitB, hitC, buildings) ||
    isOccluded(hitC, listener, buildings)
  ) {
    return null;
  }

  let bands = bounceBands(unitBands(), materialForFace(faceA));
  bands = bounceBands(bands, materialForFace(faceB));
  bands = bounceBands(bands, materialForFace(faceC));
  return finishSpecular(
    3,
    'order3',
    `${faceA.id}>${faceB.id}>${faceC.id}`,
    hitC,
    [hitA, hitB, hitC],
    image3,
    pathLen,
    bands,
  );
}

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

/** Order-3 triples: opposite facades with ground in the middle (street canyon). */
export function order3TripleList(faceList, { limit = 48 } = {}) {
  const triples = [];
  const ground = groundFace();
  for (let i = 0; i < faceList.length; i++) {
    for (let j = i + 1; j < faceList.length; j++) {
      const a = faceList[i];
      const c = faceList[j];
      if (a.building === c.building) continue;
      if (a.axis !== c.axis) continue;
      if (a.outward === c.outward) continue;
      if (Math.abs(a.value - c.value) < 1) continue;
      triples.push([a, ground, c], [c, ground, a], [a, c, ground], [c, a, ground]);
      if (triples.length >= limit) return triples.slice(0, limit);
    }
  }
  return triples.slice(0, limit);
}

/**
 * Strongest early reflections up to `limit`, mixing order-1..maxOrder.
 */
export function computeReflections(
  listener,
  source,
  buildings,
  {
    limit = 16,
    faces = null,
    maxOrder = 3,
    order2CandidateLimit = 80,
    order3CandidateLimit = 48,
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

  if (maxOrder >= 3) {
    const triples = order3TripleList(faceList, { limit: order3CandidateLimit });
    for (const [a, b, c] of triples) {
      const r = order3Reflection(listener, source, a, b, c, buildings);
      if (r) candidates.push(r);
    }
  }

  candidates.sort((a, b) => b.gain - a.gain);
  return candidates.slice(0, limit);
}

export function excessDelaySec(reflection, listener, source) {
  const direct = length(sub(source, listener));
  return reflection.delaySec - direct / SPEED_OF_SOUND;
}
