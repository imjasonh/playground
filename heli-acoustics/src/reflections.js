import { add, sub, scale, length } from './geometry.js';
import { isOccluded } from './occlusion.js';
import { SPEED_OF_SOUND, GROUND, buildingFaces } from './city.js';

const REFLECTIVITY = {
  facade: 0.55,
  ground: 0.35,
};

// Reflect a point across an axis-aligned plane (constant x or z or y).
function mirrorPoint(p, axis, value) {
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

// Order-1 image-source reflection against one finite facade. Returns null when
// the hit misses the face, the path is degenerate, or another building blocks
// source→hit or hit→listener.
export function facadeReflection(listener, source, face, buildings) {
  // Source must be on the outward side of the face.
  const si = face.axis === 'x' ? source[0] : source[2];
  if ((si - face.value) * face.outward < 0.05) return null;

  const image = mirrorPoint(source, face.axis, face.value);
  const toImage = sub(image, listener);
  const pathLen = length(toImage);
  if (pathLen < 1e-3) return null;

  const dir = scale(toImage, 1 / pathLen);
  const axisIndex = face.axis === 'x' ? 0 : 2;
  if (Math.abs(dir[axisIndex]) < 1e-9) return null;
  const tHit = (face.value - listener[axisIndex]) / dir[axisIndex];
  if (tHit <= 1e-4 || tHit >= pathLen - 1e-4) return null;

  const hit = add(listener, scale(dir, tHit));
  if (!onFace(hit, face)) return null;

  // Both legs of the bounce must stay clear of other buildings.
  if (isOccluded(source, hit, buildings) || isOccluded(hit, listener, buildings)) return null;

  return {
    kind: 'facade',
    faceId: face.id,
    hit,
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
  // Parametric along listener→image in [0,1]
  if (tHit <= 0 || tHit >= 1) return null;
  const hit = add(listener, scale(sub(image, listener), tHit));
  return {
    kind: 'ground',
    faceId: 'ground',
    hit,
    image,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: REFLECTIVITY.ground / Math.max(pathLen, 1),
  };
}

// Compute up to `limit` strongest order-1 reflections (facades + ground).
export function computeReflections(listener, source, buildings, { limit = 8, faces = null } = {}) {
  const faceList = faces || buildingFaces(buildings);
  const candidates = [];
  for (const face of faceList) {
    const r = facadeReflection(listener, source, face, buildings);
    if (r) candidates.push(r);
  }
  const g = groundReflection(listener, source);
  if (g) candidates.push(g);
  candidates.sort((a, b) => b.gain - a.gain);
  return candidates.slice(0, limit);
}

// Extra path length beyond the direct path, useful for HUD / tests.
export function excessDelaySec(reflection, listener, source) {
  const direct = length(sub(source, listener));
  return reflection.delaySec - direct / SPEED_OF_SOUND;
}
