// Geometric edge diffraction with Maekawa insertion loss + 1/(d1·d2) edge-source
// falloff (BTM / Svensson secondary-source intuition; not a full BTM integral).

import { sub, length, dot, normalize } from './geometry.js';
import { isOccluded } from './occlusion.js';
import { buildingEdges, diffractionPoint } from './edges.js';
import { SPEED_OF_SOUND } from './city.js';
import { applyAirToBands } from './airAbsorption.js';
import { maekawaBandAmplitudes } from './maekawa.js';
import { cutoffFromBands, gainFromBands, sphericalPressureGain } from './materials.js';

export { buildingEdges, diffractionPoint } from './edges.js';

/**
 * Diffraction path for one edge. Maekawa IL from path difference δ; amplitude
 * also falls as 1/(d1·d2) like a BTM edge source density term (without the
 * full line integral).
 */
export function edgeDiffraction(listener, source, edge, buildings) {
  const p = diffractionPoint(source, listener, edge.a, edge.b);
  const d1 = length(sub(p, source));
  const d2 = length(sub(listener, p));
  const pathLen = d1 + d2;
  if (pathLen < 1e-3) return null;

  const direct = length(sub(source, listener));
  const pathDiff = pathLen - direct;
  if (pathDiff < 0.05) return null;

  if (isOccluded(source, p, buildings) || isOccluded(p, listener, buildings)) return null;

  const u = normalize(sub(p, source));
  const v = normalize(sub(listener, p));
  const bend = Math.acos(Math.max(-1, Math.min(1, dot(u, v))));
  if (bend < 0.15) return null;

  const mk = maekawaBandAmplitudes(pathDiff);
  const edgeGeom = 1 / Math.max(d1 * d2, 1);
  const free = sphericalPressureGain(direct);
  const geomScale = Math.min(1.5, (edgeGeom / Math.max(free, 1e-6)) * 0.35);

  let bands = {
    low: mk.low * geomScale,
    mid: mk.mid * geomScale,
    high: mk.high * geomScale,
  };
  bands = applyAirToBands(bands, pathLen);

  return {
    kind: 'diffraction',
    order: 0,
    faceId: edge.id,
    hit: p,
    hits: [p],
    image: p,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: gainFromBands(bands) * sphericalPressureGain(pathLen),
    bands,
    cutoffHz: cutoffFromBands(bands, pathLen),
  };
}

export function computeDiffraction(listener, source, buildings, { limit = 6, edges = null } = {}) {
  const list = edges || buildingEdges(buildings);
  const out = [];
  for (const edge of list) {
    const d = edgeDiffraction(listener, source, edge, buildings);
    if (d) out.push(d);
  }
  out.sort((a, b) => b.gain - a.gain);
  return out.slice(0, limit);
}
