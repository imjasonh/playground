// Surface materials: energy absorption α → pressure reflection β = √(1−α)
// (Allen & Berkley 1979). Scattering s sends (1−s) to specular ISM and s toward
// the stochastic late field (Kang 2000 street-canyon diffuse boundaries).
// Band centers ≈ 250 Hz / 1 kHz / 4 kHz (urban facade averages).

export const MATERIALS = {
  concrete: {
    id: 'concrete',
    // Typical painted/rough concrete octave averages (abridged).
    absorb: { low: 0.02, mid: 0.06, high: 0.14 },
    scatter: 0.12,
  },
  glass: {
    id: 'glass',
    absorb: { low: 0.03, mid: 0.05, high: 0.08 },
    scatter: 0.05,
  },
  asphalt: {
    id: 'asphalt',
    absorb: { low: 0.05, mid: 0.12, high: 0.35 },
    scatter: 0.15,
  },
};

/** Pressure reflection coefficient β = √(1 − α). */
export function pressureReflection(alpha) {
  const a = Math.max(0, Math.min(0.999, alpha));
  return Math.sqrt(1 - a);
}

/** Mean β across bands (for GPU packing / single reflectivity). */
export function meanPressureReflection(material) {
  const b =
    pressureReflection(material.absorb.low) +
    pressureReflection(material.absorb.mid) +
    pressureReflection(material.absorb.high);
  return (b / 3) * Math.sqrt(Math.max(0, 1 - (material.scatter || 0)));
}

/** Facade material: alternate concrete / glass by building id. */
export function materialForFace(face) {
  if (face.kind === 'ground' || face.id === 'ground') return MATERIALS.asphalt;
  const glass = /ne-low|se/.test(face.building || '');
  return glass ? MATERIALS.glass : MATERIALS.concrete;
}

/**
 * Apply one specular bounce: β_band · √(1 − s).
 * @param {{low:number,mid:number,high:number}} bands
 * @param {{absorb:{low:number,mid:number,high:number}, scatter?:number}} material
 */
export function bounceBands(bands, material) {
  const keepSpec = Math.sqrt(Math.max(0, 1 - (material.scatter || 0)));
  return {
    low: bands.low * pressureReflection(material.absorb.low) * keepSpec,
    mid: bands.mid * pressureReflection(material.absorb.mid) * keepSpec,
    high: bands.high * pressureReflection(material.absorb.high) * keepSpec,
  };
}

export function unitBands() {
  return { low: 1, mid: 1, high: 1 };
}

/**
 * Map surviving high-band energy + path length (air already in bands) to LP.
 * Residual path darkening is mild; ISO air absorption owns the physics.
 */
export function cutoffFromBands(bands, pathLength) {
  const high = Math.max(0, Math.min(1, bands.high));
  const mid = Math.max(0, Math.min(1, bands.mid));
  const base = 900 + mid * 6000 + high * 8000;
  return Math.max(400, base - pathLength * 4);
}

/** Ear-weighted broadband amplitude from bands (spreading applied separately). */
export function gainFromBands(bands) {
  return 0.55 * bands.mid + 0.25 * bands.low + 0.2 * bands.high;
}

/** Spherical pressure spreading (Allen & Berkley): 1/R. */
export function sphericalPressureGain(pathLength) {
  return 1 / Math.max(pathLength, 1);
}
