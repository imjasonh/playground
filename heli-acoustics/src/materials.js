// Frequency-dependent surface materials for early paths and stochastic late field.
// Band absorptions are rough urban averages (low ~250 Hz, mid ~1 kHz, high ~4 kHz).

export const MATERIALS = {
  concrete: {
    id: 'concrete',
    reflectivity: 0.62,
    absorb: { low: 0.02, mid: 0.06, high: 0.14 },
  },
  glass: {
    id: 'glass',
    reflectivity: 0.7,
    absorb: { low: 0.03, mid: 0.05, high: 0.08 },
  },
  asphalt: {
    id: 'asphalt',
    reflectivity: 0.38,
    absorb: { low: 0.05, mid: 0.12, high: 0.35 },
  },
};

/** Facade material: alternate concrete / glass by building id hash. */
export function materialForFace(face) {
  if (face.kind === 'ground' || face.id === 'ground') return MATERIALS.asphalt;
  const glass = /ne-low|se/.test(face.building || '');
  return glass ? MATERIALS.glass : MATERIALS.concrete;
}

/**
 * Apply one bounce of material absorption to a 3-band energy vector.
 * @param {{low:number,mid:number,high:number}} bands
 * @param {{absorb:{low:number,mid:number,high:number}, reflectivity:number}} material
 */
export function bounceBands(bands, material) {
  return {
    low: bands.low * material.reflectivity * (1 - material.absorb.low),
    mid: bands.mid * material.reflectivity * (1 - material.absorb.mid),
    high: bands.high * material.reflectivity * (1 - material.absorb.high),
  };
}

export function unitBands() {
  return { low: 1, mid: 1, high: 1 };
}

/** Map surviving high-band energy to a low-pass cutoff for a wet tap. */
export function cutoffFromBands(bands, pathLength) {
  const high = Math.max(0, Math.min(1, bands.high));
  const mid = Math.max(0, Math.min(1, bands.mid));
  const base = 700 + mid * 5500 + high * 7000;
  return Math.max(500, base - pathLength * 12);
}

/** Broadband gain from mid band (ear-weighted) with path falloff already in bands. */
export function gainFromBands(bands) {
  return 0.55 * bands.mid + 0.25 * bands.low + 0.2 * bands.high;
}
