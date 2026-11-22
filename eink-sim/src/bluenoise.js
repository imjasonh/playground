// 64x64 tileable blue-noise threshold matrix generated with Ulichney's
// Void-and-Cluster algorithm (sigma = 1.9, toroidal wrap). Every value in
// 0..255 appears exactly 16 times, giving an isotropic, artifact-free ordered
// dither without Bayer crosshatching or error-diffusion worms.

export const BLUE_NOISE_SIZE = 64;

const BLUE_NOISE_B64 =
  "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";

let cached = null;

// Returns a Uint8Array(4096) with values in 0..255 (row-major, 64x64).
export function getBlueNoiseMatrix() {
  if (cached) return cached;
  const bin = atob(BLUE_NOISE_B64);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) {
    out[i] = bin.charCodeAt(i);
  }
  cached = out;
  return out;
}
