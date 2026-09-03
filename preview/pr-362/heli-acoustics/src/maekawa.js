// Fresnel / Maekawa barrier diffraction (Maekawa 1968; ISO 9613-2 screening).
// Used for soft occlusion of the dry path and for edge-diffraction tap gains.

import { SPEED_OF_SOUND } from './city.js';
import { BAND_HZ } from './airAbsorption.js';

/**
 * Fresnel number N = 2 δ / λ for path difference δ (m) at frequency f (Hz).
 * Positive N is in the shadow zone.
 */
export function fresnelNumber(pathDiff, freqHz, speedOfSound = SPEED_OF_SOUND) {
  const lambda = speedOfSound / Math.max(1, freqHz);
  return (2 * pathDiff) / lambda;
}

/**
 * Maekawa insertion loss in dB for Fresnel number N (shadow only).
 * IL = 10 log10(3 + 20 N), capped at 25 dB. Illuminated (N ≤ 0) → 0.
 */
export function maekawaInsertionLossDb(N) {
  if (N <= 0) return 0;
  return Math.min(25, 10 * Math.log10(3 + 20 * N));
}

/** Linear amplitude factor from Maekawa IL. */
export function maekawaAmplitude(pathDiff, freqHz) {
  const N = fresnelNumber(pathDiff, freqHz);
  const il = maekawaInsertionLossDb(N);
  return 10 ** (-il / 20);
}

/** 3-band Maekawa amplitude factors for a given path difference. */
export function maekawaBandAmplitudes(pathDiff) {
  return {
    low: maekawaAmplitude(pathDiff, BAND_HZ.low),
    mid: maekawaAmplitude(pathDiff, BAND_HZ.mid),
    high: maekawaAmplitude(pathDiff, BAND_HZ.high),
  };
}
