// ISO 9613-1 / Bass et al. atmospheric absorption (pure-tone α in dB/m).
// Default meteorology: 20 °C, 50 % RH, 101.325 kPa.
// Band centers used by the 3-band materials path.

export const AIR_DEFAULT = Object.freeze({
  tempC: 20,
  rhPercent: 50,
  pressurePa: 101325,
});

export const BAND_HZ = Object.freeze({ low: 250, mid: 1000, high: 4000 });

/**
 * Pure-tone atmospheric attenuation coefficient in dB/m (ISO 9613-1 §6 /
 * Bass–Sutherland form used by outdoor noise tools).
 * @param {number} freqHz
 * @param {{ tempC?: number, rhPercent?: number, pressurePa?: number }} [meteo]
 */
export function airAbsorptionDbPerMeter(freqHz, meteo = AIR_DEFAULT) {
  const f = Math.max(50, Math.min(10000, freqHz));
  const T = (meteo.tempC ?? AIR_DEFAULT.tempC) + 273.15;
  const T0 = 293.15;
  const T01 = 273.16;
  const p = meteo.pressurePa ?? AIR_DEFAULT.pressurePa;
  const p0 = 101325;
  const hr = Math.max(0.1, Math.min(100, meteo.rhPercent ?? AIR_DEFAULT.rhPercent));

  // Saturation vapor pressure (Pa) and molar concentration of water vapor (%).
  const psat = p0 * 10 ** (-6.8346 * (T01 / T) ** 1.261 + 4.6151);
  const h = hr * (psat / p);

  const pr = p / p0;
  const tr = T / T0;
  const frO = pr * (24 + 4.04e4 * h * (0.02 + h) / (0.391 + h));
  const frN =
    pr * tr ** -0.5 * (9 + 280 * h * Math.exp(-4.17 * (tr ** (-1 / 3) - 1)));

  const f2 = f * f;
  // Classical + rotational absorption (Neper/m).
  const alphaClass = 1.84e-11 * (1 / pr) * Math.sqrt(tr) * f2;
  // Vibrational O₂ / N₂ (Neper/m).
  const alphaVib =
    tr ** -2.5 *
    (0.01275 * Math.exp(-2239.1 / T) * (frO / (frO * frO + f2)) +
      0.1068 * Math.exp(-3352.0 / T) * (frN / (frN * frN + f2))) *
    f2;

  // Neper/m → dB/m.
  return 8.686 * (alphaClass + alphaVib);
}

/** Linear amplitude factor for a path of length `pathLen` m at `freqHz`. */
export function airGain(pathLen, freqHz, meteo = AIR_DEFAULT) {
  const aDb = airAbsorptionDbPerMeter(freqHz, meteo) * Math.max(0, pathLen);
  return 10 ** (-aDb / 20);
}

/** Per-band linear air gains for low/mid/high centers. */
export function airBandGains(pathLen, meteo = AIR_DEFAULT) {
  return {
    low: airGain(pathLen, BAND_HZ.low, meteo),
    mid: airGain(pathLen, BAND_HZ.mid, meteo),
    high: airGain(pathLen, BAND_HZ.high, meteo),
  };
}

/** Apply air absorption to a 3-band amplitude vector. */
export function applyAirToBands(bands, pathLen, meteo = AIR_DEFAULT) {
  const g = airBandGains(pathLen, meteo);
  return {
    low: bands.low * g.low,
    mid: bands.mid * g.mid,
    high: bands.high * g.high,
  };
}
