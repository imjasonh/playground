// The NYPD Aviation Unit rotary-wing fleet, keyed by FAA tail number.
//
// Hex codes are the ICAO 24-bit Mode-S addresses broadcast over ADS-B; they
// are derived deterministically from the tail number (see nnumber.js) and the
// derivation is checked against publicly reported values in the tests.
//
// Fuel burn figures are rough per-type cruise estimates for turbine (Jet-A)
// helicopters, in US gallons per flight hour. They are deliberately
// conservative order-of-magnitude numbers for cost estimation, NOT
// manufacturer performance data.

import { nNumberToIcao } from "./nnumber.js";

// Per-model metadata: colour for the map, and estimated Jet-A burn (gal/hour).
const MODELS = {
  "Bell 429": { category: "light twin", fuelGph: 50, color: "#2563eb" },
  "Bell 412EP": { category: "medium twin", fuelGph: 100, color: "#dc2626" },
  "Bell 412EPX": { category: "medium twin", fuelGph: 100, color: "#ea580c" },
  "Bell 407": { category: "light single", fuelGph: 40, color: "#16a34a" },
};

const ROSTER = [
  { tail: "N917PD", model: "Bell 429" },
  { tail: "N918PD", model: "Bell 429" },
  { tail: "N919PD", model: "Bell 429" },
  { tail: "N920PD", model: "Bell 429" },
  { tail: "N921PD", model: "Bell 429" },
  { tail: "N922PD", model: "Bell 412EPX" },
  { tail: "N412PD", model: "Bell 412EP" },
  { tail: "N414PD", model: "Bell 412EP" },
  { tail: "N422PD", model: "Bell 412EP" },
  { tail: "N407NY", model: "Bell 407" },
];

// A palette to keep same-model aircraft visually distinguishable on the map.
const PALETTE = [
  "#2563eb",
  "#dc2626",
  "#16a34a",
  "#9333ea",
  "#ea580c",
  "#0891b2",
  "#ca8a04",
  "#db2777",
  "#4f46e5",
];

export const FLEET = ROSTER.map((entry, i) => {
  const meta = MODELS[entry.model];
  if (!meta) throw new Error(`Unknown model for ${entry.tail}: ${entry.model}`);
  const hex = nNumberToIcao(entry.tail);
  if (!hex) throw new Error(`Could not derive ICAO hex for ${entry.tail}`);
  return {
    tail: entry.tail,
    hex,
    model: entry.model,
    category: meta.category,
    fuelGph: meta.fuelGph,
    color: PALETTE[i % PALETTE.length],
  };
});

// Uppercase ICAO hex -> fleet member, for fast lookup of scraped samples.
export const FLEET_BY_HEX = new Map(FLEET.map((a) => [a.hex.toUpperCase(), a]));

// Comma-separated hex list for a single adsb.lol /v2/hex/ query.
export const FLEET_HEXES = FLEET.map((a) => a.hex).join(",");

export function fleetMemberForHex(hex) {
  return FLEET_BY_HEX.get(String(hex || "").toUpperCase()) || null;
}
