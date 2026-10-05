import test from "node:test";
import assert from "node:assert/strict";

import { nNumberToIcao } from "../src/nnumber.js";

// Publicly reported ICAO hex codes for real US aircraft, including the four
// NYPD Bell 429s and the Subaru Bell 412EPX.
const KNOWN = {
  N1: "A00001",
  N1A: "A00002",
  N99999: "ADF7C7",
  N12345: "A061D9",
  N917PD: "ACB1F5",
  N918PD: "ACB5AC",
  N919PD: "ACB963",
  N920PD: "ACBF73",
  N922PD: "ACC6E1",
};

test("encodes known N-numbers to their ICAO hex", () => {
  for (const [tail, hex] of Object.entries(KNOWN)) {
    assert.equal(nNumberToIcao(tail), hex, `${tail} should encode to ${hex}`);
  }
});

test("is case- and whitespace-insensitive", () => {
  assert.equal(nNumberToIcao("  n917pd "), "ACB1F5");
});

test("always returns six uppercase hex characters in the US range", () => {
  for (const tail of ["N1", "N407NY", "N412PD", "N99999"]) {
    const hex = nNumberToIcao(tail);
    assert.match(hex, /^[0-9A-F]{6}$/);
    const value = parseInt(hex, 16);
    assert.ok(value >= 0xa00001 && value <= 0xadf7c7, `${tail} -> ${hex}`);
  }
});

test("rejects invalid input", () => {
  for (const bad of ["", "917PD", "N0", "N", "XYZ", null, undefined, 42]) {
    assert.equal(nNumberToIcao(bad), null, `${String(bad)} should be null`);
  }
});
