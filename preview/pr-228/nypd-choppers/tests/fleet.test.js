import test from "node:test";
import assert from "node:assert/strict";

import { FLEET, FLEET_BY_HEX, FLEET_HEXES, fleetMemberForHex } from "../src/fleet.js";

test("fleet contains the expected NYPD aircraft with derived hexes", () => {
  const byTail = new Map(FLEET.map((a) => [a.tail, a]));
  assert.equal(byTail.get("N917PD").hex, "ACB1F5");
  assert.equal(byTail.get("N922PD").hex, "ACC6E1");
  assert.ok(FLEET.length >= 9);
});

test("every fleet member has a positive fuel burn and a colour", () => {
  for (const a of FLEET) {
    assert.ok(a.fuelGph > 0, `${a.tail} needs a fuel burn`);
    assert.match(a.color, /^#[0-9a-f]{6}$/i);
    assert.match(a.hex, /^[0-9A-F]{6}$/);
  }
});

test("hex lookup helpers work and are case-insensitive", () => {
  assert.equal(fleetMemberForHex("acb1f5").tail, "N917PD");
  assert.equal(fleetMemberForHex("UNKNOWN"), null);
  assert.equal(FLEET_BY_HEX.size, FLEET.length);
});

test("FLEET_HEXES is a comma-joined list matching the fleet", () => {
  assert.equal(FLEET_HEXES.split(",").length, FLEET.length);
  assert.ok(FLEET_HEXES.includes("ACB1F5"));
});
