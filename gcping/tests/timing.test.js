import test from "node:test";
import assert from "node:assert/strict";

import { breakdownFromEntry } from "../src/timing.js";

test("breakdownFromEntry is null without an entry", () => {
  assert.equal(breakdownFromEntry(null), null);
});

test("breakdownFromEntry is null when Timing-Allow-Origin hid the timestamps", () => {
  assert.equal(
    breakdownFromEntry({
      connectStart: 0,
      connectEnd: 0,
      secureConnectionStart: 0,
      domainLookupStart: 0,
      domainLookupEnd: 0,
      requestStart: 0,
      responseStart: 0,
      responseEnd: 120,
      duration: 120,
    }),
    null,
  );
});

test("breakdownFromEntry splits DNS, TCP, TLS, wait, and download", () => {
  assert.deepEqual(
    breakdownFromEntry({
      domainLookupStart: 1,
      domainLookupEnd: 4,
      connectStart: 4,
      secureConnectionStart: 10,
      connectEnd: 40,
      requestStart: 40,
      responseStart: 90,
      responseEnd: 95,
      duration: 94,
    }),
    { dns: 3, tcp: 6, tls: 30, wait: 50, download: 5 },
  );
});
