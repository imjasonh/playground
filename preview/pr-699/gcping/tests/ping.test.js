import test from "node:test";
import assert from "node:assert/strict";

import { pingRegion } from "../src/ping.js";
import { PING_BUCKET } from "../src/regions.js";

test("pingRegion sends a no-cors GET and records elapsed time", async () => {
  const calls = [];
  const result = await pingRegion("us-east4", {
    nonce: "n1",
    timeoutMs: 1000,
    now: (() => {
      let t = 100;
      return () => {
        const value = t;
        t += 25;
        return value;
      };
    })(),
    fetchImpl: (url, init) => {
      calls.push({ url, init });
      return Promise.resolve(null);
    },
    getEntry: () => null,
  });
  assert.equal(calls.length, 1);
  assert.equal(
    calls[0].url,
    `https://storage.us-east4.rep.googleapis.com/${PING_BUCKET}/n1`,
  );
  assert.equal(calls[0].init.mode, "no-cors");
  assert.equal(calls[0].init.cache, "no-store");
  assert.equal(calls[0].init.credentials, "omit");
  assert.equal(result.ok, true);
  assert.equal(result.duration, 25);
  assert.equal(result.breakdown, null);
});

test("pingRegion returns a TLS breakdown when Resource Timing has one", async () => {
  const result = await pingRegion("us-east4", {
    nonce: "n2",
    timeoutMs: 1000,
    now: () => 0,
    fetchImpl: () => Promise.resolve(null),
    getEntry: () => ({
      domainLookupStart: 0,
      domainLookupEnd: 2,
      connectStart: 2,
      secureConnectionStart: 5,
      connectEnd: 20,
      requestStart: 20,
      responseStart: 40,
      responseEnd: 41,
      duration: 41,
    }),
  });
  assert.equal(result.ok, true);
  assert.deepEqual(result.breakdown, {
    dns: 2,
    tcp: 3,
    tls: 15,
    wait: 20,
    download: 1,
  });
});

test("pingRegion marks an aborted fetch", async () => {
  const controller = new AbortController();
  controller.abort();
  const result = await pingRegion("europe-west1", {
    nonce: "n3",
    timeoutMs: 1000,
    now: () => 0,
    fetchImpl: (url, init) => {
      const err = new Error(`aborted ${url} aborted=${init.signal.aborted}`);
      err.name = "AbortError";
      return Promise.reject(err);
    },
    getEntry: () => null,
    signal: controller.signal,
  });
  assert.equal(result.ok, false);
  assert.equal(result.aborted, true);
  assert.equal(result.duration, null);
});
