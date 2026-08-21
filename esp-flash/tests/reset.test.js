import test from "node:test";
import assert from "node:assert/strict";
import { resetIntoApp, sleep } from "../src/reset.js";

function mockTransport() {
  const calls = [];
  return {
    calls,
    async setDTR(state) {
      calls.push(["DTR", state]);
    },
    async setRTS(state) {
      calls.push(["RTS", state]);
    },
  };
}

test("resetIntoApp pulses EN with IO0 held high", async () => {
  const transport = mockTransport();
  const waits = [];
  await resetIntoApp(transport, {
    sleep: async (ms) => {
      waits.push(ms);
    },
  });
  assert.deepEqual(transport.calls, [
    ["DTR", false],
    ["RTS", true],
    ["RTS", false],
    ["DTR", false],
  ]);
  assert.deepEqual(waits, [100, 50]);
});

test("resetIntoApp rejects a transport without modem-control lines", async () => {
  await assert.rejects(() => resetIntoApp({}), /DTR\/RTS/);
  await assert.rejects(() => resetIntoApp(null), /DTR\/RTS/);
});

test("sleep uses the injected timer when provided", async () => {
  let seen = 0;
  await sleep(5, {
    sleep: async (ms) => {
      seen = ms;
    },
  });
  assert.equal(seen, 5);
});
