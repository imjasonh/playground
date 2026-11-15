import test from "node:test";
import assert from "node:assert/strict";
import { resetIntoApp } from "../src/reset.js";

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
  await resetIntoApp(transport);
  assert.deepEqual(transport.calls, [
    ["DTR", false],
    ["RTS", true],
    ["RTS", false],
    ["DTR", false],
  ]);
});

test("resetIntoApp rejects a transport without modem-control lines", async () => {
  await assert.rejects(() => resetIntoApp({}), /DTR\/RTS/);
  await assert.rejects(() => resetIntoApp(null), /DTR\/RTS/);
});
